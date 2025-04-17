/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/normalize.h"

#include <cmath>

#include "bitblast/aig_bitblaster.h"
#include "env.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "solver/bv/bv_solver.h"
#include "util/integer.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

std::ostream&
operator<<(std::ostream& os, const PassNormalize::OccMap& occs)
{
  for (const auto& [n, c] : occs)
  {
    os << c << ": " << n << std::endl;
  }
  return os;
}

using namespace bzla::node;

/**
 * Helper class to compute AIG score for a given set of terms.
 *
 * The AIG score is the number of AND gates. We do not fully bit-blast all
 * operators, but only the ones that are necessary.
 */
class AigScore
{
 public:
  using AigNodeRefSet =
      std::unordered_set<std::reference_wrapper<const bitblast::AigNode>,
                         std::hash<bitblast::AigNode>>;

  /** Add term to score. */
  void add(const Node& term) { d_visit.push_back(term); }

  /**
   * Incrementally process added terms, stop after constructing `limit` AND
   * gates.
   */
  void process(uint64_t limit = 100000);

  uint64_t score() const { return d_bitblaster.num_aig_ands(); }

  /** @return Whether we processed all added terms. */
  bool done() const { return d_visit.empty(); }

 private:
  /** Return encoded bits associated with bit-blasted term. */
  const auto& bits(const Node& term) const
  {
    if (d_bitblaster_cache.find(term) == d_bitblaster_cache.end())
    {
      return d_empty;
    }
    return d_bitblaster_cache.at(term);
  }

  bitblast::AigBitblaster::Bits d_empty;

  /** AIG bit-blaster. */
  bitblast::AigBitblaster d_bitblaster;
  /** Cached to store bit-blasted terms and their encoded bits. */
  std::unordered_map<Node, bitblast::AigBitblaster::Bits> d_bitblaster_cache;
  /** Node to process. */
  node::node_ref_vector d_visit;
};

void
AigScore::process(uint64_t limit)
{
  uint64_t cur_ands = d_bitblaster.num_aig_ands();
  while (!d_visit.empty())
  {
    const Node& cur = d_visit.back();
    assert(cur.type().is_bool() || cur.type().is_bv());

    if (d_bitblaster.num_aig_ands() - cur_ands >= limit)
    {
      break;
    }

    auto it = d_bitblaster_cache.find(cur);
    if (it == d_bitblaster_cache.end())
    {
      d_bitblaster_cache.emplace(cur, bitblast::AigBitblaster::Bits());
      if (!bv::BvSolver::is_leaf(cur))
      {
        d_visit.insert(d_visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.empty())
    {
      const Type& type = cur.type();
      assert(type.is_bool() || type.is_bv());

      switch (cur.kind())
      {
        case Kind::VALUE:
          it->second = type.is_bool()
                           ? d_bitblaster.bv_value(BitVector::from_ui(
                                 1, cur.value<bool>() ? 1 : 0))
                           : d_bitblaster.bv_value(cur.value<BitVector>());
          break;

        case Kind::NOT:
        case Kind::BV_NOT:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_not(bits(cur[0]));
          break;

        case Kind::AND:
        case Kind::BV_AND:
          assert(cur.kind() != Kind::NOT || type.is_bool());
          assert(cur.kind() != Kind::BV_NOT || type.is_bv());
          it->second = d_bitblaster.bv_and(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::OR:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_or(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_XOR:
          it->second = d_bitblaster.bv_xor(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_EXTRACT:
          assert(type.is_bv());
          it->second =
              d_bitblaster.bv_extract(bits(cur[0]), cur.index(0), cur.index(1));
          break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].type();
          if (type0.is_bool() || type0.is_bv())
          {
            it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          }
          else
          {
            // For all other cases we abstract equality as a Boolean constant.
            it->second = d_bitblaster.bv_constant(1);
          }
        }
        break;

        case Kind::BV_COMP:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_eq(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ADD:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_add(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_MUL:
          assert(type.is_bv());
          // Use more succinct encoding for squares
          if (cur[0] == cur[1])
          {
            it->second = d_bitblaster.bv_mul_square(bits(cur[0]));
          }
          else
          {
            it->second = d_bitblaster.bv_mul(bits(cur[0]), bits(cur[1]));
          }
          break;

        case Kind::BV_ULT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_ult(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHL:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shl(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SLT:
          assert(type.is_bool());
          it->second = d_bitblaster.bv_slt(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_SHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_shr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_ASHR:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_ashr(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::BV_CONCAT:
          assert(type.is_bv());
          it->second = d_bitblaster.bv_concat(bits(cur[0]), bits(cur[1]));
          break;

        case Kind::ITE:
          assert(cur[0].type().is_bool());
          it->second =
              d_bitblaster.bv_ite(bits(cur[0])[0], bits(cur[1]), bits(cur[2]));
          break;

        // All other kinds are not included in the score. This includes UDIV and
        // UREM since bit-blasting them is expensive and the preprocessing pass
        // does not normalize these operators.
        default:
          it->second = type.is_bool()
                           ? d_bitblaster.bv_constant(1)
                           : d_bitblaster.bv_constant(type.bv_size());
          break;
      }
    }
    d_visit.pop_back();
  }
}

/* -------------------------------------------------------------------------- */

/* === PassNormalize public ================================================= */

PassNormalize::PassNormalize(Env& env,
                             backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "no", "normalize"),
      d_rewriter(env, Rewriter::LEVEL_ARITHMETIC, "normalize"),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

/* -------------------------------------------------------------------------- */

void
PassNormalize::compute_occurrences_mul(const Node& node, OccMap& occs) const
{
  util::Timer timer(d_stats.time_compute_occurrences);

  node_ref_vector nodes;
  unordered_node_ref_map<util::Integer> occmap;  // all occurrences

  // Collect nodes and initialize occurrences for each node to zero.
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = occmap.try_emplace(cur, 0);
    visit.pop_back();
    if (inserted)
    {
      nodes.push_back(cur);
      if (cur.kind() == Kind::BV_MUL)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());

  // Compute leaf occurrences by pushing initial top node occurrence to leafs.
  //
  // Note: We have to ensure that parents are fully processed before we compute
  //       the occurrences for its children. Hence, we sort the nodes in
  //       ascending order and process the nodes with the higher IDs first.
  std::sort(nodes.begin(), nodes.end());
  assert(nodes.back() == node);
  ++occmap[node];  // Set initial occurrence of top node
  for (auto it = nodes.rbegin(), rend = nodes.rend(); it != rend; ++it)
  {
    const Node& cur = *it;
    assert(occmap.find(cur) != occmap.end());
    const auto& cur_occ = occmap[cur];

    // If it's an intermediate node, push occurrence down to children
    if (cur.kind() == Kind::BV_MUL)
    {
      for (const auto& child : cur)
      {
        assert(occmap.find(child) != occmap.end());
        occmap[child] += cur_occ;
      }
    }
    // If it's a leaf, just copy the result
    else
    {
      occs[cur] += cur_occ;
    }
  }
}

void
PassNormalize::compute_occurrences_add(const Node& node, OccMap& occs) const
{
  util::Timer timer(d_stats.time_compute_occurrences);

  node_ref_vector nodes;
  unordered_node_ref_map<util::Integer> occmap;  // all occurrences

  // Collect nodes and initialize occurrences for each node to zero.
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = occmap.try_emplace(cur, 0);
    visit.pop_back();
    if (inserted)
    {
      nodes.push_back(cur);
      if (cur.kind() == Kind::BV_ADD)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else if (cur.kind() == Kind::BV_NOT && cur[0].kind() == Kind::BV_ADD)
      {
        visit.insert(visit.end(), cur[0].begin(), cur[0].end());
      }
    }
  } while (!visit.empty());

  // Compute leaf occurrences by pushing initial top node occurrence to leafs.
  //
  // Note: We have to ensure that parents are fully processed before we compute
  //       the occurrences for its children. Hence, we sort the nodes in
  //       ascending order and process the nodes with the higher IDs first.
  std::sort(nodes.begin(), nodes.end());
  assert(nodes.back() == node);

  Node ones = d_env.nm().mk_value(BitVector::mk_ones(node.type().bv_size()));
  ++occmap[node];  // Set initial occurrence of top node
  for (auto it = nodes.rbegin(), rend = nodes.rend(); it != rend; ++it)
  {
    const Node& cur = *it;
    assert(occmap.find(cur) != occmap.end());
    const auto& cur_occ = occmap[cur];

    // If it's an intermediate node, push occurrence down to children
    if (cur.kind() == Kind::BV_NOT && cur[0].kind() == Kind::BV_ADD)
    {
      for (const auto& child : cur[0])
      {
        assert(occmap.find(child) != occmap.end());
        occmap[child] -= cur_occ;
      }
      occs[ones] += cur_occ;
    }
    else if (cur.kind() == Kind::BV_ADD)
    {
      for (const auto& child : cur)
      {
        assert(occmap.find(child) != occmap.end());
        occmap[child] += cur_occ;
      }
    }
    // If it's a leaf, just copy the result
    else
    {
      occs[cur] += cur_occ;
    }
  }
}

PassNormalize::OccMap
PassNormalize::compute_common_subterms(OccMap& lhs, OccMap& rhs)
{
  // We factor out common combinations of common leafs to maximize sharing.
  // For example,
  //         lhs = {a: 1, b: 1}
  //         rhs = {a: 2, b: 2}
  // results in
  //         lhs = {a: 0, b: 0}
  //         rhs = {a: 1, b: 1}
  //         common = (a * b).
  // A more complex example,
  //         lhs = {a: 6, b: 3, c: 2, d: 1}
  //         rhs = {a: 7, b: 5, c: 3}
  // results in
  //         lhs = {a: 0, b: 0, c: 0, d: 1}
  //         rhs = {a: 1, b: 2, c: 1}
  //         common = (aaabc * (aaabc * ab))

  util::Integer zero;
  OccMap common_occs;
  for (auto it0 = lhs.begin(), end = lhs.end(); it0 != end; ++it0)
  {
    auto it1 = rhs.find(it0->first);
    if (it1 != rhs.end())
    {
      const auto occs = std::min(it0->second, it1->second);
      if (occs == zero)
      {
        continue;
      }
      it0->second -= occs;
      it1->second -= occs;
      common_occs.emplace(it0->first, occs);
    }
  }
  return common_occs;
}

Node
PassNormalize::mk_node(Kind kind, const OccMap& occs)
{
  assert(kind == Kind::BV_ADD || kind == Kind::BV_MUL);

  Node res;
  if (occs.empty())
  {
    return res;
  }

  util::Integer zero, one(1);
  NodeManager& nm = d_env.nm();
  // combine common subterms
  if (kind == Kind::BV_ADD)
  {
    std::vector<std::pair<Node, util::Integer>> vec;
    for (const auto& [n, c] : occs)
    {
      if (c != zero)
      {
        vec.emplace_back(n, c);
      }
    }

    if (vec.empty())
    {
      return Node();
    }

    uint64_t size   = vec[0].first.type().bv_size();
    BitVector value = BitVector::mk_zero(size);

    // Extract common factors
    OccMap common;
    if (vec.size() > 1)
    {
      for (const auto& [n, c] : vec)
      {
        if (n.kind() != Kind::BV_MUL)
        {
          common.clear();
          break;
        }
        OccMap o;
        compute_occurrences_mul(n, o);
        if (common.empty())
        {
          common = std::move(o);
        }
        else
        {
          auto com = compute_common_subterms(common, o);
          common   = std::move(com);
        }
        if (common.empty())
        {
          break;
        }
      }
    }

    // Remove common factors
    if (!common.empty())
    {
      for (auto& [n, c] : vec)
      {
        OccMap occs;
        compute_occurrences_mul(n, occs);
        for (const auto& [cn, cc] : common)
        {
          occs[cn] -= cc;
        }
        n = mk_node(Kind::BV_MUL, occs);
        if (n.is_null())
        {
          n = nm.mk_value(BitVector::mk_one(size));
        }
      }
    }

    std::sort(vec.begin(), vec.end(), [](const auto& a, const auto& b) {
      return a.first.id() < b.first.id();
    });

    for (const auto& [node, occ] : vec)
    {
      if (occ == zero)
      {
        continue;
      }

      BitVector bvc(size, occ.gmp_value(), true);

      if (node.is_value())
      {
        value.ibvadd(node.value<BitVector>().bvmul(bvc));
        continue;
      }

      Node m = bvc.is_one()
                   ? node
                   : nm.mk_node(Kind::BV_MUL, {nm.mk_value(bvc), node});
      res    = res.is_null() ? m : nm.mk_node(Kind::BV_ADD, {res, m});
    }
    Node val = nm.mk_value(value);
    res      = res.is_null() ? val : nm.mk_node(Kind::BV_ADD, {res, val});

    // Multiply sum with common factors
    if (!common.empty())
    {
      ++common[res];
      res = mk_node(Kind::BV_MUL, common);
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL);

    std::vector<std::pair<Node, util::Integer>> vec, shl;
    Node value;
    for (const auto& [n, c] : occs)
    {
      if (c != zero)
      {
        if (n.kind() == Kind::BV_SHL && c == one && n[0].is_value()
            && n[0].value<BitVector>().is_one())
        {
          shl.emplace_back(n, c);
        }
        else if (n.is_value())
        {
          assert(c == one);
          assert(value.is_null());
          value = n;
        }
        else
        {
          vec.emplace_back(n, c);
        }
      }
    }

    if (vec.empty() && shl.empty() && value.is_null())
    {
      return Node();
    }

    // Sort nodes by exponent in descending order
    const auto sort_desc = [](const auto& a, const auto& b) {
      return a.second > b.second
             || (a.second == b.second && a.first.id() < b.first.id());
    };
    std::sort(vec.begin(), vec.end(), sort_desc);

    // Sort shifts by shift width
    std::sort(shl.begin(), shl.end(), [](const auto& a, const auto& b) {
      return a.first[1] < b.first[1];
    });

    if (vec.empty())
    {
      if (value.is_null())
      {
        uint64_t size = occs.begin()->first.type().bv_size();
        res           = nm.mk_value(BitVector::mk_one(size));
      }
      else
      {
        res = value;
      }
    }
    else
    {
      while (vec.size() != 1 || vec.back().second != one)
      {
        assert(std::is_sorted(vec.begin(), vec.end(), sort_desc));

        auto& [node1, exp1] = vec[0];
        const auto& exp2    = vec.size() == 1 ? zero : vec[1].second;

        // square first element
        if (exp1 >= exp2 * 2)
        {
          Node squared = nm.mk_node(kind, {node1, node1});
          bool is_odd  = exp1.is_odd();
          exp1 /= 2;
          assert(exp1 >= 1);
          if (is_odd)
          {
            std::pair<Node, util::Integer> p = std::make_pair(node1, 1);
            auto it = std::lower_bound(vec.begin(), vec.end(), p, sort_desc);
            vec.insert(it, std::move(p));
          }
          vec[0].first = squared;
        }
        // combine first and second element
        else
        {
          assert(vec.size() > 1);
          auto& node2 = vec[1].first;
          assert(exp1 >= exp2);
          node2 = nm.mk_node(kind, {node1, node2});
          exp1 -= exp2;
          if (exp1 == zero)
          {
            vec.erase(vec.begin());
          }

          // vec[1] changed, move to correct position.
          for (size_t i = 1, j = 2, size = vec.size();
               j < size && !sort_desc(vec[i], vec[j]);
               ++i, ++j)
          {
            std::swap(vec[i], vec[j]);
          }
        }

        // vec[0] changed, move to correct position.
        for (size_t i = 0, j = 1, size = vec.size();
             j < size && !sort_desc(vec[i], vec[j]);
             ++i, ++j)
        {
          std::swap(vec[i], vec[j]);
        }

        assert(!vec.empty());
      }

      assert(vec.size() == 1);
      assert(vec[0].second == 1);
      res = vec[0].first;
      if (!value.is_null())
      {
        res = nm.mk_node(Kind::BV_MUL, {value, res});
      }
    }

    // Add shifts on top
    for (const auto& [n, o] : shl)
    {
      assert(o == 1);
      assert(n[0].is_value());
      assert(n[0].value<BitVector>().is_one());
      res = nm.mk_node(Kind::BV_SHL, {res, n[1]});
    }
  }
  return d_rewriter.rewrite(res);
}

/* -------------------------------------------------------------------------- */

namespace {

util::Integer
ubv_to_int(const BitVector& bv)
{
  return (bv.size() <= BitVector::s_native_size)
             ? util::Integer(bv.to_uint64())
             : util::Integer::from_mpz_t(bv.gmp_value());
}

}  // namespace

BitVector
PassNormalize::normalize_add(const Node& node,
                             OccMap& occs,
                             bool keep_value,
                             bool push_neg)
{
  util::Timer timer(d_stats.time_normalize_add);

  uint64_t bv_size = node.type().bv_size();
  BitVector bvzero = BitVector::mk_zero(bv_size);
  BitVector value  = bvzero;
  util::Integer zero;

#ifndef NDEBUG
  std::unordered_set<Node> cache;
#endif

  std::vector<std::pair<Node, util::Integer>> work(occs.begin(), occs.end());
  occs.clear();

  for (size_t i = 0; i < work.size(); ++i)
  {
    if (work[i].second == zero)
    {
      continue;
    }

    auto [cur, cur_occ] = work[i];

    // summarize values
    if (cur.is_value())
    {
      BitVector c(bv_size, cur_occ.gmp_value(), true);
      value.ibvadd(cur.value<BitVector>().bvmul(c));
      continue;
    }
    else if (cur.kind() == Kind::BV_MUL
             && (cur[0].is_value() || cur[1].is_value()))
    {
      size_t idx      = cur[0].is_value() ? 0 : 1;
      const Node& val = cur[idx];
      const Node& t   = cur[1 - idx];
      work.emplace_back(t, ubv_to_int(val.value<BitVector>()) * cur_occ);
      continue;
    }
    else if (cur.kind() == Kind::BV_ADD
             || (push_neg
                 && (cur.kind() == Kind::BV_NOT
                     && cur[0].kind() == Kind::BV_ADD)))
    {
      OccMap occmap;
      compute_occurrences_add(cur, occmap);
      for (auto& [c, o] : occmap)
      {
        o *= cur_occ;
        work.emplace_back(c, o);
      }
      continue;
    }
    else if (cur.is_inverted())
    {
      value.ibvsub(BitVector(bv_size, cur_occ.gmp_value(), true));
      work.emplace_back(cur[0], -cur_occ);
      continue;
    }
    else if (cur.kind() == Kind::BV_MUL)
    {
      if (cur[0].kind() == Kind::BV_ADD)
      {
        work.emplace_back(d_rewriter.mk_node(Kind::BV_MUL, {cur[0][0], cur[1]}),
                          cur_occ);
        work.emplace_back(d_rewriter.mk_node(Kind::BV_MUL, {cur[0][1], cur[1]}),
                          cur_occ);
        continue;
      }
      else if (cur[1].kind() == Kind::BV_ADD)
      {
        work.emplace_back(d_rewriter.mk_node(Kind::BV_MUL, {cur[1][0], cur[0]}),
                          cur_occ);
        work.emplace_back(d_rewriter.mk_node(Kind::BV_MUL, {cur[1][1], cur[0]}),
                          cur_occ);
        continue;
      }
      else
      {
        OccMap prod;
        compute_occurrences_mul(cur, prod);
        BitVector value = normalize_mul(cur, prod, false);
        Node norm       = mk_node(Kind::BV_MUL, prod);
        if (norm != cur)
        {
          work.emplace_back(norm, ubv_to_int(value) * cur_occ);
          continue;
        }
      }
    }
    else if (cur.kind() == Kind::BV_EXTRACT && cur.index(1) == 0)
    {
      if (cur[0].kind() == Kind::BV_ADD)
      {
        work.emplace_back(
            d_rewriter.mk_node(Kind::BV_EXTRACT, {cur[0][0]}, cur.indices()),
            cur_occ);
        work.emplace_back(
            d_rewriter.mk_node(Kind::BV_EXTRACT, {cur[0][1]}, cur.indices()),
            cur_occ);
        continue;
      }
      else if (cur[0].kind() == Kind::BV_MUL
               && (cur[0][0].is_value() || cur[0][1].is_value()))
      {
        uint64_t idx = cur[0][0].is_value() ? 0 : 1;
        BitVector c  = cur[0][idx].value<BitVector>().bvextract(cur.index(0),
                                                               cur.index(1));
        work.emplace_back(
            d_rewriter.mk_node(
                Kind::BV_EXTRACT, {cur[0][1 - idx]}, cur.indices()),
            ubv_to_int(c) * cur_occ);
        continue;
      }
      else if (cur[0].kind() == Kind::BV_NOT)
      {
        value.ibvsub(BitVector(bv_size, cur_occ.gmp_value(), true));
        work.emplace_back(
            d_rewriter.mk_node(Kind::BV_EXTRACT, {cur[0][0]}, cur.indices()),
            -cur_occ);
        continue;
      }
    }
    assert(cur_occ != zero);
    assert(cur.kind() != Kind::BV_ADD);
    assert(cur.kind() != Kind::BV_MUL
           || (!cur[0].is_value() && !cur[1].is_value()));
    occs[cur] += cur_occ;
  }

  if (keep_value && (!value.is_zero() || occs.empty()))
  {
    Node val = d_env.nm().mk_value(value);
    ++occs[val];
    return value;
  }

  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_and(const Node& node, OccMap& occs)
{
  uint64_t bv_size = node.type().bv_size();
  BitVector value  = BitVector::mk_one(bv_size);
  util::Integer zero, one(1);

  for (auto& f : occs)
  {
    const Node& cur = f.first;
    // constant fold values
    if (cur.is_value())
    {
      value.ibvand(BitVector(bv_size, f.second.gmp_value(), true));
      f.second = zero;
    }
    // normalize occurrence to 1
    else if (f.second > one)
    {
      f.second = one;
    }
  }
  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_mul(const Node& node, OccMap& occs, bool keep_value)
{
  util::Timer timer(d_stats.time_normalize_mul);

  BitVector value  = BitVector::mk_one(node.type().bv_size());
  util::Integer zero;

  std::vector<std::pair<Node, util::Integer>> work(occs.begin(), occs.end());
  occs.clear();

  NodeManager& nm = d_env.nm();

  bool folded = false;
  for (size_t i = 0; i < work.size(); ++i)
  {
    auto [cur, d] = work[i];

    // constant fold values
    if (cur.is_value())
    {
      BitVector res = cur.value<BitVector>().bvpow(d.gmp_value());
      value.ibvmul(res);
      folded = true;
      continue;
    }
    // unpack (bvshl a b) to (bvmul a (bvshl 1 b))
    else if (cur.kind() == Kind::BV_SHL
             && (!cur[0].is_value() || !cur[0].value<BitVector>().is_one()))
    {
      Node n     = cur[0];
      Node bvone = nm.mk_value(BitVector::mk_one(node.type().bv_size()));
      cur        = nm.mk_node(Kind::BV_SHL, {bvone, cur[1]});
      work.emplace_back(n, d);
    }
    occs[cur] += d;
  }

  if (keep_value && folded)
  {
    Node val = d_env.nm().mk_value(value);
    ++occs[val];
    return value;
  }

  return value;
}

/* -------------------------------------------------------------------------- */

void
PassNormalize::normalize_occurrences_eq_add(uint64_t bv_size,
                                            OccMap& occs0,
                                            OccMap& occs1)
{
  // Moves negated occurrences to other side.
  //
  // Note: Occurrences must already be normalized via normalize_add().
  // (a - b + c = -d + e) is normalized to (a + c + d = b + e)

  util::Integer zero;
  for (auto& [cur, occ] : occs0)
  {
    assert(!cur.is_value() || occ == zero);
    assert(!cur.is_inverted());
    BitVector bv(bv_size, occ.gmp_value(), true);
    // Do not move min_signed coefficients unless term already exists on
    // other side. This avoids terms being moved back and forth due to
    // -min_signed == min_signed.
    if (bv.msb() && !bv.is_min_signed())
    {
      occs1[cur] -= occ;
      occ = zero;
    }
  }
}

void
PassNormalize::normalize_occurrences_eq(Kind kind,
                                        const Node& node0,
                                        const Node& node1,
                                        OccMap& occs0,
                                        OccMap& occs1)
{
  assert(kind == Kind::BV_ADD || kind == Kind::BV_MUL);

  if (kind == Kind::BV_ADD)
  {
    compute_occurrences_add(node0, occs0);
    compute_occurrences_add(node1, occs1);

    auto value0 = normalize_add(node0, occs0);
    auto value1 = normalize_add(node1, occs1);

    normalize_occurrences_eq_add(node0.type().bv_size(), occs0, occs1);
    normalize_occurrences_eq_add(node0.type().bv_size(), occs1, occs0);

    if (!value0.is_zero() && !value1.is_zero())
    {
      value0.ibvsub(value1);
      Node val = d_env.nm().mk_value(value0);
      ++occs0[val];
    }
    else
    {
      // add normalized value to lhs occurrence map
      if (!value0.is_zero() || occs0.empty())
      {
        Node val = d_env.nm().mk_value(value0);
        ++occs0[val];
      }
      if (!value1.is_zero() || occs1.empty())
      {
        Node val = d_env.nm().mk_value(value1);
        ++occs1[val];
      }
    }

    if (occs1.empty())
    {
      Node val =
          d_env.nm().mk_value(BitVector::mk_zero(node1.type().bv_size()));
      ++occs1[val];
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL);

    compute_occurrences_mul(node0, occs0);
    compute_occurrences_mul(node1, occs1);

    auto value0 = normalize_mul(node0, occs0);
    auto value1 = normalize_mul(node1, occs1);

    if (!value0.is_one() || occs0.empty())
    {
      Node val = d_env.nm().mk_value(value0);
      ++occs0[val];
    }
    if (!value1.is_one() || occs1.empty())
    {
      Node val = d_env.nm().mk_value(value1);
      ++occs1[val];
    }
  }

  auto common_occs = compute_common_subterms(occs0, occs1);
  d_stats.num_common_normalizations += common_occs.size();
  if (kind == Kind::BV_MUL)
  {
    Node common = mk_node(kind, common_occs);
    if (!common.is_null())
    {
      ++occs0[common];
      ++occs1[common];
    }
  }
  // For sums, common parts are subtracted from both sides.
}

std::pair<Node, bool>
PassNormalize::normalize_eq(Kind kind, const Node& node0, const Node& node1)
{
  assert(kind == Kind::BV_ADD || kind == Kind::BV_MUL);

  NodeManager& nm = d_env.nm();

  OccMap occs0, occs1;
  normalize_occurrences_eq(kind, node0, node1, occs0, occs1);

  assert(!occs0.empty());
  assert(!occs1.empty());

  Node left  = mk_node(kind, occs0);
  Node right = mk_node(kind, occs1);

  if (left.is_null())
  {
    uint64_t size = node0.type().bv_size();
    left          = nm.mk_value(kind == Kind::BV_MUL ? BitVector::mk_one(size)
                                            : BitVector::mk_zero(size));
  }
  if (right.is_null())
  {
    uint64_t size = node1.type().bv_size();
    right         = nm.mk_value(kind == Kind::BV_MUL ? BitVector::mk_one(size)
                                             : BitVector::mk_zero(size));
  }

  if (left == right)
  {
    return {nm.mk_value(true), true};
  }

  bool normalized = left != node0 || right != node1;
  Node res        = d_rewriter.rewrite(nm.mk_node(Kind::EQUAL, {left, right}));
  return {res, normalized};
}

/* -------------------------------------------------------------------------- */

std::pair<Node, bool>
PassNormalize::normalize_comm_assoc(Kind parent_kind,
                                    const Node& node0,
                                    const Node& node1)
{
  NodeManager& nm = d_env.nm();

  Node top_lhs = get_top(node0);
  Node top_rhs = get_top(node1);

  Kind kind = top_lhs.kind();
  if (kind != Kind::BV_ADD && kind != Kind::BV_MUL
      && (kind != Kind::BV_NOT || top_lhs[0].kind() != Kind::BV_ADD))
  {
    kind = top_rhs.kind();
    if (kind != Kind::BV_ADD && kind != Kind::BV_MUL
        && (kind != Kind::BV_NOT || top_rhs[0].kind() != Kind::BV_ADD))
    {
      return {nm.mk_node(parent_kind, {node0, node1}), false};
    }
  }

  OccMap lhs, rhs;
  if (kind == Kind::BV_ADD || kind == Kind::BV_NOT)
  {
    compute_occurrences_add(top_lhs, lhs);
    compute_occurrences_add(top_rhs, rhs);
    normalize_add(top_lhs, lhs, true, true);
    normalize_add(top_rhs, rhs, true, true);
    kind = Kind::BV_ADD;
  }
  else
  {
    assert(kind == Kind::BV_MUL);
    compute_occurrences_mul(top_lhs, lhs);
    compute_occurrences_mul(top_rhs, rhs);
    normalize_mul(top_lhs, lhs, true);
    normalize_mul(top_rhs, rhs, true);
  }

  // Factor out common subterms
  auto common_occs = compute_common_subterms(lhs, rhs);
  Node common      = mk_node(kind, common_occs);

  if (!common.is_null())
  {
    ++lhs[common];
    ++rhs[common];
  }

  Node left = mk_node(kind, lhs);
  if (left.is_null())
  {
    uint64_t size = top_lhs.type().bv_size();
    left          = nm.mk_value(kind == Kind::BV_MUL ? BitVector::mk_one(size)
                                            : BitVector::mk_zero(size));
  }
  Node right = mk_node(kind, rhs);
  if (right.is_null())
  {
    uint64_t size = top_rhs.type().bv_size();
    right         = nm.mk_value(kind == Kind::BV_MUL ? BitVector::mk_one(size)
                                             : BitVector::mk_zero(size));
  }

  // Rebuild original term
  left  = rebuild_top(node0, top_lhs, left);
  right = rebuild_top(node1, top_rhs, right);

  bool normalized = left != node0 || right != node1;
  Node res        = d_rewriter.rewrite(nm.mk_node(parent_kind, {left, right}));
  return {res, normalized};
}

Node
PassNormalize::get_top(const Node& node)
{
  Node cur = node;
  Kind k;
  while (true)
  {
    k = cur.kind();
    if ((k == Kind::BV_NOT && cur[0].kind() != Kind::BV_ADD)
        || k == Kind::BV_SHL || k == Kind::BV_SHR || k == Kind::BV_EXTRACT)
    {
      cur = cur[0];
    }
    else if (k == Kind::BV_CONCAT && cur[0].is_value())
    {
      cur = cur[1];
    }
    else if (k == Kind::BV_CONCAT && cur[1].is_value())
    {
      cur = cur[0];
    }
    else if (k == Kind::BV_AND && cur[0].is_value())
    {
      cur = cur[1];
    }
    else if (k == Kind::BV_AND && cur[1].is_value())
    {
      cur = cur[0];
    }
    else
    {
      break;
    }
  }
  return cur;
}

Node
PassNormalize::rebuild_top(const Node& node,
                           const Node& top,
                           const Node& normalized)
{
  (void) top;

  assert(top.type() == normalized.type());

  node_ref_vector visit{node};
  std::unordered_map<Node, Node> cache;

  NodeManager& nm = d_env.nm();
  Kind k;
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());

    if (inserted)
    {
      k = cur.kind();
      if ((k == Kind::BV_NOT && cur[0].kind() != Kind::BV_ADD)
          || k == Kind::BV_SHL || k == Kind::BV_SHR || k == Kind::BV_EXTRACT)
      {
        visit.push_back(cur[0]);
        // Other children stay the same
        for (size_t i = 1, size = cur.num_children(); i < size; ++i)
        {
          cache.emplace(cur[i], cur[i]);
        }
        continue;
      }
      else if (k == Kind::BV_CONCAT && cur[0].is_value())
      {
        visit.push_back(cur[1]);
        cache.emplace(cur[0], cur[0]);
        continue;
      }
      else if (k == Kind::BV_CONCAT && cur[1].is_value())
      {
        visit.push_back(cur[0]);
        cache.emplace(cur[1], cur[1]);
        continue;
      }
      else if (k == Kind::BV_AND && cur[0].is_value())
      {
        visit.push_back(cur[1]);
        cache.emplace(cur[0], cur[0]);
        continue;
      }
      else if (k == Kind::BV_AND && cur[1].is_value())
      {
        visit.push_back(cur[0]);
        cache.emplace(cur[1], cur[1]);
        continue;
      }
      else
      {
        assert(cur == top);
        it->second = normalized;
        assert(it->second.type() == cur.type());
      }
    }
    else if (it->second.is_null())
    {
      it->second = utils::rebuild_node(nm, cur, cache);
      assert(it->second.type() == cur.type());
    }
    visit.pop_back();
  } while (!visit.empty());
  return cache.at(node);
}

void
PassNormalize::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  Log(1) << "Apply normalization";

  d_cache.clear();

  bool to_process   = false;
  bool inconsistent = false;
  std::vector<Node> assertions_pass1;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (!processed(assertion) && !inconsistent)
    {
      Node proc = process(assertion);
      assert(proc == process(assertion));
      const Node& processed = d_rewriter.rewrite(proc);
      assertions_pass1.push_back(processed);
      to_process = true;
      if (processed.is_value() && !processed.value<bool>())
      {
        inconsistent = true;
      }
    }
    else
    {
      assertions_pass1.push_back(assertion);
    }
  }

  const std::vector<Node>* processed_assertions = &assertions_pass1;
  bool replace_assertions                       = false;
  std::vector<Node> assertions_pass2;
  // Compute scores for bit widths <= 64
  if (d_enable_scoring && !inconsistent && to_process)
  {
    normalize_adders(assertions_pass1, assertions_pass2);

    util::Timer timer(d_stats.time_score);
    AigScore score_before, score_pass1, score_pass2;
    bool pass2_inconsistent = false;
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      // Only compute score if assertions differ
      if (assertions[i] != assertions_pass1[i]
          || assertions[i] != assertions_pass2[i])
      {
        score_before.add(assertions[i]);
        score_pass1.add(d_env.rewriter().rewrite(assertions_pass1[i]));
        score_pass2.add(d_env.rewriter().rewrite(assertions_pass2[i]));

        if (assertions_pass2[i].is_value()
            && !assertions_pass2[i].value<bool>())
        {
          pass2_inconsistent = true;
          break;
        }
      }
    }

    uint64_t size_before = 0, size_pass1 = 0, size_pass2 = 0;
    if (pass2_inconsistent)
    {
      size_pass1 = 1;
      size_pass2 = 0;
    }
    else
    {
      // Incrementally compute AIG score until we know if pass1 or pass2 has
      // a better score than the original assertions.
      while (!score_before.done() || !score_pass1.done() || !score_pass2.done())
      {
        score_before.process();
        score_pass1.process();
        score_pass2.process();

        // Pass1 score computed and is better than original score.
        if (score_pass1.done() && score_pass1.score() < score_before.score())
        {
          ++d_stats.num_pass1_successful;
          break;
        }
        // Pass2 score computed and is better than original score.
        if (score_pass2.done() && score_pass2.score() < score_before.score())
        {
          ++d_stats.num_pass2_successful;
          break;
        }
        // Original score computed, none of the passes was better.
        if (score_before.done())
        {
          break;
        }
      }
      size_before = score_before.score();
      size_pass1  = score_pass1.score();
      size_pass2  = score_pass2.score();
    }

    if (size_pass2 < size_pass1)
    {
      processed_assertions = &assertions_pass2;
    }

    size_t size_after  = std::min(size_pass1, size_pass2);
    replace_assertions = size_after < size_before;

    Log(1) << "AIG size initial: " << size_before;
    Log(1) << "AIG size pass 1:  " << size_pass1;
    Log(1) << "AIG size pass 2:  " << size_pass2;
  }

  if (replace_assertions || inconsistent)
  {
    const std::vector<Node>& assertions_normalized = *processed_assertions;
    assert(assertions_normalized.size() == assertions.size());
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      Node norm_assertion = d_env.rewriter().rewrite(assertions_normalized[i]);
      cache_assertion(assertions[i]);
      if (assertions[i] != norm_assertion)
      {
        cache_assertion(norm_assertion);
        assertions.replace(i, norm_assertion);
        ++d_stats.num_normalized_assertions;
      }
    }
  }

  d_cache.clear();
}

Node
PassNormalize::process(const Node& node)
{
  NodeManager& nm = d_env.nm();
  Node _node      = d_rewriter.rewrite(node);

  node_ref_vector visit{_node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_cache.emplace(cur, Node());
    if (inserted)
    {
      // Do not use scoring for bit-vectors larger than 64.
      if (d_enable_scoring && cur.type().is_bv() && cur.type().bv_size() > 64)
      {
        d_enable_scoring = false;
        Log(1) << "Disable AIG scoring, found bit-vector of size "
               << cur.type().bv_size();
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;
      for (const Node& child : cur)
      {
        auto itc = d_cache.find(child);
        assert(itc != d_cache.end());
        assert(!itc->second.is_null());
        children.push_back(itc->second);
      }

      Kind k = cur.kind();
      if (k == Kind::EQUAL)
      {
        bool norm;
        Node res = utils::rebuild_node(nm, cur, children);
        Node prev_res1, prev_res2, prev_res3, prev_res4;

#ifndef NDEBUG
        std::unordered_set<Node> norm_cache;
#endif

        // Apply normalization until fixed point.
        while (true)
        {
          assert(norm_cache.insert(res).second);
          // normalize: sum = sum
          // normalize: product = product
          if (prev_res1 != res && res.kind() == Kind::EQUAL
              && res[0].kind() == res[1].kind()
              && (res[0].kind() == Kind::BV_ADD
                  || res[0].kind() == Kind::BV_MUL))
          {
            std::tie(res, norm) = normalize_eq(res[0].kind(), res[0], res[1]);
            if (norm)
            {
              d_stats.num_normalizations += 1;
              res = d_rewriter.rewrite(res);
              assert(prev_res1 != res);
              prev_res1 = res;
              continue;
            }
          }

          // normalize: sum = t
          if (prev_res2 != res && res.kind() == Kind::EQUAL
              && (res[0].kind() == Kind::BV_ADD
                  || res[1].kind() == Kind::BV_ADD))
          {
            std::tie(res, norm) = normalize_eq(Kind::BV_ADD, res[0], res[1]);
            if (norm)
            {
              d_stats.num_normalizations += 1;
              res = d_rewriter.rewrite(res);
              assert(prev_res2 != res);
              prev_res2 = res;
              continue;
            }
          }

          // normalize: product = t
          if (prev_res3 != res && res.kind() == Kind::EQUAL
              && (((res[0].kind() == Kind::BV_MUL
                    || res[1].kind() == Kind::BV_MUL)
                   && (res[0].kind() != res[1].kind()))
                  || res[0].kind() == Kind::BV_SHL
                  || res[1].kind() == Kind::BV_SHL))
          {
            std::tie(res, norm) = normalize_eq(Kind::BV_MUL, res[0], res[1]);
            if (norm)
            {
              d_stats.num_normalizations += 1;
              res = d_rewriter.rewrite(res);
              assert(prev_res3 != res);
              prev_res3 = res;
              continue;
            }
          }

          //  normalize: top(sum|product) = top(sum|product)
          if (prev_res4 != res && res.kind() == Kind::EQUAL
              && (res[0].kind() != Kind::BV_ADD && res[0].kind() != Kind::BV_MUL
                  && res[1].kind() != Kind::BV_ADD
                  && res[1].kind() != Kind::BV_MUL))
          {
            std::tie(res, norm) = normalize_comm_assoc(k, res[0], res[1]);
            if (norm)
            {
              d_stats.num_normalizations += 1;
              res = d_rewriter.rewrite(res);
              assert(prev_res4 != res);
              prev_res4 = res;
              continue;
            }
          }
          break;
        }
        it->second = res;
      }
      else if (k == Kind::BV_ULT || k == Kind::BV_SLT)
      {
        auto [res, norm] = normalize_comm_assoc(k, children[0], children[1]);
        it->second       = res;
        if (norm)
        {
          d_stats.num_normalizations += 1;
        }
      }
      else
      {
        it->second = node::utils::rebuild_node(nm, cur, children);
      }
      it->second = d_rewriter.rewrite(it->second);
    }
    visit.pop_back();
  } while (!visit.empty());

  auto it = d_cache.find(_node);
  assert(it != d_cache.end());
  return d_rewriter.rewrite(it->second);
}

namespace {

Node
cmp_repr(const Node& node)
{
  std::reference_wrapper<const Node> n = node;
  while (n.get().kind() == Kind::BV_CONCAT || n.get().kind() == Kind::BV_EXTRACT
         || n.get().kind() == Kind::BV_NOT)
  {
    if (n.get().kind() == Kind::BV_CONCAT)
    {
      n = n.get()[1];
    }
    else
    {
      n = n.get()[0];
    }
  }
  return n;
}

bool
sort_cmp(const std::unordered_map<Node, std::vector<uint64_t>>& occs_sort,
         const Node& a,
         const Node& b)
{
  Node ra        = cmp_repr(a);
  Node rb        = cmp_repr(b);
  const auto& va = occs_sort.at(ra);
  const auto& vb = occs_sort.at(rb);

  if (va != vb)
  {
    for (size_t i = 0, size = std::min(va.size(), vb.size()); i < size; ++i)
    {
      if (va[i] != vb[i])
      {
        return va[i] < vb[i];
      }
    }
    if (va.size() != vb.size())
    {
      return va.size() > vb.size();
    }
  }
  return ra.id() < rb.id() || (ra.id() == rb.id() && a.id() < b.id());
}

void
remove_zero_occs(PassNormalize::OccMap& occs)
{
  util::Integer zero;
  auto it = occs.begin();
  while (it != occs.end())
  {
    if (it->second == zero)
    {
      it = occs.erase(it);
    }
    else
    {
      ++it;
    }
  }
}

}  // namespace

void
PassNormalize::normalize_adders(const std::vector<Node>& assertions,
                                std::vector<Node>& norm_assertions)
{
  util::Timer timer(d_stats.time_adder_chains);
  std::map<Node, OccMap> adders;
  collect_adders(assertions, adders);

  for (auto& [chain, cm] : adders)
  {
    remove_zero_occs(cm);
  }

  std::vector<std::pair<Node, size_t>> adder_chain_sizes;

  // Map element to list of chains it occurs in
  std::unordered_map<Node, std::vector<Node>> elements;
  std::unordered_map<Node, std::unordered_set<Node>> elements_sort;
  for (const auto& [chain, occs] : adders)
  {
    for (const auto& [n, occ] : occs)
    {
      assert(occ != 0);
      assert(!n.is_null());
      elements[n].push_back(chain);
      elements_sort[cmp_repr(n)].insert(chain);
    }
    adder_chain_sizes.emplace_back(chain, occs.size());
  }

  // Assign ids for each chain based on the number of elements in the chain
  std::sort(adder_chain_sizes.begin(),
            adder_chain_sizes.end(),
            [](const auto& a, const auto& b) { return a.second > b.second; });

  // Assign ids
  std::unordered_map<Node, uint64_t> id_map;
  for (const auto& [chain, _] : adder_chain_sizes)
  {
    id_map.emplace(chain, id_map.size());
  }

  // Map element to list of adder chains it occurs in
  std::vector<std::pair<Node, std::vector<uint64_t>>> occs;
  for (auto& [n, chains] : elements)
  {
    occs.emplace_back(n, std::vector<uint64_t>{});
    auto& vec = occs.back().second;
    assert(!chains.empty());
    for (const Node& add : chains)
    {
      vec.push_back(id_map[add]);
    }
    std::sort(vec.begin(), vec.end());
    assert(vec.size() == chains.size());
    assert(!occs.back().first.is_null());
  }

  std::unordered_map<Node, std::vector<uint64_t>> occs_sort;
  for (auto& [n, chains] : elements_sort)
  {
    auto [it, inserted] = occs_sort.emplace(n, std::vector<uint64_t>{});
    assert(inserted);
    auto& vec = it->second;
    assert(!chains.empty());
    for (const Node& add : chains)
    {
      vec.push_back(id_map[add]);
    }
    std::sort(vec.begin(), vec.end());
    assert(vec.size() == chains.size());
  }

  // Sort elements by id vectors, tie break with element id
  std::sort(
      occs.begin(), occs.end(), [&occs_sort](const auto& a, const auto& b) {
        return sort_cmp(occs_sort, a.first, b.first);
      });

  NodeManager& nm = d_env.nm();
  std::unordered_map<Node, Node> results;
  for (const auto& [element, _] : occs)
  {
    for (const auto& chain : elements[element])
    {
      auto [it, inserted] = results.emplace(chain, element);
      if (!inserted)
      {
        it->second = nm.mk_node(Kind::BV_ADD, {element, it->second});
      }
      --adders[chain][element];
    }
  }

  util::Integer zero, one(1);
  for (auto& [chain, res] : results)
  {
    for (const auto& [n, rem_occ] : adders[chain])
    {
      if (rem_occ == zero)
      {
        continue;
      }

      Node arg =
          rem_occ == one
              ? n
              : nm.mk_node(Kind::BV_MUL,
                           {nm.mk_value(BitVector(
                                n.type().bv_size(), rem_occ.gmp_value(), true)),
                            n});
      res      = nm.mk_node(Kind::BV_ADD, {arg, res});
    }
  }

  std::unordered_map<Node, Node> subst_cache;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    norm_assertions.push_back(
        d_rewriter.rewrite(substitute(assertions[i], results, subst_cache)));
  }
}

void
PassNormalize::collect_adders(const std::vector<Node>& assertions,
                              std::map<Node, OccMap>& adders)
{
  node_ref_vector visit{assertions.begin(), assertions.end()};
  unordered_node_ref_set cache;

  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      if (cur.kind() == Kind::BV_ADD)
      {
        auto [it, inserted] = adders.emplace(cur, OccMap());
        assert(inserted);
        compute_occurrences_add(cur, it->second);
        for (const auto& [node, occ] : it->second)
        {
          visit.push_back(node);
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

/* --- PassNormalize private ------------------------------------------------ */

PassNormalize::Statistics::Statistics(util::Statistics& stats,
                                      const std::string& prefix)
    : time_normalize_add(
          stats.new_stat<util::TimerStatistic>(prefix + "time_normalize_add")),
      time_normalize_mul(
          stats.new_stat<util::TimerStatistic>(prefix + "time_normalize_mul")),
      time_compute_occurrences(
          stats.new_stat<util::TimerStatistic>(prefix + "time_compute_occs")),
      time_adder_chains(
          stats.new_stat<util::TimerStatistic>(prefix + "time_adder_chains")),
      time_score(stats.new_stat<util::TimerStatistic>(prefix + "time_score")),
      num_normalizations(
          stats.new_stat<uint64_t>(prefix + "num_normalizations")),
      num_common_normalizations(
          stats.new_stat<uint64_t>(prefix + "num_common_normalizations")),
      num_normalized_assertions(
          stats.new_stat<uint64_t>(prefix + "num_normalized_assertions")),
      num_pass1_successful(stats.new_stat<uint64_t>(prefix + "num_pass1")),
      num_pass2_successful(stats.new_stat<uint64_t>(prefix + "num_pass2"))
{
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::preprocess::pass
