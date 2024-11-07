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
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "solver/bv/bv_solver.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

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
      d_rewriter(env, Rewriter::LEVEL_SPECULATIVE, "normalize"),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

/* -------------------------------------------------------------------------- */

void
PassNormalize::compute_coefficients(const Node& node,
                                    node::Kind kind,
                                    CoefficientsMap& coeffs) const
{
  util::Timer timer(d_stats.time_compute_coefficients);
  BitVector zero = BitVector::mk_zero(node.type().bv_size());

  node_ref_vector nodes;
  unordered_node_ref_set intermediate;
  unordered_node_ref_map<BitVector> cfs;  // all coefficients

  // Collect all traversed nodes (intermediate nodes of specified kind and
  // leafs) and initialize coefficients for each node to zero.
  node_ref_vector visit{node};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cfs.emplace(cur, zero);
    visit.pop_back();
    if (inserted)
    {
      nodes.push_back(cur);
      if (cur.kind() == kind)
      {
        intermediate.insert(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());

  // Compute leaf coefficients by pushing initial top node coefficient to leafs.
  //
  // Note: We have to ensure that parents are fully processed before we compute
  //       the coefficient for its children. Hence, we sort the nodes in
  //       ascending order and process the nodes with the higher IDs first.
  std::sort(nodes.begin(), nodes.end());
  assert(nodes.back() == node);
  cfs[node].ibvinc();  // Set initial coefficient of top node
  for (auto it = nodes.rbegin(), rend = nodes.rend(); it != rend; ++it)
  {
    const Node& cur = *it;
    auto fit        = cfs.find(cur);
    assert(fit != cfs.end());

    // If it's an intermediate node, push coefficient down to children
    if (intermediate.find(cur) != intermediate.end())
    {
      assert(cur.kind() == kind);
      for (const auto& child : cur)
      {
        assert(cfs.find(child) != cfs.end());
        cfs[child].ibvadd(fit->second);
      }
    }
    // If it's a leaf, just copy the result
    else
    {
      auto [it, inserted] = coeffs.emplace(cur, cfs[cur]);
      if (!inserted)
      {
        it->second.ibvadd(cfs[cur]);
      }
    }
  }
}

PassNormalize::CoefficientsMap
PassNormalize::compute_common_coefficients(PassNormalize::CoefficientsMap& lhs,
                                           PassNormalize::CoefficientsMap& rhs)
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

  CoefficientsMap common_coeff;
  for (auto it0 = lhs.begin(), end = lhs.end(); it0 != end; ++it0)
  {
    auto it1 = rhs.find(it0->first);
    if (it1 != rhs.end())
    {
      BitVector occs =
          it0->second.compare(it1->second) <= 0 ? it0->second : it1->second;
      if (occs.is_zero())
      {
        continue;
      }
      it0->second.ibvsub(occs);
      it1->second.ibvsub(occs);
      common_coeff.emplace(it0->first, occs);
    }
  }
  return common_coeff;
}

Node
PassNormalize::mk_node(Kind kind, const CoefficientsMap& coeffs)
{
  assert(kind == Kind::BV_ADD || kind == Kind::BV_MUL);

  Node res;
  if (coeffs.empty())
  {
    return res;
  }

  std::vector<std::pair<Node, BitVector>> coeffs_vec(coeffs.begin(),
                                                     coeffs.end());
  std::sort(
      coeffs_vec.begin(), coeffs_vec.end(), [](const auto& a, const auto& b) {
        return a.first.id() < b.first.id();
      });

  NodeManager& nm = d_env.nm();
  // combine common subterms
  if (kind == Kind::BV_ADD)
  {
    const auto& [node, coeff] = coeffs_vec[0];
    assert(!coeff.is_zero());
    res = coeff.is_one() ? node
                         : nm.mk_node(Kind::BV_MUL, {nm.mk_value(coeff), node});
    for (size_t i = 1, n = coeffs_vec.size(); i < n; ++i)
    {
      const auto& [node, coeff] = coeffs_vec[i];

      res = nm.mk_node(
          Kind::BV_ADD,
          {res,
           coeff.is_one()
               ? node
               : nm.mk_node(Kind::BV_MUL, {nm.mk_value(coeff), node})});
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL);
    while (coeffs_vec.size() > 1)
    {
      std::sort(coeffs_vec.begin(),
                coeffs_vec.end(),
                [](const auto& a, const auto& b) {
                  return a.second.compare(b.second) > 0;
                });
      while (coeffs_vec.back().second.is_zero())
      {
        coeffs_vec.pop_back();
      }
      for (size_t i = 1, n = coeffs_vec.size(); i < n; ++i)
      {
        assert(coeffs_vec[i - 1].second.compare(coeffs_vec[i].second) >= 0);
        const BitVector& occs = coeffs_vec[i].second;
        coeffs_vec[i].first =
            nm.mk_node(kind, {coeffs_vec[i - 1].first, coeffs_vec[i].first});
        coeffs_vec[i - 1].second.ibvsub(occs);
      }
    }
    res            = coeffs_vec.back().first;
    const auto& cf = coeffs_vec.back().second;
    assert(cf.size() - cf.count_leading_zeros() <= 64);
    for (size_t i = 1, n = cf.to_uint64(true); i < n; ++i)
    {
      res = nm.mk_node(kind, {res, coeffs_vec.back().first});
    }
  }
  return res;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_add(const Node& node,
                             CoefficientsMap& coeffs,
                             bool keep_value,
                             bool push_neg)
{
  assert(node.kind() == Kind::BV_ADD);
  util::Timer timer(d_stats.time_normalize_add);

  uint64_t bv_size = node.type().bv_size();
  BitVector bvzero = BitVector::mk_zero(bv_size);
  BitVector value  = bvzero;

  std::unordered_set<Node> cache;
  // std::cout << "----" << std::endl;
  bool progress;
  do
  {
    progress = false;
    for (auto it = coeffs.rbegin(); it != coeffs.rend(); ++it)
    {
      auto& [cur, cur_coeff] = *it;
      if (cur_coeff.is_zero())
      {
        continue;
      }

      // summarize values
      if (cur.is_value())
      {
        value.ibvadd(cur.value<BitVector>().bvmul(cur_coeff));
        cur_coeff = bvzero;
      }
      else if (cur.is_inverted())
      {
        auto it = coeffs.find(cur[0]);
        if (it != coeffs.end())
        {
          value.ibvadd(cur_coeff.bvneg());
          it->second.ibvsub(cur_coeff);
          cur_coeff = bvzero;
        }
        // normalize inverted adders
        // ~x = ~(x + 1) + 1 = - x - 1
        else if (push_neg && cur[0].kind() == Kind::BV_ADD)
        {
          // std::cout << "cur: " << cur << std::endl;
          assert(cache.insert(cur).second);
          progress = true;
          CoefficientsMap cfs;
          BitVector coeff = coeffs.at(cur).bvneg();
          cur_coeff       = bvzero;
          compute_coefficients(cur[0], cur[0].kind(), cfs);
          for (auto& [c, cf] : cfs)
          {
            cf.ibvmul(coeff);
            if (c.is_value())
            {
              value.ibvadd(c.value<BitVector>().bvmul(cf));
            }
            else
            {
              auto [it, inserted] = coeffs.emplace(c, cf);
              if (!inserted)
              {
                it->second.ibvadd(cf);
              }
            }
          }
          value.ibvadd(coeff);
          break;
        }
      }
    }
  } while (progress);

  if (keep_value && !value.is_zero())
  {
    Node val = d_env.nm().mk_value(value);
    auto it  = coeffs.find(val);
    if (it == coeffs.end())
    {
      coeffs.emplace(val, BitVector::mk_one(value.size()));
    }
    else
    {
      it->second.ibvinc();
    }
    return value;
  }

  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_and(const Node& node,
                             PassNormalize::CoefficientsMap& coeffs)
{
  BitVector bvzero = BitVector::mk_zero(node.type().bv_size());
  BitVector bvone  = BitVector::mk_one(node.type().bv_size());
  BitVector value  = bvone;

  for (auto& f : coeffs)
  {
    const Node& cur = f.first;
    // constant fold values
    if (cur.is_value())
    {
      value.ibvand(f.second);
      f.second = bvzero;
    }
    // normalize coefficient to 1
    else if (f.second.compare(bvone) > 0)
    {
      f.second = bvone;
    }
  }
  return value;
}

/* -------------------------------------------------------------------------- */

BitVector
PassNormalize::normalize_mul(const Node& node,
                             PassNormalize::CoefficientsMap& coeffs,
                             bool keep_value)
{
  assert(node.kind() == Kind::BV_MUL);

  uint64_t bv_size = node.type().bv_size();
  BitVector bvzero = BitVector::mk_zero(bv_size);
  BitVector value  = BitVector::mk_one(bv_size);

  for (auto& f : coeffs)
  {
    const Node& cur = f.first;

    // constant fold values
    if (cur.is_value())
    {
      assert(BitVector::fits_in_size(64, f.second.str(), 2));
      for (size_t i = 0, n = f.second.to_uint64(true); i < n; ++i)
      {
        value.ibvmul(cur.value<BitVector>());
      }
      f.second = bvzero;
    }
  }

  if (keep_value && !value.is_one())
  {
    Node val = d_env.nm().mk_value(value);
    auto it  = coeffs.find(val);
    if (it == coeffs.end())
    {
      coeffs.emplace(val, BitVector::mk_one(value.size()));
    }
    else
    {
      it->second.ibvinc();
    }
    return value;
  }

  return value;
}

/* -------------------------------------------------------------------------- */

void
PassNormalize::normalize_coefficients_eq_add(
    PassNormalize::CoefficientsMap& coeffs0,
    PassNormalize::CoefficientsMap& coeffs1,
    BitVector& value)
{
  // Note: Coefficients must already be normalized in the sense that they only
  //       either appear on the left or right hand side (this function must
  //       be called with coefficients determined by
  //       normalize_coefficients_eq()).
  //       We also assume that the adders have been normalized via
  //       normalize_add(), thus both coeffs maps doe not contain values
  //       with coefficients > 0.

  // (a - b + c = -d + e) is normalized to (a + c + d = b + e)

  // ~x = ~(x + 1) + 1
  // -x = ~x + 1

  uint64_t bv_size = value.size();
  NodeManager& nm  = d_env.nm();
  Node one         = nm.mk_value(BitVector::mk_one(bv_size));
  BitVector bvzero = BitVector::mk_zero(bv_size);

  // move negated occurrences to other side
  for (auto& f : coeffs0)
  {
    const Node& cur = f.first;
    BitVector coeff = f.second;
    assert(!cur.is_value() || coeff.is_zero());
    if (coeff.is_zero())
    {
      continue;
    }
    if (cur.is_inverted())
    {
      Node neg;
      if (cur[0].kind() == Kind::BV_ADD)
      {
        if (cur[0][0] == one)
        {
          neg = cur[0][1];
          value.ibvsub(coeff);
          f.second = bvzero;
        }
        else if (cur[0][1] == one)
        {
          neg = cur[0][0];
          value.ibvsub(coeff);
          f.second = bvzero;
        }
      }
      else
      {
        neg      = cur[0];
        f.second = bvzero;
      }
      if (!neg.is_null())
      {
        if (neg.is_value())
        {
          value.ibvsub(neg.value<BitVector>().bvmul(coeff));
        }
        else
        {
          auto it = coeffs1.find(neg);
          if (it == coeffs1.end())
          {
            coeffs1.emplace(neg, coeff);
          }
          else
          {
            it->second.ibvadd(coeff);
          }
        }
        value.ibvsub(coeff);
      }
    }
  }
}

void
PassNormalize::normalize_coefficients_eq(
    const Node& node0,
    const Node& node1,
    PassNormalize::CoefficientsMap& coeffs0,
    PassNormalize::CoefficientsMap& coeffs1)
{
  assert(node0.kind() == node1.kind());
  assert(node0.kind() == Kind::BV_ADD || node0.kind() == Kind::BV_MUL);

  Kind kind = node0.kind();

  compute_coefficients(node0, node0.kind(), coeffs0);
  compute_coefficients(node1, node1.kind(), coeffs1);

  if (kind == Kind::BV_ADD)
  {
    auto value0 = normalize_add(node0, coeffs0);
    auto value1 = normalize_add(node1, coeffs1);
    normalize_coefficients_eq_add(coeffs0, coeffs1, value0);
    normalize_coefficients_eq_add(coeffs1, coeffs0, value1);
    value0.ibvsub(value1);
    // add normalized value to lhs coefficients map
    if (!value0.is_zero())
    {
      Node val = d_env.nm().mk_value(value0);
      auto it  = coeffs0.find(val);
      if (it == coeffs0.end())
      {
        coeffs0.emplace(val, BitVector::mk_one(value0.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
  }
  else
  {
    assert(kind == Kind::BV_MUL);
    auto value0 = normalize_mul(node0, coeffs0);
    auto value1 = normalize_mul(node1, coeffs1);
    if (!value0.is_one())
    {
      Node val = d_env.nm().mk_value(value0);
      auto it  = coeffs0.find(val);
      if (it == coeffs0.end())
      {
        coeffs0.emplace(val, BitVector::mk_one(value0.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
    if (!value1.is_one())
    {
      Node val = d_env.nm().mk_value(value1);
      auto it  = coeffs1.find(val);
      if (it == coeffs1.end())
      {
        coeffs1.emplace(val, BitVector::mk_one(value1.size()));
      }
      else
      {
        assert(it->second.is_zero());
        it->second.ibvinc();
      }
    }
  }

  auto common_coeffs = compute_common_coefficients(coeffs0, coeffs1);
  Node common        = mk_node(kind, common_coeffs);
  if (kind == Kind::BV_MUL && !common.is_null())
  {
    BitVector bvone = BitVector::mk_one(node0.type().bv_size());
    {
      auto [it, inserted] = coeffs0.emplace(common, bvone);
      if (!inserted)
      {
        coeffs0[common].ibvinc();
      }
    }
    {
      auto [it, inserted] = coeffs1.emplace(common, bvone);
      if (!inserted)
      {
        coeffs1[common].ibvinc();
      }
    }
  }
}

std::pair<Node, Node>
PassNormalize::_normalize_eq_mul(const CoefficientsMap& coeffs0,
                                 const CoefficientsMap& coeffs1)
{
  assert(!coeffs0.empty());
  assert(!coeffs1.empty());

  NodeManager& nm = d_env.nm();
  std::vector<Node> lhs, rhs;
  for (const auto& f : coeffs0)
  {
    if (f.second.is_zero())
    {
      continue;
    }
    assert(BitVector::fits_in_size(64, f.second.str(), 2));
    lhs.insert(lhs.end(), f.second.to_uint64(true), f.first);
  }
  for (const auto& f : coeffs1)
  {
    if (f.second.is_zero())
    {
      continue;
    }
    assert(BitVector::fits_in_size(64, f.second.str(), 2));
    rhs.insert(rhs.end(), f.second.to_uint64(true), f.first);
  }

  if (lhs.empty())
  {
    lhs.push_back(nm.mk_value(
        BitVector::mk_one(coeffs0.begin()->first.type().bv_size())));
  }
  if (rhs.empty())
  {
    rhs.push_back(nm.mk_value(
        BitVector::mk_one(coeffs1.begin()->first.type().bv_size())));
  }

  std::sort(lhs.begin(), lhs.end());
  std::sort(rhs.begin(), rhs.end());

  Node left, right;
  size_t n = lhs.size();
  left     = lhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    left = nm.mk_node(Kind::BV_MUL, {lhs[n - i - 1], left});
  }
  n     = rhs.size();
  right = rhs[n - 1];
  for (size_t i = 1; i < n; ++i)
  {
    right = nm.mk_node(Kind::BV_MUL, {rhs[n - i - 1], right});
  }
  return {left, right};
}

namespace {
Node
get_factorized_add(NodeManager& nm, const Node& node, const BitVector& coeff)
{
  assert(!node.is_null());
  assert(!coeff.is_zero());
  if (coeff.is_one())
  {
    return node;
  }
  if (coeff.is_ones())
  {
    return nm.mk_node(Kind::BV_NEG, {node});
  }
  return nm.mk_node(Kind::BV_MUL, {nm.mk_value(coeff), node});
}
}  // namespace

std::pair<Node, Node>
PassNormalize::_normalize_eq_add(PassNormalize::CoefficientsMap& coeffs0,
                                 PassNormalize::CoefficientsMap& coeffs1,
                                 uint64_t bv_size)
{
  NodeManager& nm = d_env.nm();

  BitVector lvalue = BitVector::mk_zero(bv_size);
  BitVector rvalue = BitVector::mk_zero(bv_size);

  std::vector<Node> lhs, rhs;

  for (const auto& f : coeffs0)
  {
    const Node& cur        = f.first;
    const BitVector& coeff = f.second;
    if (coeff.is_zero())
    {
      continue;
    }
    if (cur.is_value())
    {
      assert(coeff.is_one());
      lvalue.ibvadd(cur.value<BitVector>());
    }
    else
    {
      lhs.push_back(get_factorized_add(nm, cur, coeff));
    }
  }
  for (const auto& f : coeffs1)
  {
    const Node& cur        = f.first;
    const BitVector& coeff = f.second;
    if (coeff.is_zero())
    {
      continue;
    }
    assert(!cur.is_value());
    rhs.push_back(get_factorized_add(nm, cur, coeff));
  }

  // normalize values, e.g., (a + 2 = b + 3) -> (a - 1 = b)
  if (!lvalue.is_zero())
  {
    lvalue.ibvsub(rvalue);
    if (!lvalue.is_zero())
    {
      lhs.push_back(nm.mk_value(lvalue));
    }
  }
  else if (!rvalue.is_zero())
  {
    rhs.push_back(nm.mk_value(rvalue));
  }

  std::sort(lhs.begin(), lhs.end());
  std::sort(rhs.begin(), rhs.end());

  Node left  = lhs.empty() ? nm.mk_value(BitVector::mk_zero(bv_size))
                           : node::utils::mk_nary(nm, Kind::BV_ADD, lhs);
  Node right = rhs.empty() ? nm.mk_value(BitVector::mk_zero(bv_size))
                           : node::utils::mk_nary(nm, Kind::BV_ADD, rhs);
  return {left, right};
}

std::pair<Node, bool>
PassNormalize::normalize_eq_add_mul(const Node& node0, const Node& node1)
{
  assert(node0.kind() == node1.kind());
  assert(node0.kind() == Kind::BV_MUL || node0.kind() == Kind::BV_ADD);

  NodeManager& nm = d_env.nm();

  CoefficientsMap coeffs0, coeffs1;
  normalize_coefficients_eq(node0, node1, coeffs0, coeffs1);

  assert(!coeffs0.empty() && !coeffs1.empty());

  auto [left, right] =
      node0.kind() == Kind::BV_ADD
          ? _normalize_eq_add(coeffs0, coeffs1, node0.type().bv_size())
          : _normalize_eq_mul(coeffs0, coeffs1);

  if (left == right)
  {
    return {nm.mk_value(true), true};
  }

  if (left == node0 && right == node1)
  {
    return {nm.mk_node(Kind::EQUAL, {node0, node1}), false};
  }

  return {nm.mk_node(Kind::EQUAL, {left, right}), true};
}

/* -------------------------------------------------------------------------- */

namespace {

}  // namespace

void
PassNormalize::remove_zero_coeffs(PassNormalize::CoefficientsMap& coeffs)
{
  auto it = coeffs.begin();
  while (it != coeffs.end())
  {
    if (it->second.is_zero())
    {
      it = coeffs.erase(it);
    }
    else
    {
      ++it;
    }
  }
}

std::pair<Node, Node>
PassNormalize::normalize_common(Kind kind,
                                PassNormalize::CoefficientsMap& lhs,
                                PassNormalize::CoefficientsMap& rhs)
{
  std::vector<Node> lhs_norm, rhs_norm;
  assert(!lhs.empty());
  assert(!rhs.empty());

  size_t lhs_size    = lhs.begin()->first.type().bv_size();
  size_t rhs_size    = rhs.begin()->first.type().bv_size();
  auto common_coeffs = compute_common_coefficients(lhs, rhs);
  Node common        = mk_node(kind, common_coeffs);

  if (!common.is_null())
  {
    auto [it, inserted] = lhs.emplace(common, BitVector::mk_one(lhs_size));
    if (!inserted)
    {
      it->second.ibvinc();
    }
    std::tie(it, inserted) = rhs.emplace(common, BitVector::mk_one(rhs_size));
    if (!inserted)
    {
      it->second.ibvinc();
    }
  }

  remove_zero_coeffs(lhs);
  remove_zero_coeffs(rhs);

  Node left, right;
  if (!lhs.empty())
  {
    left = mk_node(kind, lhs);
  }
  else
  {
    left = d_env.nm().mk_value(BitVector::mk_zero(lhs_size));
  }
  if (!rhs.empty())
  {
    right = mk_node(kind, rhs);
  }
  else
  {
    right = d_env.nm().mk_value(BitVector::mk_zero(rhs_size));
  }
  return {left, right};
}

std::pair<Node, bool>
PassNormalize::normalize_comm_assoc(Kind parent_kind,
                                    const Node& node0,
                                    const Node& node1)
{
  NodeManager& nm = d_env.nm();

  Node top_lhs = get_top(node0);
  Node top_rhs = get_top(node1);

  Kind kind = top_lhs.kind();
  if (kind != Kind::BV_ADD && kind != Kind::BV_MUL)
  // && kind != Kind::BV_AND && kind != Kind::BV_XOR))
  {
    kind = top_rhs.kind();
    if (kind != Kind::BV_ADD && kind != Kind::BV_MUL)
    {
      return {nm.mk_node(parent_kind, {node0, node1}), false};
    }
  }

  CoefficientsMap lhs, rhs;
  compute_coefficients(top_lhs, kind, lhs);
  compute_coefficients(top_rhs, kind, rhs);
  if (top_lhs.kind() == Kind::BV_ADD)
  {
    normalize_add(top_lhs, lhs, true, true);
  }
  else if (top_lhs.kind() == Kind::BV_MUL)
  {
    normalize_mul(top_lhs, lhs, true);
  }
  if (top_rhs.kind() == Kind::BV_ADD)
  {
    normalize_add(top_rhs, rhs, true, true);
  }
  else if (top_rhs.kind() == Kind::BV_MUL)
  {
    normalize_mul(top_rhs, rhs, true);
  }
  auto [left, right] = normalize_common(kind, lhs, rhs);
  auto rebuilt_left  = rebuild_top(node0, top_lhs, left);
  auto rebuilt_right = rebuild_top(node1, top_rhs, right);

  // std::cout << "normalization done" << std::endl;
  return {nm.mk_node(parent_kind, {rebuilt_left, rebuilt_right}),
          rebuilt_left != node0 || rebuilt_right != node1};
}

std::pair<Node, bool>
PassNormalize::normalize_comm_assoc(const Node& node)
{
  NodeManager& nm = d_env.nm();
  assert(node.kind() == Kind::BV_ADD || node.kind() == Kind::BV_MUL);

  Kind kind = node.kind();

  CoefficientsMap coeffs;
  // std::cout << "compute coeff lhs: " << std::flush;
  compute_coefficients(node, kind, coeffs);
  size_t coeffs_size = coeffs.size();
  // std::cout << "done" << std::endl;;
  if (kind == Kind::BV_ADD)
  {
    normalize_add(node, coeffs, true, true);
  }
  else if (kind == Kind::BV_MUL)
  {
    normalize_mul(node, coeffs, true);
  }
  remove_zero_coeffs(coeffs);
#if 1
  if (coeffs_size <= coeffs.size())
  {
    return {node, false};
  }
#endif
  Node res = coeffs.empty()
                 ? nm.mk_value(BitVector::mk_zero(node.type().bv_size()))
                 : mk_node(kind, coeffs);

  // std::cout << "normalization done" << std::endl;
  return {res, res != node};
}

Node
PassNormalize::get_top(const Node& node)
{
  Node cur = node;
  Kind k;
  while (true)
  {
    k = cur.kind();
    if (k == Kind::BV_NOT || k == Kind::BV_SHL || k == Kind::BV_SHR
        || k == Kind::BV_EXTRACT)
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
      if (k == Kind::BV_NOT || k == Kind::BV_SHL || k == Kind::BV_SHR
          || k == Kind::BV_EXTRACT)
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

namespace {
#if 0
void
_count_kinds(const Node& node,
             std::unordered_set<Node>& cache,
             std::unordered_map<Kind, uint64_t>& kinds)
{
  std::vector<Node> visit{node};
  do
  {
    Node cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      kinds[cur.kind()] += 1;
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

std::unordered_map<Kind, uint64_t>
_count_kinds(AssertionVector& assertions)
{
  std::unordered_map<Kind, uint64_t> kinds;
  std::unordered_set<Node> cache;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    _count_kinds(assertion, cache, kinds);
  }
  return kinds;
}

void
print_diff(const std::unordered_map<Kind, uint64_t>& before,
           const std::unordered_map<Kind, uint64_t>& after)
{
  std::unordered_set<Kind> kinds;
  //std::cout << "*** before:" << std::endl;
  std::vector<std::pair<int64_t, Kind>> pairs;
  for (auto [k, v] : before)
  {
    //std::cout << v << ": " << k << std::endl;
    auto it = after.find(k);
    if (it != after.end())
    {
      pairs.emplace_back(it->second - v, k);
    }
  }
  for (auto [k, v] : after)
  {
    auto it = before.find(k);
    if (it == before.end())
    {
      pairs.emplace_back(v, k);
    }
  }

  //std::cout << "*** diff:" << std::endl;
  std::sort(pairs.begin(), pairs.end());
  for (auto [v, k] : pairs)
  {
    if (v != 0)
    {
      //std::cout << std::showpos << v << std::noshowpos << ": " << k
                << std::endl;
    }
  }
}
#endif

Node
rewrite_term(NodeManager& nm,
             const Node& cur,
             const std::vector<Node>& children)
{
  Kind k = cur.kind();

  if (k == Kind::EQUAL)
  {
    Node mul, val;
    if (children[0].kind() == Kind::BV_MUL)
    {
      mul = children[0];
      val = children[1];
    }
    else if (children[1].kind() == Kind::BV_MUL)
    {
      mul = children[1];
      val = children[0];
    }

    if (!val.is_null() && val.is_value() && val.value<BitVector>().is_zero())
    {
      Node udiv, t;
      if (mul[0].kind() == Kind::BV_UDIV)
      {
        udiv = mul[0];
        t    = mul[1];
      }
      else if (mul[1].kind() == Kind::BV_UDIV)
      {
        udiv = mul[1];
        t    = mul[0];
      }

      if (!udiv.is_null() && udiv[1] == t)
      {
        return nm.mk_node(Kind::OR,
                          {nm.mk_node(Kind::EQUAL, {t, val}),
                           nm.mk_node(Kind::BV_UGT, {t, udiv[0]})});
      }
    }
  }

  return Node();
}

}  // namespace

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
      const Node& processed = d_env.rewriter().rewrite(process(assertion));
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
          || assertions[i] == assertions_pass2[i])
      {
        score_before.add(assertions[i]);
        score_pass1.add(assertions_pass1[i]);
        score_pass2.add(assertions_pass2[i]);

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
          break;
        }
        // Pass2 score computed and is better than original score.
        if (score_pass2.done() && score_pass2.score() < score_before.score())
        {
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
      cache_assertion(assertions[i]);
      if (assertions[i] != assertions_normalized[i])
      {
        cache_assertion(assertions_normalized[i]);
        assertions.replace(i, assertions_normalized[i]);
        ++d_stats.num_normalized_assertions;
      }
    }
  }

  d_cache.clear();
}

namespace {
/**
 * Distributive multiplication (recursive up to a given depth).
 *
 * - (bvmul (bvshl x s) r) -> (bvshl (bvmul x r) s)
 * - (bvmul l (bvshl x s)) -> (bvshl (bvmul x l) s)
 * - (bvmul (bvadd x s) r) -> (bvadd (bvmul x r) (bvmul (s r)))
 * - (bvmul l (bvadd x s)) -> (bvadd (bvmul x l) (bvmul (s l)))
 *
 * @param left  The left operand of the multiplication.
 * @param right The right operand of the multiplication.
 * @param depth The recursion depth.
 * @return The resulting node.
 */
Node
distrib_mul(NodeManager& nm, const Node& left, const Node& right, uint8_t depth)
{
  if (depth && left.kind() == Kind::BV_SHL && !right.is_value())
  {
    return nm.mk_node(Kind::BV_SHL,
                      {distrib_mul(nm, left[0], right, depth - 1), left[1]});
  }
  if (depth && right.kind() == Kind::BV_SHL && !left.is_value())
  {
    return nm.mk_node(Kind::BV_SHL,
                      {distrib_mul(nm, right[0], left, depth - 1), right[1]});
  }
  if (depth && left.kind() == Kind::BV_ADD && !right.is_value())
  {
    return nm.mk_node(Kind::BV_ADD,
                      {distrib_mul(nm, left[0], right, depth - 1),
                       distrib_mul(nm, left[1], right, depth - 1)});
  }
  if (depth && right.kind() == Kind::BV_ADD && !left.is_value())
  {
    return nm.mk_node(Kind::BV_ADD,
                      {distrib_mul(nm, right[0], left, depth - 1),
                       distrib_mul(nm, right[1], left, depth - 1)});
  }
  return nm.mk_node(Kind::BV_MUL, {left, right});
}

}  // namespace

Node
PassNormalize::process(const Node& node)
{
  NodeManager& nm = d_env.nm();
  Node _node      = d_rewriter.rewrite(node);
  bool normalized = false;
  do
  {
    normalized = false;
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
        if (k == Kind::EQUAL && children[0].kind() == children[1].kind()
            && (children[0].kind() == Kind::BV_ADD
                || children[0].kind() == Kind::BV_MUL))
        {
          auto [res, norm] = normalize_eq_add_mul(children[0], children[1]);
          if (norm)
          {
            d_stats.num_normalizations += 1;
            normalized = true;
          }
          it->second = res;
        }
        else if (k == Kind::EQUAL)
        {
          Node rw = rewrite_term(nm, cur, children);
          if (rw.is_null())
          {
            auto [res, norm] =
                normalize_comm_assoc(k, children[0], children[1]);
            it->second = res;
            if (norm)
            {
              d_stats.num_normalizations += 1;
              normalized = true;
            }
          }
          else
          {
            it->second = rw;
          }
        }
        else if (k == Kind::BV_ULT || k == Kind::BV_SLT)
        {
          auto [res, norm] = normalize_comm_assoc(k, children[0], children[1]);
          it->second       = res;
          if (norm)
          {
            d_stats.num_normalizations += 1;
            normalized = true;
          }
        }
        else if (k == Kind::BV_MUL)
        {
          it->second =
              d_rewriter.rewrite(distrib_mul(nm, children[0], children[1], 5));
        }
        else
        {
          it->second = node::utils::rebuild_node(nm, cur, children);
        }
      }
      visit.pop_back();
    } while (!visit.empty());
    if (normalized)
    {
      _node = d_cache.at(_node);
    }
  } while (normalized);
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

}  // namespace

void
PassNormalize::normalize_adders(const std::vector<Node>& assertions,
                                std::vector<Node>& norm_assertions)
{
  util::Timer timer(d_stats.time_adder_chains);
  std::map<Node, CoefficientsMap> adders;
  collect_adders(assertions, adders);

  for (auto& [chain, cm] : adders)
  {
    remove_zero_coeffs(cm);
  }

  std::vector<std::pair<Node, size_t>> adder_chain_sizes;

  // Map element to list of chains it occurs in
  std::unordered_map<Node, std::vector<Node>> elements;
  std::unordered_map<Node, std::unordered_set<Node>> elements_sort;
  for (const auto& [chain, coeffs] : adders)
  {
    for (const auto& [n, coeff] : coeffs)
    {
      assert(!coeff.is_zero());
      assert(!n.is_null());
      elements[n].push_back(chain);
      elements_sort[cmp_repr(n)].insert(chain);
    }
    adder_chain_sizes.emplace_back(chain, coeffs.size());
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
      auto& coeff = adders[chain][element];
      coeff.ibvdec();
    }
  }

  for (auto& [chain, res] : results)
  {
    for (const auto& [n, rem_coeff] : adders[chain])
    {
      if (rem_coeff.is_zero())
      {
        continue;
      }

      Node arg = rem_coeff.is_one()
                     ? n
                     : nm.mk_node(Kind::BV_MUL, {nm.mk_value(rem_coeff), n});
      res      = nm.mk_node(Kind::BV_ADD, {arg, res});
    }
  }

  std::unordered_map<Node, Node> subst_cache;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    norm_assertions.push_back(d_env.rewriter().rewrite(
        substitute(assertions[i], results, subst_cache)));
  }
}

void
PassNormalize::collect_adders(const std::vector<Node>& assertions,
                              std::map<Node, CoefficientsMap>& adders)
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
        auto [it, inserted] = adders.emplace(cur, CoefficientsMap());
        assert(inserted);
        compute_coefficients(cur, cur.kind(), it->second);
        for (const auto& [node, coeff] : it->second)
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
      time_compute_coefficients(
          stats.new_stat<util::TimerStatistic>(prefix + "time_compute_coeff")),
      time_adder_chains(
          stats.new_stat<util::TimerStatistic>(prefix + "time_adder_chains")),
      time_score(stats.new_stat<util::TimerStatistic>(prefix + "time_score")),
      num_normalizations(
          stats.new_stat<uint64_t>(prefix + "num_normalizations")),
      num_normalized_assertions(
          stats.new_stat<uint64_t>(prefix + "num_normalized_assertions"))
{
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::preprocess::pass
