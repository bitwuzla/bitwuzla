/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "ls/ls_bv.h"

#include <cassert>
#include <functional>
#include <iostream>
#include <unordered_set>

#include "../util/hash_pair.h"
#include "bv/bitvector.h"
#include "ls/bv/bitvector_domain.h"
#include "ls/bv/bitvector_node.h"

namespace bzla::ls {

/* LocalSearchBv public ----------------------------------------------------- */

LocalSearchBV::LocalSearchBV(uint64_t max_nprops,
                             uint64_t max_nupdates,
                             uint32_t seed)
    : LocalSearch<BitVector>(max_nprops, max_nupdates, seed)

{
  d_true.reset(new BitVector(BitVector::mk_true()));
}

uint64_t
LocalSearchBV::mk_node(NodeKind kind,
                       uint64_t size,
                       const std::vector<uint64_t>& children,
                       const std::vector<uint64_t>& indices,
                       const std::optional<std::string>& symbol)
{
  return _mk_node(kind, size, children, indices, true, symbol);
}

uint64_t
LocalSearchBV::mk_node(NodeKind kind,
                       const BitVectorDomain& domain,
                       const std::vector<uint64_t>& children,
                       const std::vector<uint64_t>& indices,
                       const std::optional<std::string>& symbol)
{
  return _mk_node(kind, domain, children, indices, true, symbol);
}

uint64_t
LocalSearchBV::mk_node(const BitVector& assignment,
                       const BitVectorDomain& domain,
                       const std::optional<std::string>& symbol)
{
  assert(assignment.size() == domain.size());  // API check
  uint64_t id = d_nodes.size();
  std::unique_ptr<BitVectorNode> res(
      new BitVectorNode(d_rng.get(), assignment, domain));
  res->set_id(id);
  res->set_symbol(symbol);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

uint64_t
LocalSearchBV::invert_node(uint64_t id)
{
  assert(id < d_nodes.size());  // API check
  return mk_node(NodeKind::NOT, get_node(id)->domain().bvnot(), {id});
}

const BitVectorDomain&
LocalSearchBV::get_domain(uint64_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->domain();
}

void
LocalSearchBV::fix_bit(uint64_t id, uint32_t idx, bool value)
{
  assert(id < d_nodes.size());  // API check
  BitVectorNode* node = get_node(id);
  assert(idx < node->domain().size());  // API check
  node->fix_bit(idx, value);
}

/* LocalSearchBv private ---------------------------------------------------- */

uint64_t
LocalSearchBV::_mk_node(NodeKind kind,
                        uint64_t size,
                        const std::vector<uint64_t>& children,
                        const std::vector<uint64_t>& indices,
                        bool normalize,
                        const std::optional<std::string>& symbol)
{
  return _mk_node(
      kind, BitVectorDomain(size), children, indices, normalize, symbol);
}

uint64_t
LocalSearchBV::_mk_node(NodeKind kind,
                        const BitVectorDomain& domain,
                        const std::vector<uint64_t>& children,
                        const std::vector<uint64_t>& indices,
                        bool normalize,
                        const std::optional<std::string>& symbol)
{
  uint64_t id = d_nodes.size();
  for (uint64_t c : children)
  {
    assert(c < id);  // API check
    assert(d_parents.find(c) != d_parents.end());
    d_parents.at(c).insert(id);
  }

  std::unique_ptr<BitVectorNode> res;

  switch (kind)
  {
    case NodeKind::CONST:
      assert(children.size() == 0);  // API check
      assert(indices.size() == 0);   // API check
      return mk_node(domain.lo(), domain);

    case NodeKind::EQ:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorEq(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::ITE:
      assert(children.size() == 3);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorIte(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 get_node(children[2])));
      break;
    case NodeKind::BV_ADD:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorAdd(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;

    case NodeKind::AND:
    case NodeKind::BV_AND:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorAnd(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_ASHR:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorAshr(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_CONCAT:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorConcat(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_MUL:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorMul(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::NOT:
    case NodeKind::BV_NOT:
      assert(children.size() == 1);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorNot(d_rng.get(), domain, get_node(children[0])));
      break;
    case NodeKind::BV_SHL:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorShl(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_SHR:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorShr(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_SLT:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorSlt(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 d_options.use_opt_lt_concat_sext));
      break;
    case NodeKind::BV_UDIV:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorUdiv(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_ULT:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorUlt(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 d_options.use_opt_lt_concat_sext));
      break;
    case NodeKind::BV_UREM:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorUrem(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::XOR:
    case NodeKind::BV_XOR:
      assert(children.size() == 2);  // API check
      assert(indices.size() == 0);   // API check
      res.reset(new BitVectorXor(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;

    case NodeKind::BV_EXTRACT: {
      assert(children.size() == 1);      // API check
      assert(indices.size() == 2);       // API check
      assert(indices[0] >= indices[1]);  // API check
      assert(indices[0] < get_node(children[0])->size());
      BitVectorNode* child0 = get_node(children[0]);
      res.reset(new BitVectorExtract(
          d_rng.get(), domain, child0, indices[0], indices[1], normalize));
      if (normalize)
      {
        d_to_normalize_nodes.insert(child0);
      }
      break;
    }

    case NodeKind::BV_SEXT:
      assert(children.size() == 1);  // API check
      assert(indices.size() == 1);   // API check
      res.reset(new BitVectorSignExtend(
          d_rng.get(), domain, get_node(children[0]), indices[0]));
      break;

    default: assert(0);  // API check
  }
  res->set_id(id);
  res->set_symbol(symbol);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};

  return id;
}

BitVectorNode*
LocalSearchBV::get_node(uint64_t id) const
{
  return reinterpret_cast<BitVectorNode*>(LocalSearch<BitVector>::get_node(id));
}

void
LocalSearchBV::update_bounds_aux(BitVectorNode* root, int32_t pos)
{
  assert(root->is_inequality());
  assert(root->arity() == 2);

  BitVectorNode* child0 = root->child(0);
  BitVectorNode* child1 = root->child(1);
  bool is_signed        = root->kind() == NodeKind::BV_SLT;
  uint64_t size         = child0->size();
  BitVector min_value, max_value;

  if (is_signed)
  {
    min_value = BitVector::mk_min_signed(size);
    max_value = BitVector::mk_max_signed(size);
  }
  else
  {
    min_value = BitVector::mk_zero(size);
    max_value = BitVector::mk_ones(size);
  }

  bool is_ult = d_roots_ineq.at(root);
  assert((is_ult && root->assignment().is_true())
         || (!is_ult && root->assignment().is_false()));
  if (is_ult)
  {
    // x < s
    if (!child0->all_value() && (pos < 0 || pos == 0))
    {
      assert((is_signed && child1->assignment().signed_compare(min_value) > 0)
             || (!is_signed && child1->assignment().compare(min_value) > 0));
      child0->update_bounds(
          min_value, child1->assignment(), false, true, is_signed);
      assert(is_signed || child0->min_u()->compare(*child0->max_u()) <= 0);
      assert(!is_signed
             || child0->min_s()->signed_compare(*child0->max_s()) <= 0);
    }

    // s < x
    if (!child1->all_value() && (pos < 0 || pos == 1))
    {
      assert((is_signed && child0->assignment().signed_compare(max_value) < 0)
             || (!is_signed && child0->assignment().compare(max_value) < 0));
      child1->update_bounds(
          child0->assignment(), max_value, true, false, is_signed);
      assert(is_signed || child1->min_u()->compare(*child1->max_u()) <= 0);
      assert(!is_signed
             || child1->min_s()->signed_compare(*child1->max_s()) <= 0);
    }
  }
  else
  {
    // x >= s
    if (!child0->all_value() && (pos < 0 || pos == 0))
    {
      assert((is_signed && child1->assignment().signed_compare(max_value) <= 0)
             || (!is_signed && child1->assignment().compare(max_value) <= 0));
      child0->update_bounds(
          child1->assignment(), max_value, false, false, is_signed);
      assert(is_signed || child0->min_u()->compare(*child0->max_u()) <= 0);
      assert(!is_signed
             || child0->min_s()->signed_compare(*child0->max_s()) <= 0);
    }

    // s >= x
    if (!child1->all_value() && (pos < 0 || pos == 1))
    {
      assert((is_signed && min_value.signed_compare(child0->assignment()) <= 0)
             || (!is_signed && min_value.compare(child0->assignment()) <= 0));
      child1->update_bounds(
          min_value, child0->assignment(), false, false, is_signed);
      assert(is_signed || child1->min_u()->compare(*child1->max_u()) <= 0);
      assert(!is_signed
             || child1->min_s()->signed_compare(*child1->max_s()) <= 0);
    }
  }
}

void
LocalSearchBV::compute_bounds(Node<BitVector>* node)
{
  BitVectorNode* n = reinterpret_cast<BitVectorNode*>(node);
  for (uint32_t i = 0, arity = node->arity(); i < arity; ++i)
  {
    n->child(i)->reset_bounds();
  }
  for (uint32_t i = 0, arity = node->arity(); i < arity; ++i)
  {
    const BitVectorNode* child                  = n->child(i);
    const std::unordered_set<uint64_t>& parents = d_parents.at(child->id());
    for (uint64_t pid : parents)
    {
      BitVectorNode* p = get_node(pid);
      if (!is_ineq_root(p)) continue;
      if (p->assignment().is_true() != d_roots_ineq.at(p)) continue;
      if (p->kind() == NodeKind::BV_NOT)
      {
        p = p->child(0);
      }

      update_bounds_aux(
          p, child == p->child(0) ? (child == p->child(1) ? -1 : 0) : 1);
    }
  }
}

std::vector<std::pair<uint64_t, uint64_t>>
LocalSearchBV::split_indices(BitVectorNode* node)
{
  std::unordered_set<std::pair<uint64_t, uint64_t>> slices{
      {node->size() - 1, 0}};

  const auto& extracts = node->get_extracts();
  if (extracts.size() < 2)
  {
    return {};
  }

  for (BitVectorExtract* ex : extracts)
  {
    slices.insert({ex->hi(), ex->lo()});
  }

  bool restart = false;
  do
  {
    for (auto slice : slices)
    {
      restart       = false;
      auto [hi, lo] = slice;
      for (auto s : slices)
      {
        if (s == slice) continue;

        auto [h, l] = s;
        // not overlapping?
        if (lo > h || hi < l || l > hi || h < lo)
        {
          continue;
        }
        // overlapping
        if (hi == h)
        {
          uint64_t max = std::max(lo, l);
          uint64_t min = std::min(lo, l);
          if (min == lo)
          {
            slices.erase(slice);
          }
          else
          {
            slices.erase(s);
          }
          slices.insert({max - 1, min});
          restart = true;
          break;
        }
        else if (lo == l)
        {
          uint64_t max = std::max(hi, h);
          uint64_t min = std::min(hi, h);
          if (max == hi)
          {
            slices.erase(slice);
          }
          else
          {
            slices.erase(s);
          }
          slices.insert({max, min + 1});
          restart = true;
          break;
        }
        else
        {
          std::vector<uint64_t> idxs = {hi, lo, h, l};
          std::sort(idxs.begin(), idxs.end());
          // we have to copy s to ensure that we erase the expected element
          // after slice has been erased (both are references)
          std::pair<uint64_t, uint64_t> tmp = s;
          slices.erase(slice);
          slices.erase(tmp);
          slices.insert({idxs[3], idxs[2] + 1});
          slices.insert({idxs[2], idxs[1]});
          slices.insert({idxs[1] - 1, idxs[0]});
          restart = true;
          break;
        }
      }
      if (restart) break;
    }
  } while (restart);

  std::vector<std::pair<uint64_t, uint64_t>> sorted{slices.begin(),
                                                    slices.end()};
  std::sort(sorted.begin(), sorted.end());
  return sorted;
}

BitVectorNode*
LocalSearchBV::mk_normalized_extract(BitVectorNode* child,
                                     uint64_t hi,
                                     uint64_t lo)
{
  assert(child);
  return get_node(_mk_node(NodeKind::BV_EXTRACT,
                           child->domain().bvextract(hi, lo),
                           {child->id()},
                           {hi, lo},
                           false));
}

BitVectorNode*
LocalSearchBV::mk_normalized_concat(BitVectorNode* child0,
                                    BitVectorNode* child1)
{
  assert(child0);
  assert(child1);
  return get_node(mk_node(NodeKind::BV_CONCAT,
                          child0->domain().bvconcat(child1->domain()),
                          {child0->id(), child1->id()}));
}

void
LocalSearchBV::normalize_extracts(BitVectorNode* node)
{
  const auto& extracts = node->get_extracts();
  if (extracts.size() < 2) return;

  std::vector<std::pair<uint64_t, uint64_t>> sorted_idxs = split_indices(node);

  for (BitVectorExtract* ex : extracts)
  {
    if (ex->is_normalized()) continue;

    uint64_t hi               = ex->hi();
    uint64_t lo               = ex->lo();
    BitVectorNode* normalized = nullptr;
    for (auto rit = sorted_idxs.rbegin(); rit != sorted_idxs.rend(); ++rit)
    {
      if (rit->first == hi)
      {
        assert(!normalized);
        if (rit->second == lo)
        {
          break;
        }
        normalized = mk_normalized_extract(node, rit->first, rit->second);
      }
      else if (rit->first < hi)
      {
        normalized = mk_normalized_concat(
            normalized, mk_normalized_extract(node, rit->first, rit->second));
        if (rit->second == lo)
        {
          break;
        }
      }
    }
    if (normalized)
    {
      uint64_t id = normalized->id();
      assert(d_parents[id].empty());
      // The normalized node is uniquely created for each normalized child1
      // of an extract, thus only that extract is its parent.
      d_parents[id] = {ex->id()};
      // Remove this extract from the parents list of the normalized child
      assert(!d_parents[ex->child(0)->id()].empty());
      d_parents[ex->child(0)->id()].erase(ex->id());
      ex->normalize(normalized);
    }
  }
}

void
LocalSearchBV::normalize()
{
  for (auto& node : d_to_normalize_nodes)
  {
    normalize_extracts(node);
  }
  normalize_ids();
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::ls
