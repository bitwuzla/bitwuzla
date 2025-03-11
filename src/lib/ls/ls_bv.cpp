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
#include "bv/domain/bitvector_domain.h"
#include "ls/bv/bitvector_node.h"
#include "ls/internal.h"

namespace bzla::ls {

/* LocalSearchBv public ----------------------------------------------------- */

LocalSearchBV::LocalSearchBV(uint64_t max_nprops,
                             uint64_t max_nupdates,
                             uint32_t seed,
                             uint32_t log_level,
                             uint32_t verbosity_level,
                             const std::string& stats_prefix,
                             util::Statistics* statistics)
    : LocalSearch<BitVector>(max_nprops,
                             max_nupdates,
                             seed,
                             log_level,
                             verbosity_level,
                             stats_prefix,
                             "(lib::ls::bv)",
                             statistics)

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
  return _mk_node(kind, size, children, indices, symbol);
}

uint64_t
LocalSearchBV::mk_node(NodeKind kind,
                       const BitVectorDomain& domain,
                       const std::vector<uint64_t>& children,
                       const std::vector<uint64_t>& indices,
                       const std::optional<std::string>& symbol)
{
  return _mk_node(kind, domain, children, indices, symbol);
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
                        const std::optional<std::string>& symbol)
{
  return _mk_node(kind, BitVectorDomain(size), children, indices, symbol);
}

uint64_t
LocalSearchBV::_mk_node(NodeKind kind,
                        const BitVectorDomain& domain,
                        const std::vector<uint64_t>& children,
                        const std::vector<uint64_t>& indices,
                        const std::optional<std::string>& symbol)
{
  uint64_t id = d_nodes.size();
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
          d_rng.get(), domain, child0, indices[0], indices[1]));
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
      assert(is_signed
             || child0->bounds_u().d_min.compare(child0->bounds_u().d_max)
                    <= 0);
      assert(
          !is_signed
          || child0->bounds_s().d_min.signed_compare(child0->bounds_s().d_max)
                 <= 0);
    }

    // s < x
    if (!child1->all_value() && (pos < 0 || pos == 1))
    {
      assert((is_signed && child0->assignment().signed_compare(max_value) < 0)
             || (!is_signed && child0->assignment().compare(max_value) < 0));
      child1->update_bounds(
          child0->assignment(), max_value, true, false, is_signed);
      assert(is_signed
             || child1->bounds_u().d_min.compare(child1->bounds_u().d_max)
                    <= 0);
      assert(
          !is_signed
          || child1->bounds_s().d_min.signed_compare(child1->bounds_s().d_max)
                 <= 0);
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
      assert(is_signed
             || child0->bounds_u().d_min.compare(child0->bounds_u().d_max)
                    <= 0);
      assert(
          !is_signed
          || child0->bounds_s().d_min.signed_compare(child0->bounds_s().d_max)
                 <= 0);
    }

    // s >= x
    if (!child1->all_value() && (pos < 0 || pos == 1))
    {
      assert((is_signed && min_value.signed_compare(child0->assignment()) <= 0)
             || (!is_signed && min_value.compare(child0->assignment()) <= 0));
      child1->update_bounds(
          min_value, child0->assignment(), false, false, is_signed);
      assert(is_signed
             || child1->bounds_u().d_min.compare(child1->bounds_u().d_max)
                    <= 0);
      assert(
          !is_signed
          || child1->bounds_s().d_min.signed_compare(child1->bounds_s().d_max)
                 <= 0);
    }
  }
}

void
LocalSearchBV::compute_bounds(Node<BitVector>* node)
{
#ifndef NDEBUG
  StatisticsInternal& stats = d_internal->d_stats;
#endif
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
#ifndef NDEBUG
      if (p->is_inequality())
      {
        if (p->kind() == NodeKind::BV_SLT)
        {
          stats.num_sineq_parents_per_kind << child->kind();
        }
        else
        {
          assert(p->kind() == NodeKind::BV_ULT);
          stats.num_uineq_parents_per_kind << child->kind();
        }
      }
#endif
      if (!is_ineq_root(p)) continue;
      if (p->assignment().is_true() != d_roots_ineq.at(p)) continue;
#ifndef NDEBUG
      if (p->kind() == NodeKind::BV_SLT)
      {
        stats.num_sbounds_per_kind << child->kind();
      }
      else
      {
        assert(p->kind() == NodeKind::BV_ULT);
        stats.num_ubounds_per_kind << child->kind();
      }
#endif
      update_bounds_aux(
          p, child == p->child(0) ? (child == p->child(1) ? -1 : 0) : 1);
    }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::ls
