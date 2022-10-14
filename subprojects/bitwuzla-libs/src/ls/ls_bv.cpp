#include "ls/ls_bv.h"

#include <cassert>

#include "bv/bitvector.h"
#include "ls/bv/bitvector_domain.h"
#include "ls/bv/bitvector_node.h"

namespace bzla::ls {

LocalSearchBV::LocalSearchBV(uint64_t max_nprops,
                             uint64_t max_nupdates,
                             uint32_t seed)
    : LocalSearch<BitVector, BitVectorNode>(max_nprops, max_nupdates, seed)

{
  d_true.reset(new BitVector(BitVector::mk_true()));
}

uint64_t
LocalSearchBV::mk_node(uint64_t size)
{
  return mk_node(BitVector::mk_zero(size), BitVectorDomain(size));
}

uint64_t
LocalSearchBV::mk_node(NodeKind kind,
                       uint64_t size,
                       const std::vector<uint64_t>& children)
{
  return mk_node(kind, BitVectorDomain(size), children);
}

uint64_t
LocalSearchBV::mk_indexed_node(NodeKind kind,
                               uint64_t size,
                               uint64_t child0,
                               const std::vector<uint64_t>& indices)
{
  return mk_indexed_node(kind, BitVectorDomain(size), child0, indices);
}

uint64_t
LocalSearchBV::mk_node(const BitVector& assignment,
                       const BitVectorDomain& domain)
{
  uint64_t id = d_nodes.size();
  assert(assignment.size() == domain.size());  // API check
  std::unique_ptr<BitVectorNode> res(
      new BitVectorNode(d_rng.get(), assignment, domain));
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

uint64_t
LocalSearchBV::mk_node(NodeKind kind,
                       const BitVectorDomain& domain,
                       const std::vector<uint64_t>& children)
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
    case NodeKind::EQ:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorEq(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::ITE:
      assert(children.size() == 3);  // API check
      res.reset(new BitVectorIte(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 get_node(children[2])));
      break;
    case NodeKind::BV_ADD:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAdd(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;

    case NodeKind::AND:
    case NodeKind::BV_AND:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAnd(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_ASHR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAshr(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_CONCAT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorConcat(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_MUL:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorMul(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::NOT:
    case NodeKind::BV_NOT:
      assert(children.size() == 1);  // API check
      res.reset(new BitVectorNot(d_rng.get(), domain, get_node(children[0])));
      break;
    case NodeKind::BV_SHL:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorShl(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_SHR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorShr(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_SLT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorSlt(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 d_options.use_opt_lt_concat_sext));
      break;
    case NodeKind::BV_UDIV:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUdiv(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::BV_ULT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUlt(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 d_options.use_opt_lt_concat_sext));
      break;
    case NodeKind::BV_UREM:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUrem(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case NodeKind::XOR:
    case NodeKind::BV_XOR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorXor(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;

    default: assert(0);  // API check
  }
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};

  return id;
}

uint64_t
LocalSearchBV::mk_indexed_node(NodeKind kind,
                               const BitVectorDomain& domain,
                               uint64_t child0,
                               const std::vector<uint64_t>& indices)
{
  // API check
  assert(kind == NodeKind::BV_EXTRACT || kind == NodeKind::BV_SEXT);
  // API check
  assert(kind != NodeKind::BV_EXTRACT || indices.size() == 2);
  // API check
  assert(kind != NodeKind::BV_EXTRACT || indices[0] >= indices[1]);
  // API check
  assert(kind != NodeKind::BV_EXTRACT || indices[0] < get_node(child0)->size());
  // API check
  assert(kind != NodeKind::BV_SEXT || indices.size() == 1);

  uint64_t id = d_nodes.size();
  assert(child0 < id);

  assert(d_parents.find(child0) != d_parents.end());
  d_parents.at(child0).insert(id);

  std::unique_ptr<BitVectorNode> res;
  if (kind == NodeKind::BV_EXTRACT)
  {
    res.reset(new BitVectorExtract(
        d_rng.get(), domain, get_node(child0), indices[0], indices[1]));
  }
  else
  {
    res.reset(new BitVectorSignExtend(
        d_rng.get(), domain, get_node(child0), indices[0]));
  }
  res->set_id(id);
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

void
LocalSearchBV::update_bounds_aux(BitVectorNode* root, int32_t pos)
{
  assert(root->is_inequality());
  assert(root->arity() == 2);

  BitVectorNode* child0 = (*root)[0];
  BitVectorNode* child1 = (*root)[1];
  bool is_signed        = root->get_kind() == NodeKind::BV_SLT;
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
    if (!child0->all_const() && (pos < 0 || pos == 0))
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
    if (!child1->all_const() && (pos < 0 || pos == 1))
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
    if (!child0->all_const() && (pos < 0 || pos == 0))
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
    if (!child1->all_const() && (pos < 0 || pos == 1))
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
LocalSearchBV::compute_bounds(BitVectorNode* node)
{
  for (uint32_t i = 0, arity = node->arity(); i < arity; ++i)
  {
    (*node)[i]->reset_bounds();
  }
  for (uint32_t i = 0, arity = node->arity(); i < arity; ++i)
  {
    const BitVectorNode* child                  = (*node)[i];
    const std::unordered_set<uint64_t>& parents = d_parents.at(child->id());
    for (uint64_t pid : parents)
    {
      BitVectorNode* p = get_node(pid);
      if (!is_ineq_root(p)) continue;
      if (p->assignment().is_true() != d_roots_ineq.at(p)) continue;
      if (p->get_kind() == NodeKind::BV_NOT)
      {
        p = (*p)[0];
      }

      update_bounds_aux(p, child == (*p)[0] ? (child == (*p)[1] ? -1 : 0) : 1);
    }
  }
}

}  // namespace bzla::ls
