#include "bzlals.h"

#include <cassert>
#include <iostream>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "log.h"
#include "rng.h"

#define BZLALS_PROB_USE_INV_VALUE 990

namespace bzlals {

struct BzlaLsMove
{
  BzlaLsMove() : d_nprops(0), d_input(nullptr) {}

  BzlaLsMove(uint64_t nprops, BitVectorNode* input, BitVector assignment)
      : d_nprops(nprops), d_input(input), d_assignment(assignment)
  {
  }

  uint64_t d_nprops;
  BitVectorNode* d_input;
  BitVector d_assignment;
};

BzlaLs::BzlaLs(uint64_t max_nprops, uint32_t seed)
    : d_max_nprops(max_nprops), d_seed(seed)
{
  d_rng.reset(new RNG(d_seed));
  d_one = BitVector::mk_one(1);
}

uint32_t
BzlaLs::mk_node(NodeKind kind,
                uint32_t size,
                const std::vector<uint32_t>& children)
{
  return mk_node(
      kind, BitVector::mk_zero(size), BitVectorDomain(size), children);
}

uint32_t
BzlaLs::mk_indexed_node(NodeKind kind,
                        uint32_t size,
                        uint32_t child0,
                        const std::vector<uint32_t>& indices)
{
  return mk_indexed_node(
      kind, BitVector::mk_zero(size), BitVectorDomain(size), child0, indices);
}

uint32_t
BzlaLs::mk_node(NodeKind kind,
                const BitVector& assignment,
                const BitVectorDomain& domain,
                const std::vector<uint32_t>& children)
{
  assert(assignment.size() == domain.size());
  uint32_t id = d_nodes.size();

  for (uint32_t c : children)
  {
    assert(c < id);
    assert(d_parents.find(c) != d_parents.end());
    assert(d_parents.at(c).find(id) == d_parents.at(c).end());
    d_parents.at(c).insert(id);
  }

  std::unique_ptr<BitVectorNode> res;
  switch (kind)
  {
    case ADD:
      assert(children.size() == 2);
      res.reset(new BitVectorAdd(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;

    case AND:
      assert(children.size() == 2);
      res.reset(new BitVectorAnd(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case ASHR:
      assert(children.size() == 2);
      res.reset(new BitVectorAshr(d_rng.get(),
                                  assignment,
                                  domain,
                                  d_nodes[children[0]].get(),
                                  d_nodes[children[1]].get()));
      break;
    case CONCAT:
      assert(children.size() == 2);
      res.reset(new BitVectorConcat(d_rng.get(),
                                    assignment,
                                    domain,
                                    d_nodes[children[0]].get(),
                                    d_nodes[children[1]].get()));
      break;
    case EQ:
      assert(children.size() == 2);
      res.reset(new BitVectorEq(d_rng.get(),
                                assignment,
                                domain,
                                d_nodes[children[0]].get(),
                                d_nodes[children[1]].get()));
      break;
    case ITE:
      assert(children.size() == 3);
      res.reset(new BitVectorIte(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get(),
                                 d_nodes[children[2]].get()));
      break;
    case MUL:
      assert(children.size() == 2);
      res.reset(new BitVectorMul(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case NOT:
      assert(children.size() == 1);
      d_nodes.push_back(std::make_unique<BitVectorNot>(
          d_rng.get(), assignment, domain, d_nodes[children[0]].get()));
      break;
    case SHL:
      assert(children.size() == 2);
      res.reset(new BitVectorShl(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case SHR:
      assert(children.size() == 2);
      res.reset(new BitVectorShr(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case SLT:
      assert(children.size() == 2);
      res.reset(new BitVectorSlt(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case UDIV:
      assert(children.size() == 2);
      res.reset(new BitVectorUdiv(d_rng.get(),
                                  assignment,
                                  domain,
                                  d_nodes[children[0]].get(),
                                  d_nodes[children[1]].get()));
      break;
    case ULT:
      assert(children.size() == 2);
      res.reset(new BitVectorSlt(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;
    case UREM:
      assert(children.size() == 2);
      res.reset(new BitVectorUrem(d_rng.get(),
                                  assignment,
                                  domain,
                                  d_nodes[children[0]].get(),
                                  d_nodes[children[1]].get()));
      break;
    case XOR:
      assert(children.size() == 2);
      res.reset(new BitVectorXor(d_rng.get(),
                                 assignment,
                                 domain,
                                 d_nodes[children[0]].get(),
                                 d_nodes[children[1]].get()));
      break;

    default:
      assert(kind == CONST);
      assert(children.empty());
      res.reset(new BitVectorNode(d_rng.get(), assignment, domain));
  }
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(d_nodes[id] == d_nodes.back());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

uint32_t
BzlaLs::mk_indexed_node(NodeKind kind,
                        const BitVector& assignment,
                        const BitVectorDomain& domain,
                        uint32_t child0,
                        const std::vector<uint32_t>& indices)
{
  assert(kind == EXTRACT || kind == SEXT);
  assert(assignment.size() == domain.size());
  assert(kind != EXTRACT || indices.size() == 2);
  assert(kind != EXTRACT || indices[0] >= indices[1]);
  assert(kind != EXTRACT || indices[0] < assignment.size());
  assert(kind != SEXT || indices.size() == 1);

  uint32_t id = d_nodes.size();
  assert(child0 < id);

  assert(d_parents.find(child0) != d_parents.end());
  assert(d_parents.at(child0).find(id) == d_parents.at(child0).end());
  d_parents.at(child0).insert(id);

  std::unique_ptr<BitVectorNode> res;
  if (kind == EXTRACT)
  {
    res.reset(new BitVectorExtract(d_rng.get(),
                                   assignment,
                                   domain,
                                   d_nodes[child0].get(),
                                   indices[0],
                                   indices[1]));
  }
  else
  {
    res.reset(new BitVectorSignExtend(
        d_rng.get(), assignment, domain, d_nodes[child0].get(), indices[0]));
  }
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

void
BzlaLs::register_root(uint32_t root)
{
  d_roots.push_back(root);
}

BzlaLsMove
BzlaLs::select_move(BitVectorNode* root, const BitVector& t_root)
{
  uint64_t nprops  = 0;
  BitVectorNode* cur = root;
  BitVector t      = t_root;
  BitVector t_new;

  for (;;)
  {
    uint32_t arity = cur->arity();

    if (arity == 0)
    {
      return BzlaLsMove(nprops, cur, t);
    }
    else if (cur->is_const() || cur->all_const())
    {
      break;
    }
    else
    {
      assert(!cur->domain().is_fixed());

      BZLALSLOG << "propagate: " << t << std::endl;

      /* Select path */
      uint32_t pos_x = cur->select_path(t);
      assert(pos_x < arity);

      /** Select value
       *
       * 1) randomly choose to compute inverse over consistent value
       *    with probability BZLALS_PROB_USE_INV_VALUE
       * 2) if inverse value selected and no inverse value exists,
       *    fall back to consistent value
       * 3) if consistent value selected and no consistent value exists,
       *    conflict
       */

      if (d_rng->pick_with_prob(BZLALS_PROB_USE_INV_VALUE)
          && cur->is_invertible(t, pos_x))
      {
        t = cur->inverse_value(t, pos_x);
        BZLALSLOG << "inverse value: " << t_new << std::endl;
      }
      else if (cur->is_consistent(t, pos_x))
      {
        t = cur->consistent_value(t, pos_x);
        BZLALSLOG << "consistent value: " << t_new << std::endl;
      }
      else
      {
        break;
      }

      // TODO skip when no progress?

      /* Propagate down */
      cur = (*cur)[pos_x];
      nprops += 1;
    }
  }
  /* Conflict case */
  return BzlaLsMove(nprops, root, BitVector());
}
}  // namespace bzlals
