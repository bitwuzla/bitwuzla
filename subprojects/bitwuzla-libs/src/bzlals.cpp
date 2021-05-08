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

BzlaLs::BzlaLs(uint64_t max_nprops) : d_max_nprops(max_nprops)
{
  d_one = BitVector::mk_one(1);
}

void
BzlaLs::register_root(BitVectorNode* root)
{
  d_roots.push_back(root);
}

void
BzlaLs::init_parents()
{
  /* map nodes to their parents */
  std::vector<BitVectorNode*> to_visit = d_roots;
  while (!to_visit.empty())
  {
    BitVectorNode* cur = to_visit.back();
    to_visit.pop_back();
    if (d_parents.find(cur) == d_parents.end())
    {
      d_parents[cur] = {};
    }
    for (uint32_t i = 0; i < cur->arity(); ++i)
    {
      BitVectorNode* child = (*cur)[i];
      if (d_parents.find(child) == d_parents.end())
      {
        d_parents[child] = {};
      }
      if (d_parents.at(child).find(cur) == d_parents.at(child).end())
      {
        d_parents.at(child).insert(cur);
      }
      to_visit.push_back(child);
    }
  }
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
