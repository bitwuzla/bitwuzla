#include "bzlals.h"

#include <cassert>
#include <iostream>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "log.h"
#include "rng.h"

#define BZLALS_PROB_USE_INV_VALUE 990

namespace bzlals {

BzlaLsMove
bzlals_select_move(RNG* rng, BitVectorOp* root, const BitVector& t_root)
{
  uint64_t nprops  = 0;
  BitVectorOp* cur = root;
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

      if (rng->pick_with_prob(BZLALS_PROB_USE_INV_VALUE)
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
