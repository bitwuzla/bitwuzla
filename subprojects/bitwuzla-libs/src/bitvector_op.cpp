#include "bitvector_op.h"

#include <cassert>

#include "gmpmpz.h"

namespace bzlals {

/* -------------------------------------------------------------------------- */

BitVectorOp*&
BitVectorOp::operator[](uint32_t pos) const
{
  assert(pos <= arity());
  assert(d_children);
  return d_children[pos];
}

/* -------------------------------------------------------------------------- */

BitVectorAdd::BitVectorAdd(uint32_t size) : BitVectorOp(size)
{
}

BitVectorAdd::BitVectorAdd(const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
}

bool
BitVectorAdd::is_invertible(const BitVector& t, uint32_t pos_x)
{
  if (d_children[pos_x]->domain().has_fixed_bits())
  {
    /* IC: mfb(x, t - s) */
    uint32_t pos_s           = 1 - pos_x;
    const BitVector& s       = d_children[pos_s]->assignment();
    const BitVectorDomain& x = d_children[pos_x]->domain();
    return x.match_fixed_bits(t.bvsub(s));
  }
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorAnd::BitVectorAnd(uint32_t size) : BitVectorOp(size) {}

BitVectorAnd::BitVectorAnd(const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
}

bool
BitVectorAnd::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  bool check = t.bvand(s).compare(t) == 0;
  if (check && d_children[pos_x]->domain().has_fixed_bits())
  {
    /* IC: (t & s) = t && ((s & hi_x) & m) = (t & m)
     *     with m = ~(lo_x ^ hi_x)  ... mask out all non-const bits */
    BitVector mask = x.lo().bvxnor(x.hi());
    return s.bvand(x.hi()).bvand(mask).compare(t.bvand(mask)) == 0;
  }
  /* IC: (t & s) = t */
  return check;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzlals
