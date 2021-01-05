#include "bitvector_op.h"

#include <cassert>

#include "gmpmpz.h"

namespace bzlals {

BitVectorOp*&
BitVectorOp::operator[](uint32_t pos) const
{
  assert(pos <= arity());
  assert(d_children);
  return d_children[pos];
}

BitVectorAdd::BitVectorAdd(uint32_t size) : BitVectorOp(size)
{
  d_children.reset(new BitVectorOp*[2]);
}

BitVectorAdd::BitVectorAdd(const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
  d_children.reset(new BitVectorOp*[2]);
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

}  // namespace bzlals
