#include "bitvector_op.h"

#include <cassert>

#include "gmpmpz.h"

namespace bzlals {

BitVectorOp*&
BitVectorOp::operator[](uint32_t pos) const
{
  assert(pos <= get_arity());
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
  (void) t;
  (void) pos_x;
  return true;
}

}  // namespace bzlals
