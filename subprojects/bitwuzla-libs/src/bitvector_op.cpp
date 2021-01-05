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

BitVectorConcat::BitVectorConcat(uint32_t size) : BitVectorOp(size) {}

BitVectorConcat::BitVectorConcat(const BitVector& assignment,
                                 const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
}

bool
BitVectorConcat::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector tx;
  bool check;

  uint32_t bw_t = t.size();
  uint32_t bw_s = s.size();

  if (pos_x == 0)
  {
    check = t.bvextract(bw_s - 1, 0).compare(s) == 0;
    tx    = t.bvextract(bw_t - 1, bw_s);
  }
  else
  {
    check = t.bvextract(bw_t - 1, bw_t - bw_s).compare(s) == 0;
    tx    = t.bvextract(bw_t - bw_s - 1, 0);
  }

  if (check && d_children[pos_x]->domain().has_fixed_bits())
  {
    /* IC: s = ts && mfb(x, tx) */
    return x.match_fixed_bits(tx);
  }
  /* IC: s = ts
   *   pos_x = 0: ts = t[bw(s) - 1 : 0]
   *   pos_x = 1: ts = t[bw(t) - 1 : bw(t) - bw(s)] */
  return check;
}

/* -------------------------------------------------------------------------- */

BitVectorEq::BitVectorEq(uint32_t size) : BitVectorOp(size) {}

BitVectorEq::BitVectorEq(const BitVector& assignment,
                         const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
}

bool
BitVectorEq::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  if (d_children[pos_x]->domain().has_fixed_bits())
  {
    /* IC: t = 0: (hi_x != lo_x) || (hi_x != s)
     *     t = 1: mfb(x, s) */
    if (t.is_false())
    {
      return x.hi().compare(x.lo()) || x.hi().compare(s);
    }
    return x.match_fixed_bits(s);
  }
  /* IC: true */
  return true;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzlals
