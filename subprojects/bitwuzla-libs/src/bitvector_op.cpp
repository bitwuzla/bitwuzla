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
    BitVector sub            = t.bvsub(s);
    if (x.match_fixed_bits(sub))
    {
      d_inverse.reset(new BitVector(sub));
      return true;
    }
    return false;
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
    if (x.is_fixed())
    {
      if (x.lo().bvand(s).compare(t) == 0)
      {
        d_inverse.reset(new BitVector(x.lo()));
        return true;
      }
      return false;
    }
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
    if (x.match_fixed_bits(tx))
    {
      d_inverse.reset(new BitVector(tx));
      return true;
    }
    return false;
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
    if (x.is_fixed())
    {
      if (x.lo().bveq(s).compare(t) == 0)
      {
        d_inverse.reset(new BitVector(x.lo()));
        return true;
      }
      return false;
    }
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

BitVectorMul::BitVectorMul(uint32_t size) : BitVectorOp(size) {}

BitVectorMul::BitVectorMul(const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(assignment, domain)
{
}

bool
BitVectorMul::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  bool check = s.bvneg().bvor(s).bvand(t).compare(t) == 0;

  if (check && d_children[pos_x]->domain().has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bvmul(s).compare(t) == 0)
      {
        d_inverse.reset(new BitVectorDomain(x));
        return true;
      }
      return false;
    }

    /* IC: (((-s | s) & t) = t) &&
     *     (s = 0 || ((odd(s) => mfb(x, t * s^-1)) &&
     *               (!odd(s) => mfb (x << c, y << c))))
     *     with c = ctz(s) and y = (t >> c) * (s >> c)^-1 */
    if (!s.is_zero())
    {
      /** s odd */
      if (s.get_lsb())
      {
        BitVector inv = s.bvmodinv().bvmul(t);
        if (x.match_fixed_bits(inv))
        {
          d_inverse.reset(new BitVectorDomain(inv));
          return true;
        }
        return false;
      }

      /** s even */
      /* Check if relevant bits of
       *   y = (t >> ctz(s)) * (s >> ctz(s))^-1
       * match corresponding constant bits of x, i.e.,
       * mfb(x[bw - ctz(s) - 1:0], y[bw - ctz(s) - 1:0]). */
      uint32_t bw             = x.size();
      uint32_t ctz            = s.count_trailing_zeros();
      BitVectorDomain x_prime = x.bvextract(bw - ctz - 1, 0);
      BitVector y             = t.bvshr(ctz).bvmul(s.bvshr(ctz).bvmodinv());
      BitVector y_ext         = y.bvextract(bw - ctz - 1, 0);
      if (x_prime.match_fixed_bits(y_ext))
      {
        /* Result domain is x[bw - 1:ctz(s)] o y[bw - ctz(s) - 1:0] */
        d_inverse.reset(
            new BitVectorDomain(x.lo().bvextract(bw - 1, ctz).bvconcat(y),
                                x.hi().bvextract(bw - 1, ctz).bvconcat(y)));
        return true;
      }
      return false;
    }
    return true;
  }
  /* IC: ((-s | s) & t) = t */
  return check;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzlals
