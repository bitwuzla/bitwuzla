#include "bitvector_op.h"

#include <cassert>

#include "gmpmpz.h"

namespace bzlals {

/* -------------------------------------------------------------------------- */

BitVectorOp::BitVectorOp(RNG* rng, uint32_t size)
    : d_rng(rng),
      d_assignment(BitVector::mk_zero(size)),
      d_domain(BitVectorDomain(size))
{
  assert(rng);
  d_children.reset(new BitVectorOp*[arity()]);
}

BitVectorOp::BitVectorOp(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain)
    : d_rng(rng), d_assignment(assignment), d_domain(domain)
{
  assert(rng);
  d_children.reset(new BitVectorOp*[arity()]);
}

BitVectorOp*&
BitVectorOp::operator[](uint32_t pos) const
{
  assert(pos <= arity());
  assert(d_children);
  return d_children[pos];
}

/* -------------------------------------------------------------------------- */

BitVectorAdd::BitVectorAdd(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorAdd::BitVectorAdd(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
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

BitVectorAnd::BitVectorAnd(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorAnd::BitVectorAnd(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorAnd::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  bool check = t.bvand(s).compare(t) == 0;

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bvand(s).compare(t) == 0)
      {
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

BitVectorConcat::BitVectorConcat(RNG* rng, uint32_t size)
    : BitVectorOp(rng, size)
{
}

BitVectorConcat::BitVectorConcat(RNG* rng,
                                 const BitVector& assignment,
                                 const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
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

  if (check && x.has_fixed_bits())
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

BitVectorEq::BitVectorEq(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorEq::BitVectorEq(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorEq::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  if (x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bveq(s).compare(t) == 0)
      {
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

BitVectorMul::BitVectorMul(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorMul::BitVectorMul(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorMul::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  bool check = s.bvneg().bvor(s).bvand(t).compare(t) == 0;

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bvmul(s).compare(t) == 0)
      {
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

BitVectorShl::BitVectorShl(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorShl::BitVectorShl(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorShl::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  uint32_t ctz_t           = 0;
  uint32_t ctz_s           = 0;
  bool check;

  if (pos_x == 0)
  {
    check = t.bvshr(s).bvshl(s).compare(t) == 0;
  }
  else
  {
    ctz_t = t.count_trailing_zeros();
    ctz_s = s.count_trailing_zeros();
    check = ctz_s <= ctz_t
            && (t.is_zero() || s.bvshl(ctz_t - ctz_s).compare(t) == 0);
  }

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if ((pos_x == 0 && x.lo().bvshl(s).compare(t) == 0)
          || (pos_x == 1 && s.bvshl(x.lo()).compare(t) == 0))
      {
        return true;
      }
      return false;
    }
    /* IC: pos_x = 0: IC_wo && mfb(x << s, t)
     *     pos_x = 1: IC_wo &&
     *                ((t = 0) => (hi_x >= ctz(t) - ctz(s) || (s = 0))) &&
     *                ((t != 0) => mfb(x, ctz(t) - ctz(s))) */
    if (pos_x == 0)
    {
      // TODO can't we reuse x.bvshl(s)? domain gen -> select random value
      // for value computation
      return x.bvshl(s).match_fixed_bits(t);
    }
    if (t.is_zero())
    {
      uint32_t bw    = x.size();
      bool s_is_zero = s.is_zero();
      BitVector min  = BitVector(bw, ctz_t - ctz_s);
      if (s_is_zero || x.hi().compare(min) >= 0)
      {
        BitVectorDomainGenerator gen(
            x, d_rng, s_is_zero ? x.lo() : min, x.hi());
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
        return true;
      }
      return false;
    }
    return x.match_fixed_bits(BitVector(x.size(), ctz_t - ctz_s));
  }
  /* IC_wo: pos_x = 0: (t >> s) << s = t
   *        pos_x = 1: ctz(s) <= ctz(t) &&
   *                   ((t = 0) || (s << (ctz(t) - ctz(s))) = t) */
  return check;
}

/* -------------------------------------------------------------------------- */

BitVectorShr::BitVectorShr(RNG* rng, uint32_t size) : BitVectorOp(rng, size) {}

BitVectorShr::BitVectorShr(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorShr::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  return is_invertible(d_rng, t, s, x, pos_x, d_inverse);
}

bool
BitVectorShr::is_invertible(RNG* rng,
                            const BitVector& t,
                            const BitVector& s,
                            const BitVectorDomain& x,
                            uint32_t pos_x,
                            std::unique_ptr<BitVector>& inverse)
{
  uint32_t clz_t = 0;
  uint32_t clz_s = 0;
  bool check;

  if (pos_x == 0)
  {
    check = t.bvshl(s).bvshr(s).compare(t) == 0;
  }
  else
  {
    clz_t = t.count_leading_zeros();
    clz_s = s.count_leading_zeros();
    check = clz_s <= clz_t
            && (t.is_zero() || s.bvshr(clz_t - clz_s).compare(t) == 0);
  }

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if ((pos_x == 0 && x.lo().bvshr(s).compare(t) == 0)
          || (pos_x == 1 && s.bvshr(x.lo()).compare(t) == 0))
      {
        return true;
      }
      return false;
    }
    /* IC: pos_x = 0: IC_wo && mfb(x >> s, t)
     *     pos_x = 1: IC_wo &&
     *                ((t = 0) => (hi_x >= clz(t) - clz(s) || (s = 0))) &&
     *                ((t != 0) => mfb(x, clz(t) - clz(s))) */
    if (pos_x == 0)
    {
      // TODO can't we reuse x.bvshr(s)? domain gen -> select random value
      // for value computation
      return x.bvshr(s).match_fixed_bits(t);
    }
    if (t.is_zero())
    {
      uint32_t bw    = x.size();
      bool s_is_zero = s.is_zero();
      BitVector min  = BitVector(bw, clz_t - clz_s);
      if (s_is_zero || x.hi().compare(min) >= 0)
      {
        BitVectorDomainGenerator gen(x, rng, s_is_zero ? x.lo() : min, x.hi());
        assert(gen.has_random());
        inverse.reset(new BitVector(gen.random()));
        return true;
      }
      return false;
    }
    return x.match_fixed_bits(BitVector(x.size(), clz_t - clz_s));
  }
  /* IC_wo: pos_x = 0: (t << s) >> s = t
   *        pos_x = 1: clz(s) <= clz(t) &&
   *                   ((t = 0) || (s >> (clz(t) - clz(s))) = t) */
  return check;
}

/* -------------------------------------------------------------------------- */

BitVectorAshr::BitVectorAshr(RNG* rng, uint32_t size) : BitVectorOp(rng, size)
{
}

BitVectorAshr::BitVectorAshr(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorAshr::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector snot, tnot, sshr;
  bool check;

  /* IC:
   * w/o const bits (IC_wo):
   *     pos_x = 0: (s < bw(s) => (t << s) >>a s = t) &&
   *                (s >= bw(s) => (t = ones || t = 0))
   *     pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
   *                (s[msb] = 1 => IC_shr(~s >> x = ~t)
   *
   * with const bits:
   *     pos_x = 0: IC_wo && mfb(x >>a s, t)
   *     pos_x = 1: IC_wo &&
   *                (s[msb ] = 0 => IC_shr) &&
   *                (s[msb] = 1 => IC_shr(~s >> x = ~t))
   */
  if (pos_x == 1)
  {
    if (s.get_msb())
    {
      return BitVectorShr::is_invertible(
          d_rng, t.bvnot(), s.bvnot(), x, pos_x, d_inverse);
    }
    return BitVectorShr::is_invertible(d_rng, t, s, x, pos_x, d_inverse);
  }

  uint32_t bw = s.size();
  if (s.compare(BitVector(bw, bw)) < 0)
  {
    check = t.bvshl(s).bvashr(s).compare(t) == 0;
  }
  else
  {
    check = t.is_zero() || t.is_ones();
  }

  if (check && x.has_fixed_bits())
  {
    // TODO can't we reuse x.bvashr(s)? domain gen -> select random value
    // for value computation
    return x.bvashr(s).match_fixed_bits(t);
  }
  return check;
}

/* -------------------------------------------------------------------------- */

BitVectorUdiv::BitVectorUdiv(RNG* rng, uint32_t size) : BitVectorOp(rng, size)
{
}

BitVectorUdiv::BitVectorUdiv(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain)
    : BitVectorOp(rng, assignment, domain)
{
}

bool
BitVectorUdiv::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector s_mul_t, s_udiv_t;
  bool check;

  if (pos_x == 0)
  {
    s_mul_t = s.bvmul(t);
    check   = s_mul_t.bvudiv(s).compare(t) == 0;
  }
  else
  {
    s_udiv_t = s.bvudiv(t);
    check    = s.bvudiv(s_udiv_t).compare(t) == 0;
  }

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if ((pos_x == 0 && x.lo().bvudiv(s).compare(t) == 0)
          || (pos_x == 1 && s.bvudiv(x.lo()).compare(t) == 0))
      {
        return true;
      }
      return false;
    }

    /* IC: pos_x = 0: IC_wo &&
     *                (t = 0 => lo_x < s) &&
     *                ((t != 0 && s != 0 ) => \exists y. (
     *                    mfb(x, y) && (~c => y < s * t + 1) &&
     *                    (c => y <= ones)))
     *                with c = umulo(s, t + 1) && uaddo(t, 1)
     *     pos_x = 1: IC_wo &&
     *                (t != ones => hi_x > 0) &&   ... covered by is_fixed check
     *                ((s != 0 || t != 0) => (s / hi_x <= t) && \exists y. (
     *                    mfb(x, y) &&
     *                    (t = ones => y <= s / t) &&
     *                    (t != ones => y > t + 1 && y <= s / t)))
     */
    if (pos_x == 0)
    {
      if (t.is_zero())
      {
        return x.lo().compare(s) < 0;
      }
      else if (!s.is_zero())
      {
        BitVector& min = s_mul_t;
        BitVector max  = min.bvadd(s);
        if (max.compare(min) < 0)
        {
          max = BitVector::mk_ones(s.size());
        }
        else
        {
          max.ibvdec(max);
        }

        BitVectorDomainGenerator gen(x, d_rng, min, max);
        if (gen.has_next())
        {
          d_inverse.reset(new BitVectorDomain(gen.random(), max));
          return true;
        }
        return false;
      }
      return true;
    }
    else if (!s.is_zero() || !t.is_zero())
    {
      uint32_t bw = s.size();
      BitVector min, max;
      if (s.bvudiv(x.hi()).compare(t) > 0)
      {
        return false;
      }

      if (t.is_ones())
      {
        min = BitVector::mk_zero(bw);
        max = s.is_ones() ? BitVector::mk_one(bw) : min;
      }
      else if (s.compare(t) == 0)
      {
        min = BitVector::mk_one(bw);
        max = min;
      }
      else
      {
        min = t.bvinc();
        min.ibvudiv(s, min);
        min.ibvinc(min);
        max = s_udiv_t;
      }
      BitVectorDomainGenerator gen(x, d_rng, min, max);
      if (gen.has_next())
      {
        d_inverse.reset(new BitVectorDomain(gen.random(), max));
        return true;
      }
      return false;
    }
    return true;
  }
  /* IC_wo: pos_x = 0: (s * t) / s = t
   *        pos_x = 1: s / (s / t) = t  */
  return check;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzlals
