#include "bitvector_op.h"

#include <cassert>
#include <iostream>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "rng.h"

namespace bzlals {

/* -------------------------------------------------------------------------- */

BitVectorOp::BitVectorOp(RNG* rng, uint32_t size, BitVectorOp* child0)
    : BitVectorOp(rng, BitVector::mk_zero(size), BitVectorDomain(size), child0)
{
}

BitVectorOp::BitVectorOp(RNG* rng,
                         uint32_t size,
                         BitVectorOp* child0,
                         BitVectorOp* child1)
    : BitVectorOp(
        rng, BitVector::mk_zero(size), BitVectorDomain(size), child0, child1)
{
}

BitVectorOp::BitVectorOp(RNG* rng,
                         uint32_t size,
                         BitVectorOp* child0,
                         BitVectorOp* child1,
                         BitVectorOp* child2)
    : BitVectorOp(rng,
                  BitVector::mk_zero(size),
                  BitVectorDomain(size),
                  child0,
                  child1,
                  child2)
{
}

BitVectorOp::BitVectorOp(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain,
                         BitVectorOp* child0)
    : d_rng(rng), d_arity(1), d_assignment(assignment), d_domain(domain)
{
  assert(rng);
  d_children.reset(new BitVectorOp*[d_arity]);
  d_children[0] = child0;
}

BitVectorOp::BitVectorOp(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain,
                         BitVectorOp* child0,
                         BitVectorOp* child1)
    : d_rng(rng), d_arity(2), d_assignment(assignment), d_domain(domain)
{
  assert(rng);
  d_children.reset(new BitVectorOp*[d_arity]);
  d_children[0] = child0;
  d_children[1] = child1;
}

BitVectorOp::BitVectorOp(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain,
                         BitVectorOp* child0,
                         BitVectorOp* child1,
                         BitVectorOp* child2)
    : d_rng(rng), d_arity(3), d_assignment(assignment), d_domain(domain)
{
  assert(rng);
  d_children.reset(new BitVectorOp*[d_arity]);
  d_children[0] = child0;
  d_children[1] = child1;
  d_children[2] = child2;
}

BitVectorOp*
BitVectorOp::operator[](uint32_t pos) const
{
  assert(pos <= arity());
  assert(d_children);
  return d_children[pos];
}

/* -------------------------------------------------------------------------- */

BitVectorAdd::BitVectorAdd(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorAdd::BitVectorAdd(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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

bool
BitVectorAdd::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorAnd::BitVectorAnd(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorAnd::BitVectorAnd(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    return s.bvand(x.hi()).ibvand(mask).compare(t.bvand(mask)) == 0;
  }
  /* IC: (t & s) = t */
  return check;
}

bool
BitVectorAnd::is_consistent(const BitVector& t, uint32_t pos_x)
{
  /* CC: t & hi_x = t */
  const BitVectorDomain& x = d_children[pos_x]->domain();
  return t.compare(t.bvand(x.hi())) == 0;
}

/* -------------------------------------------------------------------------- */

BitVectorConcat::BitVectorConcat(RNG* rng,
                                 uint32_t size,
                                 BitVectorOp* child0,
                                 BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorConcat::BitVectorConcat(RNG* rng,
                                 const BitVector& assignment,
                                 const BitVectorDomain& domain,
                                 BitVectorOp* child0,
                                 BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    assert(pos_x == 1);
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

bool
BitVectorConcat::is_consistent(const BitVector& t, uint32_t pos_x)
{
  /* CC: mfb(x, tx)
   * with pos_x = 0: tx = t[bw(t) - 1 : bw(t) - bw(x)]
   *      pos_x = 1: tx = t[bw(x) - 1 : 0] */
  const BitVectorDomain& x = d_children[pos_x]->domain();
  uint32_t bw_t            = t.size();
  uint32_t bw_x            = x.size();
  if (pos_x == 0)
  {
    return x.match_fixed_bits(t.bvextract(bw_t - 1, bw_t - bw_x));
  }
  return x.match_fixed_bits(t.bvextract(bw_x - 1, 0));
}

/* -------------------------------------------------------------------------- */

BitVectorEq::BitVectorEq(RNG* rng,
                         uint32_t size,
                         BitVectorOp* child0,
                         BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorEq::BitVectorEq(RNG* rng,
                         const BitVector& assignment,
                         const BitVectorDomain& domain,
                         BitVectorOp* child0,
                         BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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

bool
BitVectorEq::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  /* CC: true */
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorMul::BitVectorMul(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorMul::BitVectorMul(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
{
}

bool
BitVectorMul::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  bool check = s.bvneg().ibvor(s).ibvand(t).compare(t) == 0;

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
        BitVector inv = s.bvmodinv().ibvmul(t);
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
      BitVector y             = t.bvshr(ctz).ibvmul(s.bvshr(ctz).ibvmodinv());
      BitVector y_ext         = y.bvextract(bw - ctz - 1, 0);
      if (x_prime.match_fixed_bits(y_ext))
      {
        /* Result domain is x[bw - 1:ctz(s)] o y[bw - ctz(s) - 1:0] */
        d_inverse.reset(
            new BitVectorDomain(x.lo().bvextract(bw - 1, ctz).ibvconcat(y),
                                x.hi().bvextract(bw - 1, ctz).ibvconcat(y)));
        return true;
      }
      return false;
    }
    return true;
  }
  /* IC: ((-s | s) & t) = t */
  return check;
}

bool
BitVectorMul::is_consistent(const BitVector& t, uint32_t pos_x)
{
  /* CC: (t != 0 => xhi != 0) &&
   *     (odd(t) => xhi[lsb] != 0) &&
   *     (!odd(t) => \exists y. (mcb(x, y) && ctz(t) >= ctz(y)) */
  const BitVectorDomain& x = d_children[pos_x]->domain();

  if (x.hi().is_zero()) return t.is_zero();

  bool is_odd = t.get_lsb();
  if (is_odd && !x.hi().get_lsb()) return false;

  if (!is_odd && x.has_fixed_bits())
  {
    uint32_t size  = t.size();
    uint32_t ctz_t = t.count_trailing_zeros();
    BitVectorDomainGenerator gen(
        x,
        d_rng,
        t.is_zero() ? BitVector::mk_zero(size) : BitVector::mk_one(size),
        x.hi());
    assert(gen.has_random() || x.is_fixed());
    BitVector tmp = gen.has_random() ? gen.random() : x.lo();
    bool res      = false;
    for (uint32_t i = 0; i < size && i <= ctz_t; ++i)
    {
      if (!x.is_fixed_bit_false(i))
      {
        res = true;
        break;
      }
    }
    if (res)
    {
      if (ctz_t < size)
      {
        uint32_t i;
        do
        {
          i = d_rng->pick<uint32_t>(0, ctz_t);
        } while (x.is_fixed_bit_false(i));
        tmp.set_bit(i, true);
      }
      d_consistent.reset(new BitVector(tmp));
    }
    return res;
  }
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorShl::BitVectorShl(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorShl::BitVectorShl(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    check = t.bvshr(s).ibvshl(s).compare(t) == 0;
  }
  else
  {
    assert(pos_x == 1);
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

bool
BitVectorShl::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorShr::BitVectorShr(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorShr::BitVectorShr(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    check = t.bvshl(s).ibvshr(s).compare(t) == 0;
  }
  else
  {
    assert(pos_x == 1);
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

bool
BitVectorShr::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorAshr::BitVectorAshr(RNG* rng,
                             uint32_t size,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorAshr::BitVectorAshr(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    check = t.bvshl(s).ibvashr(s).compare(t) == 0;
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

bool
BitVectorAshr::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorUdiv::BitVectorUdiv(RNG* rng,
                             uint32_t size,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorUdiv::BitVectorUdiv(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
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
    assert(pos_x == 1);
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
          max.ibvdec();
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
        min.ibvudiv(s, min).ibvinc();
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

bool
BitVectorUdiv::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorUlt::BitVectorUlt(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorUlt::BitVectorUlt(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
{
}

bool
BitVectorUlt::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /* IC: pos_x = 0: t = 1 => (s != 0 && lo_x < s) && t = 0 => (hi_x >= s)
   *     pos_x = 1: t = 1 => (s != ones && hi_x > s) && t = 0 => (lo_x <= s) */
  if (x.has_fixed_bits())
  {
    if (pos_x == 0)
    {
      if (t.is_true())
      {
        return !s.is_zero() && x.lo().compare(s) < 0;
      }
      return x.hi().compare(s) >= 0;
    }
    assert(pos_x == 1);
    if (t.is_true())
    {
      return !s.is_ones() && x.hi().compare(s) > 0;
    }
    return x.lo().compare(s) <= 0;
  }

  /* IC_wo: pos_x = 0: t = 0 || s != 0
   *        pos_x = 1: t = 0 || s != ones */
  if (pos_x == 0)
  {
    return t.is_false() || !s.is_zero();
  }
  assert(pos_x == 1);
  return t.is_false() || !s.is_ones();
}

bool
BitVectorUlt::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorSlt::BitVectorSlt(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorSlt::BitVectorSlt(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
{
}

bool
BitVectorSlt::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /* IC: pos_x = 0: t = 1 => (s != min_signed_value &&
   *                 ((MSB(x) = 0 && lo_x < s) ||
   *                  (MSB(x) != 0 && 1 o lo_x[bw-2:0] < s))) &&
   *                t = 0 => ((MSB(x) = 1 && hi_x >= s) ||
   *                          (MSB(x) != 1 && 0 o hi_x[bw-2:0] >= s))))
   *     pos_x = 1: t = 1 => (s != max_signed_value &&
   *                          ((MSB(x) = 1 && s < hi_x) ||
   *                           (MSB(x) != 1 && s < 0 o hi_x[bw-2:0])))
   *                t = 0 => ((MSB(x) = 0 && s >= lo_x) ||
   *                          (MSB(x) != 0 && s >= 1 o lo_x[bw-2:0]))) */
  if (x.has_fixed_bits())
  {
    uint32_t msb   = x.size() - 1;
    bool msb_false = x.is_fixed_bit_false(msb);
    bool msb_true  = x.is_fixed_bit_true(msb);
    if (pos_x == 0)
    {
      if (t.is_true())
      {
        if (s.is_min_signed()) return false;
        if (msb_false)
        {
          return x.lo().signed_compare(s) < 0;
        }
        BitVector tmp(x.lo());
        tmp.set_bit(msb, true);
        return tmp.signed_compare(s) < 0;
      }
      if (msb_true)
      {
        return x.hi().signed_compare(s) >= 0;
      }
      BitVector tmp(x.hi());
      tmp.set_bit(msb, false);
      return tmp.signed_compare(s) >= 0;
    }
    assert(pos_x == 1);
    if (t.is_true())
    {
      if (s.is_max_signed()) return false;
      if (msb_true)
      {
        return s.signed_compare(x.hi()) < 0;
      }
      BitVector tmp(x.hi());
      tmp.set_bit(msb, false);
      return s.signed_compare(tmp) < 0;
    }
    if (msb_false)
    {
      return s.signed_compare(x.lo()) >= 0;
    }
    BitVector tmp(x.lo());
    tmp.set_bit(msb, true);
    return s.signed_compare(tmp) >= 0;
  }

  /* IC_wo: pos_x = 0: t = 0 || s != min_signed_value
   *        pos_x = 1: t = 0 || s != max_signed_value */
  if (pos_x == 0)
  {
    return t.is_false() || !s.is_min_signed();
  }
  assert(pos_x == 1);
  return t.is_false() || !s.is_max_signed();
}

bool
BitVectorSlt::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorUrem::BitVectorUrem(RNG* rng,
                             uint32_t size,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorUrem::BitVectorUrem(RNG* rng,
                             const BitVector& assignment,
                             const BitVectorDomain& domain,
                             BitVectorOp* child0,
                             BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
{
}

bool
BitVectorUrem::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  bool check;

  if (pos_x == 0)
  {
    check = s.bvneg().ibvnot().compare(t) >= 0;
  }
  else
  {
    assert(pos_x == 1);
    check = t.bvadd(t).ibvsub(s).ibvand(s).compare(t) >= 0;
  }

  if (check && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if ((pos_x == 0 && x.lo().bvurem(s).compare(t) == 0)
          || (pos_x == 1 && s.bvurem(x.lo()).compare(t) == 0))
      {
        return true;
      }
      return false;
    }
    /* IC: pos_x = 0: IC_wo &&
     *                ((s = 0 || t = ones) => mfb(x, t)) &&
     *                ((s != 0 && t != ones) => \exists y. (
     *                    mfb(x, s * y + t) && !umulo(s, y) && !uaddo(s *y, t)))
     *     pos_x = 1: IC_wo &&
     *                (s = t => (lo_x = 0 || hi_x > t)) &&
     *                (s != t => \exists y. (
     *                    mfb(x, y) && y > t && (s - t) mod y = 0) */
    if (pos_x == 0)
    {
      if (s.is_zero() || t.is_ones())
      {
        return x.match_fixed_bits(t);
      }
      else
      {
        assert(s.compare(t) > 0);
        if (!x.match_fixed_bits(t))
        {
          /* simplest solution (0 <= res < s: res = t) does not apply, thus
           * x = s * n + t with n s.t. (s * n + t) does not overflow */
          uint32_t bw    = x.size();
          BitVector ones = BitVector::mk_ones(bw);
          if (ones.bvsub(s).compare(t) < 0)
          {
            /* overflow for n = 1 -> only simplest solution possible, but
             * simplest possible solution not applicable */
            return false;
          }
          else
          {
            /* x = s * n + t, with n s.t. (s * n + t) does not overflow
             * -> n <= (~0 - t) / s (truncated)
             * -> ~0 - s * n >= t                                       */

            /* n_hi = (~0 - t) / s */
            BitVector n_hi = ones.bvsub(t).ibvudiv(s);
            assert(!n_hi.is_zero());
            /* ~0 - s * n_hi < t ? decrease n_hi until >= t */
            BitVector mul = s.bvmul(n_hi);
            BitVector sub = ones.bvsub(mul);
            while (sub.compare(t) < 0)
            {
              n_hi.ibvdec();
              mul.ibvmul(s, n_hi);
              sub.ibvsub(ones, mul);
            }
            /* hi = s * n_hi + t (upper bound for x) */
            BitVector hi = mul.bvadd(t);
            /* x->lo <= x <= hi */
            BitVectorDomainGenerator gen(x, d_rng, x.lo(), hi);
            while (gen.has_next())
            {
              BitVector bv = gen.next();
              assert(x.match_fixed_bits(bv));
              BitVector rem = bv.bvurem(s);
              if (rem.compare(t) == 0)
              {
                d_inverse.reset(new BitVectorDomain(bv, hi));
                return true;
              }
            }
            return false;
          }
        }
        return true;
      }
    }
    if (s.compare(t) == 0)
    {
      /* s = t: x = 0 or random x > t */
      return x.lo().is_zero() || x.hi().compare(t) > 0;
    }

    /* s = x * n + t
     *
     * In general, x = s - t is always a solution with n = 1, but
     * fixed bits of x may not match s - t. In this case, we look for a
     * factor n s.t. x = (s - t) / n, where fixed bits match. */
    assert(t.compare(s) <= 0);
    BitVector n = s.bvsub(t);
    /* Is (s - t) a solution?
     *
     * -> if yes we do not cache the result to enforce that inverse() selects
     *    one of several possible choices rather than only this solution
     */
    if (!x.match_fixed_bits(n))
    {
      if (t.is_zero() && x.match_fixed_bits(BitVector::mk_one(x.size())))
      {
        /* we don't cache the result for the same reason as above */
        return true;
      }
      /* s - t does not match const bits of x and one is not a possible
       * solution. Find factor n of (s - t) s.t. n > t and n matches the const
       * bits of x. Pick x = n.  */
      BitVector bv = x.get_factor(d_rng, n, t, 10000);
      assert(bv.is_null() || x.match_fixed_bits(bv));
      if (!bv.is_null())
      {
        assert(s.bvurem(bv).compare(t) == 0);
        d_inverse.reset(new BitVectorDomain(bv));
        return true;
      }
      return false;
    }
    return true;
  }
  /* IC_wo: pos_x = 0: ~(-s) >= t
   *        pos_x = 1: (t + t - s) & s >= t */
  return check;
}

bool
BitVectorUrem::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorXor::BitVectorXor(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, size, child0, child1)
{
}

BitVectorXor::BitVectorXor(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1)
    : BitVectorOp(rng, assignment, domain, child0, child1)
{
}

bool
BitVectorXor::is_invertible(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /* IC_wo: true */
  if (!x.has_fixed_bits()) return true;

  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /* IC: mfb(x, s^t) */
  return x.match_fixed_bits(s.bvxor(t));
}

bool
BitVectorXor::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorIte::BitVectorIte(RNG* rng,
                           uint32_t size,
                           BitVectorOp* child0,
                           BitVectorOp* child1,
                           BitVectorOp* child2)
    : BitVectorOp(rng, size, child0, child1, child2)
{
}

BitVectorIte::BitVectorIte(RNG* rng,
                           const BitVector& assignment,
                           const BitVectorDomain& domain,
                           BitVectorOp* child0,
                           BitVectorOp* child1,
                           BitVectorOp* child2)
    : BitVectorOp(rng, assignment, domain, child0, child1, child2)
{
}

bool
BitVectorIte::is_invertible(const BitVector& t, uint32_t pos_x)
{
  uint32_t pos_s0          = pos_x == 0 ? 1 : 0;
  uint32_t pos_s1          = pos_x == 2 ? 1 : 2;
  const BitVector& s0      = d_children[pos_s0]->assignment();
  const BitVector& s1      = d_children[pos_s1]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /* IC: pos_x = 0: (!is_fixed(x) && (s0 = t || s1 = t)) ||
   *                (is_fixed_true(x) && s0 = t) ||
   *                (is_fixed_false(x) && s1 = t)
   *                with s0 the value for '_t' and s1 the value for '_e'
   *     pos_x = 1: s0 = true && mfb(x, t)
   *                with s0 the value for '_c'
   *     pos_x = 2: s0 == false && mfb(x, t)
   *                with s0 the value for '_c'
   */
  if (x.has_fixed_bits())
  {
    if (pos_x == 0)
    {
      if (x.is_fixed())
      {
        if (x.is_fixed_bit_true(0))
        {
          return s0.compare(t) == 0;
        }
        return s1.compare(t) == 0;
      }
      return s0.compare(t) == 0 || s1.compare(t) == 0;
    }
    if (pos_x == 1)
    {
      return s0.is_true() && x.match_fixed_bits(t);
    }
    assert(pos_x == 2);
    return s0.is_false() && x.match_fixed_bits(t);
  }

  /* IC_wo: pos_x = 0: s0 == t || s1 == t
   *                   with s0 the value for the '_t' branch
   *                   and s1 the value for the '_e' branch
   *        pos_x = 1: s0 == true
   *                   with s0 the value for condition '_c'
   *        pos_x = 2: s0 == false
   *                   with s0 the value for condition '_c' */
  if (pos_x == 0)
  {
    return s0.compare(t) == 0 || s1.compare(t) == 0;
  }
  if (pos_x == 1)
  {
    return s0.is_true();
  }
  assert(pos_x == 2);
  return s0.is_false();
}

bool
BitVectorIte::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorExtract::BitVectorExtract(
    RNG* rng, uint32_t size, BitVectorOp* child0, uint32_t hi, uint32_t lo)
    : BitVectorOp(rng, size, child0), d_hi(hi), d_lo(lo)
{
}

BitVectorExtract::BitVectorExtract(RNG* rng,
                                   const BitVector& assignment,
                                   const BitVectorDomain& domain,
                                   BitVectorOp* child0,
                                   uint32_t hi,
                                   uint32_t lo)
    : BitVectorOp(rng, assignment, domain, child0), d_hi(hi), d_lo(lo)
{
}

bool
BitVectorExtract::is_invertible(const BitVector& t, uint32_t pos_x)
{
  (void) pos_x;

  const BitVectorDomain& x = d_children[pos_x]->domain();

  /* IC_wo: true */
  if (!x.has_fixed_bits()) return true;
  // TODO: maybe we should cache the domain extraction
  /* IC: mfb(x[hi:lo], t) */
  return x.bvextract(d_hi, d_lo).match_fixed_bits(t);
}

bool
BitVectorExtract::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */

BitVectorSignExtend::BitVectorSignExtend(RNG* rng,
                                         uint32_t size,
                                         BitVectorOp* child0,
                                         uint32_t n)
    : BitVectorOp(rng, size, child0), d_n(n)
{
}

BitVectorSignExtend::BitVectorSignExtend(RNG* rng,
                                         const BitVector& assignment,
                                         const BitVectorDomain& domain,
                                         BitVectorOp* child0,
                                         uint32_t n)
    : BitVectorOp(rng, assignment, domain, child0), d_n(n)
{
}

bool
BitVectorSignExtend::is_invertible(const BitVector& t, uint32_t pos_x)
{
  (void) pos_x;

  const BitVectorDomain& x = d_children[pos_x]->domain();
  uint32_t size            = t.size();
  BitVector t_x            = t.bvextract(size - 1 - d_n, 0);
  BitVector t_ext          = t.bvextract(size - 1, size - 1 - d_n);

  bool check = t_ext.is_zero() || t_ext.is_ones();

  if (check && x.has_fixed_bits())
  {
    /* IC: IC_wo && mfb(x, t_x) */
    check = x.match_fixed_bits(t_x);
  }
  if (check) d_inverse.reset(new BitVector(t_x));
  /* IC_wo: t_ext == ones || t_ext == zero
   *         and t_x   = t[t_size - 1 - n : 0]
   *         and t_ext = t[t_size - 1, t_size - 1 - n]
   *         (i.e., it includes MSB of t_x) */
  return check;
}

bool
BitVectorSignExtend::is_consistent(const BitVector& t, uint32_t pos_x)
{
  (void) t;
  (void) pos_x;
  // TODO
  return true;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzlals
