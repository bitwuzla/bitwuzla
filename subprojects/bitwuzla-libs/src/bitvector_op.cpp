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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);
  if (d_children[pos_x]->domain().has_fixed_bits())
  {
    /** IC: mfb(x, t - s) */
    uint32_t pos_s           = 1 - pos_x;
    const BitVector& s       = d_children[pos_s]->assignment();
    const BitVectorDomain& x = d_children[pos_x]->domain();
    BitVector sub            = t.bvsub(s);
    if (x.match_fixed_bits(sub))
    {
      d_inverse.reset(new BitVector(std::move(sub)));
      return true;
    }
    return false;
  }
  return true;
}

bool
BitVectorAdd::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);
  (void) t;
  (void) pos_x;
  return true;
}

const BitVector&
BitVectorAdd::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  if (d_inverse == nullptr)
  {
    d_inverse.reset(new BitVector(t.bvsub(s)));
  }
  assert(t.compare(d_inverse->bvadd(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorAdd::consistent_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_consistent == nullptr);
#ifndef NDEBUG
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
#endif
  (void) t;

  /** consistent value: random value */

  if (x.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(x, d_rng);
    d_consistent.reset(new BitVector(gen.random()));
  }
  else
  {
    d_consistent.reset(new BitVector(BitVector(x.size(), *d_rng)));
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /** IC_wo: (t & s) = t */
  bool ic_wo = t.bvand(s).compare(t) == 0;

  /**
   * IC: IC_wo && ((s & hi_x) & m) = (t & m)
   *     with m = ~(lo_x ^ hi_x)  ... mask out all non-const bits
   */
  if (ic_wo && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bvand(s).compare(t) == 0)
      {
        return true;
      }
      return false;
    }
    BitVector mask = x.lo().bvxnor(x.hi());
    return s.bvand(x.hi()).ibvand(mask).compare(t.bvand(mask)) == 0;
  }
  return ic_wo;
}

bool
BitVectorAnd::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /* CC: t & hi_x = t */
  return t.compare(t.bvand(x.hi())) == 0;
}

const BitVector&
BitVectorAnd::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /** inverse value: (t & s) | (~s & rand) */

  uint32_t size = t.size();
  BitVector rand;
  if (x.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(x, d_rng);
    assert(gen.has_random());
    rand = gen.random();
  }
  else
  {
    rand = BitVector(size, *d_rng);
  }
  d_inverse.reset(new BitVector(t.bvand(s).bvor(s.bvnot().ibvand(rand))));

  assert(t.compare(d_inverse->bvand(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorAnd::consistent_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_consistent == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());

  /** consistent value: t | rand */

  if (x.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(x, d_rng);
    d_consistent.reset(new BitVector(gen.random().ibvor(t)));
  }
  else
  {
    d_consistent.reset(new BitVector(BitVector(x.size(), *d_rng).ibvor(t)));
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector tx;
  bool ic_wo;

  uint32_t bw_t = t.size();
  uint32_t bw_s = s.size();

  /**
   * IC_wo: s = ts
   *   pos_x = 0: ts = t[size(s) - 1 : 0]
   *   pos_x = 1: ts = t[size(t) - 1 : size(t) - size(s)]
   */
  if (pos_x == 0)
  {
    ic_wo = t.bvextract(bw_s - 1, 0).compare(s) == 0;
    tx    = t.bvextract(bw_t - 1, bw_s);
  }
  else
  {
    assert(pos_x == 1);
    ic_wo = t.bvextract(bw_t - 1, bw_t - bw_s).compare(s) == 0;
    tx    = t.bvextract(bw_t - bw_s - 1, 0);
  }

  /** IC: IC_wo && mfb(x, tx) */
  if (ic_wo && x.has_fixed_bits())
  {
    if (x.match_fixed_bits(tx))
    {
      d_inverse.reset(new BitVector(std::move(tx)));
      return true;
    }
    return false;
  }

  return ic_wo;
}

bool
BitVectorConcat::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC: mfb(x, tx)
   * with pos_x = 0: tx = t[size(t) - 1 : size(t) - size(x)]
   *      pos_x = 1: tx = t[size(x) - 1 : 0]
   */

  uint32_t bw_t            = t.size();
  uint32_t bw_x            = x.size();
  if (pos_x == 0)
  {
    return x.match_fixed_bits(t.bvextract(bw_t - 1, bw_t - bw_x));
  }
  return x.match_fixed_bits(t.bvextract(bw_x - 1, 0));
}

const BitVector&
BitVectorConcat::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      /** inverse value: t[size(t) - 1: size(s)] */
      d_inverse.reset(new BitVector(t.bvextract(t.size() - 1, s.size())));
    }
    else
    {
      /** inverse value: t[size(x) - 1: 0] */
      d_inverse.reset(new BitVector(t.bvextract(x.size() - 1, 0)));
    }
  }
  assert(pos_x == 1 || t.compare(d_inverse->bvconcat(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvconcat(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorConcat::consistent_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_consistent == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t bw_t = t.size();
  uint32_t bw_x = x.size();

  if (pos_x == 0)
  {
    /** consistent value: t[msb, bw_x] */
    d_consistent.reset(new BitVector(t.bvextract(bw_t - 1, bw_t - bw_x)));
  }
  else
  {
    /** consistent value: t[bw_x - 1, 0] */
    d_consistent.reset(new BitVector(t.bvextract(bw_x - 1, 0)));
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /**
   * IC: t = 0: (hi_x != lo_x) || (hi_x != s)
   *     t = 1: mfb(x, s)
   */
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
    if (t.is_false())
    {
      return x.hi().compare(x.lo()) || x.hi().compare(s);
    }
    return x.match_fixed_bits(s);
  }

  /** IC_wo: true */
  return true;
}

bool
BitVectorEq::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  (void) t;
  (void) pos_x;
  /* CC: true */
  return true;
}

const BitVector&
BitVectorEq::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /**
   * inverse value: t = 0: random bit-vector != s
   *                t = 1: s
   */

  if (t.is_zero())
  {
    if (x.has_fixed_bits())
    {
      BitVector res;
      BitVectorDomainGenerator gen(x, d_rng);
      do
      {
        assert(gen.has_random());
        res = gen.random();
      } while (s.compare(res) == 0);
      d_inverse.reset(new BitVector(std::move(res)));
    }
    else
    {
      BitVector res;
      do
      {
        res = BitVector(x.size(), *d_rng);
      } while (s.compare(res) == 0);
      d_inverse.reset(new BitVector(std::move(res)));
    }
  }
  else
  {
    assert(x.match_fixed_bits(s));
    d_inverse.reset(new BitVector(s));
  }

  assert(t.compare(d_inverse->bveq(s)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorEq::consistent_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_consistent == nullptr);
#ifndef NDEBUG
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
#endif
  (void) t;

  /** consistent value: random value */
  if (x.has_fixed_bits())
  {
    BitVectorDomainGenerator gen(x, d_rng);
    d_consistent.reset(new BitVector(gen.random()));
  }
  else
  {
    d_consistent.reset(new BitVector(BitVector(x.size(), *d_rng)));
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);
  d_inverse_domain.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /** IC_wo: ((-s | s) & t) = t */
  bool ic_wo = s.bvneg().ibvor(s).ibvand(t).compare(t) == 0;

  /**
   * IC: IC_wo &&
   *     (s = 0 || ((odd(s) => mfb(x, t * s^-1)) &&
   *               (!odd(s) => mfb (x << c, y << c))))
   *     with c = ctz(s) and y = (t >> c) * (s >> c)^-1
   */
  if (ic_wo && x.has_fixed_bits())
  {
    if (x.is_fixed())
    {
      if (x.lo().bvmul(s).compare(t) == 0)
      {
        return true;
      }
      return false;
    }

    if (!s.is_zero())
    {
      /*-- s odd --*/
      if (s.get_lsb())
      {
        BitVector inv = s.bvmodinv().ibvmul(t);
        if (x.match_fixed_bits(inv))
        {
          d_inverse.reset(new BitVector(std::move(inv)));
          return true;
        }
        return false;
      }

      /*-- s even --*/
      /* Check if relevant bits of
       *   y = (t >> ctz(s)) * (s >> ctz(s))^-1
       * match corresponding constant bits of x, i.e.,
       * mfb(x[size - ctz(s) - 1:0], y[size - ctz(s) - 1:0]). */
      uint32_t size   = x.size();
      uint32_t ctz    = s.count_trailing_zeros();
      BitVector y_ext = t.bvshr(ctz)
                            .ibvmul(s.bvshr(ctz).ibvmodinv())
                            .ibvextract(size - ctz - 1, 0);
      if (x.bvextract(size - ctz - 1, 0).match_fixed_bits(y_ext))
      {
        /* Result domain is x[size - 1:size - ctz] o y[size - ctz(s) - 1:0] */
        d_inverse_domain.reset(new BitVectorDomain(
            x.bvextract(size - 1, size - ctz).bvconcat(y_ext)));
        return true;
      }
      return false;
    }
    return true;
  }

  return ic_wo;
}

bool
BitVectorMul::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC: (t != 0 => xhi != 0) &&
   *     (odd(t) => xhi[lsb] != 0) &&
   *     (!odd(t) => \exists y. (mcb(x, y) && ctz(t) >= ctz(y))
   */

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

const BitVector&
BitVectorMul::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /**
   * inverse value:
   *
   *   s = 0 (=> t = 0): random bit-vector
   *
   *   s odd : t * s^-1 (unique solution)
   *
   *   s even: multiple solutions possible
   *      + s = 2^n: t >> n
   *                 with all bits shifted in randomly set to 0 or 1
   *      + s = 2^n * m, m is odd: c * m^-1
   *                               with c = t >> n and
   *                               all bits shifted in set randomly and
   *                               m^-1 the mod inverse of m
   *
   */

  uint32_t size = t.size();

  if (d_inverse == nullptr && d_inverse_domain == nullptr)
  {
    if (s.is_zero())
    {
      assert(t.is_zero());
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(x, d_rng);
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(new BitVector(size, *d_rng));
      }
    }
    else if (s.get_lsb())
    {
      assert(!x.has_fixed_bits());
      d_inverse.reset(new BitVector(t.bvmul(s.bvmodinv())));
    }
    else
    {
      assert(!x.has_fixed_bits());
      assert(t.count_trailing_zeros() >= s.count_trailing_zeros());
      uint32_t n = s.count_trailing_zeros();
      BitVector right;
      if (s.is_power_of_two())
      {
        right = t.bvextract(size - 1, n);
      }
      else
      {
        right = s.bvshr(n)
                    .ibvmodinv()
                    .ibvmul(t.bvshr(n))
                    .ibvextract(size - n - 1, 0);
      }
      d_inverse.reset(new BitVector(BitVector(n, *d_rng).ibvconcat(right)));
    }
  }
  else if (d_inverse_domain != nullptr)
  {
    if (d_inverse_domain->is_fixed())
    {
      d_inverse.reset(new BitVector(d_inverse_domain->lo()));
    }
    else
    {
      BitVectorDomainGenerator gen(*d_inverse_domain, d_rng);
      d_inverse.reset(new BitVector(gen.random()));
    }
  }
  assert(pos_x == 1 || t.compare(d_inverse->bvmul(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvmul(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorMul::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());

  /**
   * consistent value:
   *   t = 0: random value
   *   t > 0: t odd : random odd value
   *          t even: random even value > 0 with ctz(x) <= ctz(t)
   */

  if (d_consistent == nullptr)
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainGenerator gen(x, d_rng);
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(new BitVector(BitVector(x.size(), *d_rng)));
    }

    if (!t.is_zero())
    {
      while (d_consistent->is_zero())
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(BitVector(x.size(), *d_rng)));
        }
      }

      if (t.get_lsb())
      {
        if (!d_consistent->get_lsb())
        {
          assert(!x.is_fixed_bit_false(0));
          d_consistent->set_bit(0, true);
        }
      }
      else
      {
        assert(!x.has_fixed_bits());
        uint32_t ctz_t = t.count_trailing_zeros();
        /* choose consistent value as 2^n with prob 0.1 */
        if (d_rng->pick_with_prob(100))
        {
          d_consistent->iset(0);
          d_consistent->set_bit(d_rng->pick<uint32_t>(0, ctz_t - 1), true);
        }
        /* choose consistent value as t / 2^n with prob 0.1 */
        else if (d_rng->pick_with_prob(100))
        {
          d_consistent->iset(t);
          uint32_t r = d_rng->pick<uint32_t>(0, ctz_t);
          if (r > 0)
          {
            d_consistent->ibvshr(r);
          }
        }
        /* choose random value with ctz(t) >= ctz(res) with prob 0.8 */
        else
        {
          if (d_consistent->count_trailing_zeros() > ctz_t)
          {
            d_consistent->set_bit(d_rng->pick<uint32_t>(0, ctz_t - 1), true);
          }
        }
      }
    }
  }

  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  uint32_t ctz_t           = 0;
  uint32_t ctz_s           = 0;
  bool ic_wo;

  /**
   * IC_wo: pos_x = 0: (t >> s) << s = t
   *        pos_x = 1: ctz(s) <= ctz(t) &&
   *                   ((t = 0) || (s << (ctz(t) - ctz(s))) = t)
   */
  if (pos_x == 0)
  {
    ic_wo = t.bvshr(s).ibvshl(s).compare(t) == 0;
  }
  else
  {
    assert(pos_x == 1);
    ctz_t = t.count_trailing_zeros();
    ctz_s = s.count_trailing_zeros();
    ic_wo = ctz_s <= ctz_t
            && (t.is_zero() || s.bvshl(ctz_t - ctz_s).compare(t) == 0);
  }

  /**
   * IC: pos_x = 0: IC_wo && mfb(x << s, t)
   *     pos_x = 1: IC_wo &&
   *                ((t = 0) => (hi_x >= ctz(t) - ctz(s) || (s = 0))) &&
   *                ((t != 0) => mfb(x, ctz(t) - ctz(s)))
   */
  if (ic_wo && x.has_fixed_bits())
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

    if (pos_x == 0)
    {
      return x.bvshl(s).match_fixed_bits(t);
    }
    if (t.is_zero())
    {
      uint32_t size    = x.size();
      bool s_is_zero = s.is_zero();
      BitVector min  = BitVector(size, ctz_t - ctz_s);
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

  return ic_wo;
}

bool
BitVectorShl::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC: pos_x = 0: \exists y. (y <= ctz(t) /\ mcb(x << y, t))
   *     pos_x = 1: t = 0 \/ \exists y. (y <= ctz(t) /\ mcb(x, y))
   */

  uint32_t ctz_t           = t.count_trailing_zeros();
  uint32_t size            = t.size();

  if (ctz_t != size)
  {
    if (pos_x == 0)
    {
      if (x.is_fixed())
      {
        uint32_t ctz_x = x.lo().count_trailing_zeros();
        return x.lo().bvshl(ctz_t - ctz_x).compare(t) == 0;
      }

      std::vector<BitVector> stack;

      for (uint32_t i = 0; i <= ctz_t; ++i)
      {
        BitVectorDomain x_slice = x.bvextract(size - 1 - i, 0);
        BitVector t_slice       = t.bvextract(size - 1, i);
        if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
      }
      bool res = !stack.empty();
      if (res)
      {
        uint32_t i          = d_rng->pick<uint32_t>(0, stack.size() - 1);
        BitVector& right    = stack[i];
        uint32_t size_right = right.size();
        if (size == size_right)
        {
          d_consistent.reset(new BitVector(right));
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          d_consistent.reset(new BitVector(
              gen.random().ibvextract(size - 1, size_right).ibvconcat(right)));
        }
      }
      return res;
    }
    else
    {
      if (x.is_fixed())
      {
        return BitVector(size, ctz_t).compare(x.lo()) >= 0;
      }

      BitVectorDomainGenerator gen(x, d_rng, x.lo(), BitVector(size, ctz_t));
      bool res = gen.has_random();
      if (res)
      {
        d_consistent.reset(new BitVector(gen.random()));
      }
      return res;
    }
  }
  return true;
}

const BitVector&
BitVectorShl::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = t.size();

  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      /** inverse value: t >> s (with bits shifted in set randomly) */

      /* actual value is small enough to fit into 32 bit (max bit width handled
       * is INT32_MAX) */
      uint32_t shift;
      if (size > 64)
      {
        shift = s.bvextract(32, 0).to_uint64();
      }
      else
      {
        shift = s.to_uint64();
      }
      assert(shift >= size || t.count_trailing_zeros() >= shift);
      assert(shift < size || t.count_trailing_zeros() == size);

      if (shift >= size)
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          d_inverse.reset(new BitVector(gen.random()));
        }
        else
        {
          d_inverse.reset(new BitVector(size, *d_rng));
        }
      }
      else if (shift > 0)
      {
        BitVector left;
        if (x.has_fixed_bits())
        {
          BitVectorDomain x_ext = x.bvextract(size - 1, size - shift);
          if (x_ext.is_fixed())
          {
            left = x_ext.lo();
          }
          else
          {
            BitVectorDomainGenerator gen(x_ext, d_rng);
            assert(gen.has_random());
            left = gen.random();
          }
        }
        else
        {
          left = BitVector(shift, *d_rng);
        }
        d_inverse.reset(new BitVector(
            std::move(left.ibvconcat(t.bvextract(size - 1, shift)))));
      }
      else
      {
        d_inverse.reset(new BitVector(t));
      }
    }
    else
    {
      /**
       * inverse value:
       *   s = 0 && t = 0: random
       *
       *   else          : shift = ctz(t) - ctz(s)
       *                   + t = 0: shift <= res < size
       *                   + else : shift
       *
       */

      if (s.is_zero() && t.is_zero())
      {
        d_inverse.reset(new BitVector(size, *d_rng));
      }
      else
      {
        uint32_t ctz_s = s.count_trailing_zeros();
        uint32_t ctz_t = t.count_trailing_zeros();
        assert(ctz_t >= ctz_s);
        uint32_t shift = ctz_t - ctz_s;
        if (t.is_zero())
        {
          assert(!x.has_fixed_bits());
          d_inverse.reset(new BitVector(
              size, *d_rng, BitVector(size, shift), BitVector::mk_ones(size)));
        }
        else
        {
          d_inverse.reset(new BitVector(size, shift));
        }
      }
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvshl(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvshl(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorShl::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());

  /**
   * consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with ctz(x) <= ctz(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value <= ctz(t)
   */

  if (d_consistent == nullptr)
  {
    uint32_t size  = x.size();
    uint32_t ctz_t = t.count_trailing_zeros();

    if (pos_x == 0)
    {
      if (ctz_t == size)
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(size, *d_rng));
        }
      }
      else
      {
        assert(!x.has_fixed_bits());
        uint32_t shift = d_rng->pick<uint32_t>(0, ctz_t);
        if (shift == 0)
        {
          d_consistent.reset(new BitVector(t));
        }
        else
        {
          d_consistent.reset(
              new BitVector(BitVector(shift, *d_rng)
                                .ibvconcat(t.bvextract(size - 1, shift))));
        }
      }
    }
    else
    {
      uint32_t max = ctz_t < size ? ctz_t : ((1u << size) - 1);
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(
            x, d_rng, BitVector::mk_zero(size), BitVector(size, max));
        assert(gen.has_random());
        d_consistent.reset(new BitVector(gen.random()));
      }
      else
      {
        d_consistent.reset(new BitVector(size, d_rng->pick<uint32_t>(0, max)));
      }
    }
  }

  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

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
  bool ic_wo;

  /**
   * IC_wo: pos_x = 0: (t << s) >> s = t
   *        pos_x = 1: clz(s) <= clz(t) &&
   *                   ((t = 0) || (s >> (clz(t) - clz(s))) = t)
   */
  if (pos_x == 0)
  {
    ic_wo = t.bvshl(s).ibvshr(s).compare(t) == 0;
  }
  else
  {
    assert(pos_x == 1);
    clz_t = t.count_leading_zeros();
    clz_s = s.count_leading_zeros();
    ic_wo = clz_s <= clz_t
            && (t.is_zero() || s.bvshr(clz_t - clz_s).compare(t) == 0);
  }

  /**
   * IC: pos_x = 0: IC_wo && mfb(x >> s, t)
   *     pos_x = 1: IC_wo &&
   *                ((t = 0) => (hi_x >= clz(t) - clz(s) || (s = 0))) &&
   *                ((t != 0) => mfb(x, clz(t) - clz(s)))
   */
  if (ic_wo && x.has_fixed_bits())
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
    if (pos_x == 0)
    {
      return x.bvshr(s).match_fixed_bits(t);
    }
    if (t.is_zero())
    {
      uint32_t size    = x.size();
      bool s_is_zero = s.is_zero();
      BitVector min  = BitVector(size, clz_t - clz_s);
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

  return ic_wo;
}

bool
BitVectorShr::is_consistent(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /* CC: pos_x = 0: \exists y. (y <= ctz(t) /\ mcb(x >> y, t))
   *     pos_x = 1: t = 0 \/ \exists y. (y <= ctz(t) /\ mcb(x, y)) */

  uint32_t clz_t           = t.count_leading_zeros();
  uint32_t size            = t.size();

  if (clz_t != size)
  {
    if (pos_x == 0)
    {
      if (x.is_fixed())
      {
        uint32_t clz_x = x.lo().count_leading_zeros();
        return x.lo().bvshr(clz_t - clz_x).compare(t) == 0;
      }

      std::vector<BitVector> stack;

      for (uint32_t i = 0; i <= clz_t; ++i)
      {
        BitVectorDomain x_slice = x.bvextract(size - 1, i);
        BitVector t_slice       = t.bvextract(size - 1 - i, 0);
        if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
      }
      bool res = !stack.empty();
      if (res)
      {
        uint32_t i         = d_rng->pick<uint32_t>(0, stack.size() - 1);
        BitVector& left    = stack[i];
        uint32_t size_left = left.size();
        if (size == size_left)
        {
          d_consistent.reset(new BitVector(left));
        }
        else
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          d_consistent.reset(new BitVector(left.ibvconcat(
              gen.random().ibvextract(size - 1 - size_left, 0))));
        }
      }
      return res;
    }
    else
    {
      if (x.is_fixed())
      {
        return BitVector(size, clz_t).compare(x.lo()) >= 0;
      }

      BitVectorDomainGenerator gen(x, d_rng, x.lo(), BitVector(size, clz_t));
      bool res = gen.has_random();
      if (res)
      {
        d_consistent.reset(new BitVector(gen.random()));
      }
      return res;
    }
  }
  return true;
}

const BitVector&
BitVectorShr::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      assert(s.compare(BitVector(s.size(), s.size())) >= 0
             || s.compare(BitVector(s.size(), t.count_leading_zeros())) <= 0);
      assert(s.compare(BitVector(s.size(), s.size())) < 0 || t.is_zero());
      inverse_value(d_rng, t, s, x, 0, d_inverse);
    }
    else
    {
      inverse_value(d_rng, t, s, x, 1, d_inverse);
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvshr(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvshr(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

void
BitVectorShr::inverse_value(RNG* rng,
                            const BitVector& t,
                            const BitVector& s,
                            const BitVectorDomain& x,
                            uint32_t pos_x,
                            std::unique_ptr<BitVector>& inverse_value)
{
  uint32_t size = t.size();
  if (pos_x == 0)
  {
    /** inverse value: t << s (with bits shifted in set randomly) */

    /* actual value is small enough to fit into 32 bit (max bit width handled
     * is INT32_MAX) */
    uint32_t shift;
    if (size > 64)
    {
      shift = s.bvextract(32, 0).to_uint64();
    }
    else
    {
      shift = s.to_uint64();
    }

    if (shift >= size)
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(x, rng);
        assert(gen.has_random());
        inverse_value.reset(new BitVector(gen.random()));
      }
      else
      {
        inverse_value.reset(new BitVector(size, *rng));
      }
    }
    else if (shift > 0)
    {
      BitVector right;
      if (x.has_fixed_bits())
      {
        BitVectorDomain x_ext = x.bvextract(shift - 1, 0);
        if (x_ext.is_fixed())
        {
          right = x_ext.lo();
        }
        else
        {
          BitVectorDomainGenerator gen(x_ext, rng);
          assert(gen.has_random());
          right = gen.random();
        }
      }
      else
      {
        right = BitVector(shift, *rng);
      }
      inverse_value.reset(new BitVector(
          std::move(t.bvextract(size - shift - 1, 0).ibvconcat(right))));
    }
    else
    {
      inverse_value.reset(new BitVector(t));
    }
  }
  else
  {
    /**
     * inverse value:
     *   s = 0 && t = 0: random
     *
     *   else          : shift = clz(t) - clz(s)
     *                   + t = 0: shift <= res < size
     *                   + else : shift
     *
     */
    if (s.is_zero() && t.is_zero())
    {
      inverse_value.reset(new BitVector(size, *rng));
    }
    else
    {
      uint32_t clz_s = s.count_leading_zeros();
      uint32_t clz_t = t.count_leading_zeros();
      assert(clz_t >= clz_s);
      uint32_t shift = clz_t - clz_s;
      if (t.is_zero())
      {
        assert(!x.has_fixed_bits());
        inverse_value.reset(new BitVector(
            size, *rng, BitVector(size, shift), BitVector::mk_ones(size)));
      }
      else
      {
        inverse_value.reset(new BitVector(size, shift));
      }
    }
  }
}

const BitVector&
BitVectorShr::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());

  /**
   * consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with clz(x) <= clz(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value <= clz(t)
   */

  if (d_consistent == nullptr)
  {
    uint32_t size  = x.size();
    uint32_t clz_t = t.count_leading_zeros();

    if (pos_x == 0)
    {
      if (clz_t == size)
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(size, *d_rng));
        }
      }
      else
      {
        assert(!x.has_fixed_bits());
        uint32_t shift = d_rng->pick<uint32_t>(0, clz_t);
        if (shift == 0)
        {
          d_consistent.reset(new BitVector(t));
        }
        else
        {
          d_consistent.reset(
              new BitVector(t.bvextract(size - shift - 1, 0)
                                .ibvconcat(BitVector(shift, *d_rng))));
        }
      }
    }
    else
    {
      uint32_t max = clz_t < size ? clz_t : ((1u << size) - 1);
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(
            x, d_rng, BitVector::mk_zero(size), BitVector(size, max));
        assert(gen.has_random());
        d_consistent.reset(new BitVector(gen.random()));
      }
      else
      {
        d_consistent.reset(new BitVector(size, d_rng->pick<uint32_t>(0, max)));
      }
    }
  }

  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector snot, tnot, sshr;
  bool ic_wo;

  /**
   * IC_wo: pos_x = 0: (s < size(s) => (t << s) >>a s = t) &&
   *                   (s >= size(s) => (t = ones || t = 0))
   *        pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
   *                   (s[msb] = 1 => IC_shr(~s >> x = ~t)
   *
   * IC:
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

  uint32_t size = s.size();
  if (s.compare(BitVector(size, size)) < 0)
  {
    ic_wo = t.bvshl(s).ibvashr(s).compare(t) == 0;
  }
  else
  {
    ic_wo = t.is_zero() || t.is_ones();
  }

  if (ic_wo && x.has_fixed_bits())
  {
    return x.bvashr(s).match_fixed_bits(t);
  }
  return ic_wo;
}

bool
BitVectorAshr::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits:
   *     pos_x = 0:
   *     ((t = 0 \/ t = ones) => \exists y. (y[msb] = t[msb] /\ mcb(x, y))) /\
   *     ((t != 0 /\ t != ones) => \exists y. (
   *        c => y <= clo(t) /\ ~c => y <= clz(t) /\ mcb(x, y))
   *     with c = ((t << y)[msb] = 1)
   *
   *     pos_x = 1:
   *     t = 0 \/ t = ones \/
   *     \exists y. (c => y < clo(t) /\ ~c => y < clz(t) /\ mcb(x, y)
   *     with c = (t[msb] = 1)
   */

  bool is_signed = t.get_msb();
  uint32_t cnt_t = is_signed ? t.count_leading_ones() : t.count_leading_zeros();
  uint32_t size  = t.size();

  if (x.is_fixed())
  {
    if (pos_x == 0)
    {
      uint32_t cnt_x = is_signed ? x.lo().count_leading_ones()
                                 : x.lo().count_leading_zeros();
      return x.lo().bvashr(cnt_t - cnt_x).compare(t) == 0;
    }
    return t.is_zero() || t.is_ones()
           || BitVector(size, cnt_t).compare(x.lo()) > 0;
  }

  if (!is_signed && t.is_zero())
  {
    if (pos_x == 0)
    {
      BitVectorDomainSignedGenerator gen(
          x, d_rng, BitVector::mk_zero(size), BitVector::mk_max_signed(size));
      bool res = gen.has_random();
      if (res)
      {
        d_consistent.reset(new BitVector(gen.random()));
      }
      return res;
    }
    return true;
  }

  if (is_signed && t.is_ones())
  {
    if (pos_x == 0)
    {
      BitVectorDomainSignedGenerator gen(
          x, d_rng, BitVector::mk_min_signed(size), BitVector::mk_ones(size));
      bool res = gen.has_random();
      if (res)
      {
        d_consistent.reset(new BitVector(gen.random()));
      }
      return res;
    }
    return true;
  }

  if (pos_x)
  {
    BitVectorDomainGenerator gen(x, d_rng, x.lo(), BitVector(size, cnt_t - 1));
    bool res = gen.has_random();
    if (res)
    {
      d_consistent.reset(new BitVector(gen.random()));
    }
    return res;
  }
  std::vector<BitVector> stack;

  for (uint32_t i = 0; i < cnt_t; ++i)
  {
    BitVectorDomain x_slice = x.bvextract(size - 1, i);
    BitVector t_slice       = t.bvextract(size - 1 - i, 0);
    if (x_slice.match_fixed_bits(t_slice)) stack.push_back(t_slice);
  }
  bool res = !stack.empty();
  if (res)
  {
    uint32_t i         = d_rng->pick<uint32_t>(0, stack.size() - 1);
    BitVector& left    = stack[i];
    uint32_t size_left = left.size();
    if (size == size_left)
    {
      d_consistent.reset(new BitVector(left));
    }
    else
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      d_consistent.reset(new BitVector(
          left.bvconcat(gen.random().ibvextract(size - 1 - size_left, 0))));
    }
  }
  return res;
}

const BitVector&
BitVectorAshr::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = t.size();

  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      BitVectorShr::inverse_value(d_rng, t, s, x, 0, d_inverse);
      if (t.get_msb())
      {
        if (!d_inverse->get_msb())
        {
          assert(!x.is_fixed_bit(x.size() - 1));
          d_inverse->set_bit(x.size() - 1, true);
        }
        assert(s.compare(BitVector(s.size(), s.size())) >= 0
               || s.compare(BitVector(s.size(), t.count_leading_ones())) <= 0);
        assert(s.compare(BitVector(s.size(), s.size())) < 0 || t.is_ones());
      }
      else
      {
        if (d_inverse->get_msb())
        {
          assert(!x.is_fixed_bit(x.size() - 1));
          d_inverse->set_bit(x.size() - 1, false);
        }
        assert(s.compare(BitVector(s.size(), s.size())) >= 0
               || s.compare(BitVector(s.size(), t.count_leading_zeros())) <= 0);
        assert(s.compare(BitVector(s.size(), s.size())) < 0 || t.is_zero());
      }
    }
    else
    {
      /**
       * inverse value:
       *   s = 0 && t = 0: random
       *
       *   else          : shift = cnt(t) - cnt(s)
       *                   with cnt = clz if t[msb] = 0 else clo
       *                   + t = 0: shift <= res < size
       *                   + else : shift
       *
       */
      if (!s.get_msb())
      {
        BitVectorShr::inverse_value(d_rng, t, s, x, 1, d_inverse);
      }
      else
      {
        assert(t.get_msb());
        if (s.is_ones() && t.is_ones())
        {
          d_inverse.reset(new BitVector(size, *d_rng));
        }
        else
        {
          uint32_t clo_s = s.count_leading_ones();
          uint32_t clo_t = t.count_leading_ones();
          assert(clo_t >= clo_s);
          uint32_t shift = clo_t - clo_s;
          if (t.is_ones())
          {
            assert(!x.has_fixed_bits());
            d_inverse.reset(new BitVector(size,
                                          *d_rng,
                                          BitVector(size, shift),
                                          BitVector::mk_ones(size)));
          }
          else
          {
            d_inverse.reset(new BitVector(size, shift));
          }
        }
      }
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvashr(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvashr(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorAshr::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());

  /**
   * consistent value:
   *   pos_x = 0: t = 0: random
   *              t > 0: random value with cnt(x) < cnt(t)
   *   pos_x = 1: t = 0: random
   *              t > 0: random value < cnt(t)
   *   with cnt = clz if t[msb] = 0 and cnt = clo if t[msb] = 1
   */

  if (d_consistent == nullptr)
  {
    bool is_signed = t.get_msb();
    uint32_t size  = x.size();
    uint32_t cnt_t =
        is_signed ? t.count_leading_ones() : t.count_leading_zeros();

    if (pos_x == 0)
    {
      if (cnt_t == size)
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(size, *d_rng));
        }
        if (is_signed && !d_consistent->get_msb())
        {
          d_consistent->set_bit(size - 1, true);
        }
        else if (!is_signed && d_consistent->get_msb())
        {
          d_consistent->set_bit(size - 1, false);
        }
      }
      else if (cnt_t == 0)
      {
        d_consistent.reset(new BitVector(t));
      }
      else
      {
        assert(!x.has_fixed_bits());
        uint32_t shift = d_rng->pick<uint32_t>(0, cnt_t - 1);
        if (shift == 0)
        {
          d_consistent.reset(new BitVector(t));
        }
        else
        {
          d_consistent.reset(
              new BitVector(t.bvextract(size - shift - 1, 0)
                                .ibvconcat(BitVector(shift, *d_rng))));
        }
      }
    }
    else
    {
      uint32_t max = cnt_t < size ? cnt_t - 1 : ((1u << size) - 1);
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(
            x, d_rng, BitVector::mk_zero(size), BitVector(size, max));
        assert(gen.has_random());
        d_consistent.reset(new BitVector(gen.random()));
      }
      else
      {
        d_consistent.reset(new BitVector(size, d_rng->pick<uint32_t>(0, max)));
      }
    }
  }

  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  BitVector s_mul_t, s_udiv_t;
  bool ic_wo;

  /**
   * IC_wo: pos_x = 0: (s * t) / s = t
   *        pos_x = 1: s / (s / t) = t
   */
  if (pos_x == 0)
  {
    s_mul_t = s.bvmul(t);
    ic_wo   = s_mul_t.bvudiv(s).compare(t) == 0;
  }
  else
  {
    assert(pos_x == 1);
    s_udiv_t = s.bvudiv(t);
    ic_wo    = s.bvudiv(s_udiv_t).compare(t) == 0;
  }

  /**
   * IC: pos_x = 0: IC_wo &&
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
  if (ic_wo && x.has_fixed_bits())
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
          d_inverse.reset(new BitVector(gen.random()));
          return true;
        }
        return false;
      }
      return true;
    }
    else if (!s.is_zero() || !t.is_zero())
    {
      uint32_t size = s.size();
      BitVector min, max;
      if (s.bvudiv(x.hi()).compare(t) > 0)
      {
        return false;
      }

      if (t.is_ones())
      {
        min = BitVector::mk_zero(size);
        max = s.is_ones() ? BitVector::mk_one(size) : min;
      }
      else if (s.compare(t) == 0)
      {
        min = BitVector::mk_one(size);
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
        d_inverse.reset(new BitVector(gen.random()));
        return true;
      }
      return false;
    }
    return true;
  }

  return ic_wo;
}

bool
BitVectorUdiv::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC: pos_x = 0:
   *       (t != ones => x_hi >= t) && (t = 0 => x_lo != ones) &&
   *       ((t != 0 && t != ones && t != 1 && !mfb(x, t)) =>
   *        (!mulo(2, t) && \exists y,o.(mfb(x, y*t + o) && y >= 1 && o <= c
   *         && !mulo(y, t) && !addo(y * t, o))))
   *     with c = min(y − 1, x_hi − y * t)
   *
   *     pos_x = 1:
   *       (t = ones => (mfb(x, 0) || mfb(x, 1))) &&
   *       (t != ones => (!mulo(x_lo, t) &&
   *                  \exists y. (y > 0 && mfb(x, y) && !mulo(y, t))))
   */

  bool t_is_zero = t.is_zero();
  bool t_is_ones = t.is_ones();

  if (pos_x == 0)
  {
    if (!t_is_ones && x.hi().compare(t) < 0) return false;
    if (t_is_zero && x.lo().is_ones()) return false;

    if (!t_is_zero && !t_is_ones && !t.is_one() && !x.match_fixed_bits(t))
    {
      BitVector bvres = consistent_value_pos0_aux(t);
      bool res        = !bvres.is_null();
      if (res)
      {
        d_consistent.reset(new BitVector(bvres));
      }
      return res;
    }
  }
  else
  {
    if (x.hi().is_zero())
    {
      return t.is_ones();
    }

    uint32_t size  = t.size();
    BitVector zero = BitVector::mk_zero(size);
    BitVector one  = BitVector::mk_one(size);

    if (t_is_ones && !x.match_fixed_bits(zero) && !x.match_fixed_bits(one))
    {
      return false;
    }

    if (!t_is_ones)
    {
      if (x.lo().is_umul_overflow(t))
      {
        return false;
      }

      if (!x.is_fixed())
      {
        bool res = true;
        BitVectorDomainGenerator gen(x, d_rng, one, x.hi());
        assert(gen.has_random());
        BitVector bvres = gen.random();
        while (bvres.is_umul_overflow(t))
        {
          bvres.ibvdec();
          BitVectorDomainGenerator ggen(x, d_rng, one, bvres);
          if (!ggen.has_random())
          {
            res = false;
            break;
          }
          bvres = ggen.random();
        }
        if (res)
        {
          d_consistent.reset(new BitVector(bvres));
        }
        return res;
      }
    }
  }
  return true;
}

const BitVector&
BitVectorUdiv::inverse_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = t.size();

  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      /**
       * inverse value:
       *   t = ones: s = 1: ones
       *             s = 0: random value
       *
       *   s * t does not overflow: - s * t
       *                            - v with v / s = t
       *                            (0.5 prob)
       */
      if (t.is_ones())
      {
        if (s.is_one())
        {
          d_inverse.reset(new BitVector(BitVector::mk_ones(size)));
        }
        else
        {
          assert(s.is_zero());
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(x, d_rng);
            assert(gen.has_random());
            d_inverse.reset(new BitVector(gen.random()));
          }
          else
          {
            d_inverse.reset(new BitVector(size, *d_rng));
          }
        }
      }
      else
      {
        assert(!s.is_umul_overflow(t));
        BitVector mul = s.bvmul(t);
        if (d_rng->flip_coin() && x.match_fixed_bits(mul))
        {
          d_inverse.reset(new BitVector(std::move(mul)));
        }
        else
        {
          /**
           * determine upper and lower bounds:
           * upper = s * (t + 1) - 1
           *         if s * (t + 1) does not overflow, else
           *         ones
           * lower = s * t
           */
          BitVector up = t.bvinc();
          if (s.is_umul_overflow(up))
          {
            up = BitVector::mk_ones(size);
          }
          else
          {
            up.ibvmul(s).ibvdec();
          }
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(x, d_rng, mul, up);
            assert(gen.has_random());
            d_inverse.reset(new BitVector(gen.random()));
          }
          else
          {
            d_inverse.reset(new BitVector(size, *d_rng, mul, up));
          }
        }
      }
    }
    else
    {
      /**
       * inverse value:
       *   t = ones: s  = t: 1 or 0
       *             s != t: 0
       *
       *   t = 0   : 0 < s < ones: random value > s
       *             s = 0       : random value > 0
       *
       *   t is a divisior of s: t / s or s with s / x = t (0.5 prob)
       *
       *   else : s with s / x = t
       */
      if (t.is_ones())
      {
        BitVector one = BitVector::mk_one(size);
        if (s.compare(t) == 0 && x.match_fixed_bits(one)
            && (!x.match_fixed_bits(BitVector::mk_zero(size))
                || d_rng->flip_coin()))
        {
          d_inverse.reset(new BitVector(std::move(one)));
        }
        else
        {
          d_inverse.reset(new BitVector(BitVector::mk_zero(size)));
        }
      }
      else if (t.is_zero())
      {
        if (s.is_zero())
        {
          BitVector min = BitVector::mk_one(size);
          BitVector max = BitVector::mk_ones(size);
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(x, d_rng, min, max);
            assert(gen.has_random());
            d_inverse.reset(new BitVector(gen.random()));
          }
          else
          {
            d_inverse.reset(new BitVector(size, *d_rng, min, max));
          }
        }
        else
        {
          assert(!s.is_ones());
          BitVector max = BitVector::mk_ones(size);
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(x, d_rng, s.bvinc(), max);
            assert(gen.has_random());
            d_inverse.reset(new BitVector(gen.random()));
          }
          else
          {
            d_inverse.reset(new BitVector(size, *d_rng, s.bvinc(), max));
          }
        }
      }
      else
      {
        assert(s.compare(t) >= 0);
        BitVector rem = s.bvurem(t);
        BitVector div = s.bvudiv(t);
        if (d_rng->flip_coin() && rem.is_zero() && x.match_fixed_bits(div))
        {
          d_inverse.reset(new BitVector(std::move(div)));
        }
        else
        {
          /**
           * determine upper and lower bounds:
           * upper = s / t
           * lower = s / (t + 1) + 1
           */
          BitVector lo = s.bvudiv(t.bvinc()).ibvinc();
          assert(lo.compare(div) <= 0);
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(x, d_rng, lo, div);
            assert(gen.has_random());
            d_inverse.reset(new BitVector(gen.random()));
          }
          else
          {
            d_inverse.reset(new BitVector(size, *d_rng, lo, div));
          }
        }
      }
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvudiv(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvudiv(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorUdiv::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t size = x.size();

  /**
   * consistent value:
   *
   *   pos_x = 0: t = 0   : random value < ones
   *              t = ones: random value
   *              t = one : random value > 0
   *              else    : x = y * t + offset
   *                        with y in [1, ones / t]
   *                        and offset in [0, min(y - 1, ones - y * t)]
   *
   *   pos_x = 1: t = ones: 0 or 1
   *              else    : x * t such that no overflow occurs
   */

  if (d_consistent == nullptr)
  {
    if (pos_x == 0)
    {
      if (t.is_zero())
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x,
                                       d_rng,
                                       BitVector::mk_zero(size),
                                       BitVector::mk_ones(size).ibvdec());
          assert(gen.has_random());
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(size,
                                           *d_rng,
                                           BitVector::mk_zero(size),
                                           BitVector::mk_ones(size).ibvdec()));
        }
      }
      else if (t.is_ones())
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(x, d_rng);
          assert(gen.has_random());
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(size, *d_rng));
        }
      }
      else if (t.is_one())
      {
        if (x.has_fixed_bits())
        {
          BitVectorDomainGenerator gen(
              x, d_rng, BitVector::mk_one(size), x.hi());
          assert(gen.has_random());
          d_consistent.reset(new BitVector(gen.random()));
        }
        else
        {
          d_consistent.reset(new BitVector(
              size, *d_rng, BitVector::mk_one(size), BitVector::mk_ones(size)));
        }
      }
      else
      {
        if (x.has_fixed_bits())
        {
          BitVector bvres = consistent_value_pos0_aux(t);
          if (bvres.is_null())
          {
            assert(x.match_fixed_bits(t));
            d_consistent.reset(new BitVector(t));
          }
          else
          {
            d_consistent.reset(new BitVector(std::move(bvres)));
          }
        }
        else
        {
          BitVector ones = BitVector::mk_ones(size);
          /* Compute x = y * t + offset with y in [1, ones / t] and
           * offset in [0, min(y - 1, ones - y * t)].  */
          BitVector y(size, *d_rng, BitVector::mk_one(size), ones.bvudiv(t));
          assert(!y.is_umul_overflow(t));
          d_consistent.reset(new BitVector(y.bvmul(t)));

          /* Make sure that adding the offset to (y * t) does not overflow.
           * The maximum value of the offset is the minimum of
           * (y - 1, ones - (y * t)).  */
          BitVector sub = ones.bvsub(*d_consistent);
          /* Compute offset for adding to y * t. */
          BitVector offset(size,
                           *d_rng,
                           BitVector::mk_zero(size),
                           sub.compare(y.ibvdec()) < 0 ? sub : y);
          assert(!d_consistent->is_uadd_overflow(offset));
          d_consistent->ibvadd(offset);
        }
      }
    }
    else
    {
      if (t.is_ones())
      {
        BitVector one   = BitVector::mk_one(size);
        BitVector zero  = BitVector::mk_zero(size);
        bool match_one  = x.match_fixed_bits(one);
        bool match_zero = x.match_fixed_bits(zero);
        if (!match_zero || (match_one && d_rng->flip_coin()))
        {
          d_consistent.reset(new BitVector(std::move(one)));
        }
        else
        {
          assert(match_zero);
          d_consistent.reset(new BitVector(std::move(zero)));
        }
      }
      else
      {
        BitVector one = BitVector::mk_one(size);
        BitVector max = BitVector::mk_ones(size);
        if (x.has_fixed_bits())
        {
          BitVector rand;
          for (;;)
          {
            BitVectorDomainGenerator gen(x, d_rng, one, max);
            assert(gen.has_random());
            rand = gen.random();
            if (!rand.is_umul_overflow(t)) break;
            max = rand.ibvdec();
          }
          d_consistent.reset(new BitVector(std::move(rand)));
        }
        else
        {
          BitVector rand;
          for (;;)
          {
            rand = BitVector(size, *d_rng, one, max);
            if (!rand.is_umul_overflow(t)) break;
            max = rand.ibvdec();
          }
          d_consistent.reset(new BitVector(std::move(rand)));
        }
      }
    }
  }

  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
}

BitVector
BitVectorUdiv::consistent_value_pos0_aux(const BitVector& t)
{
  /* remaining solutions other than x = t:
   * min <= x <= ones with min = x->lo / t * t if x->lo / t > 1 and
   *                       min = 2 * t otherwise */

  const BitVectorDomain& x = d_children[0]->domain();
  uint32_t size            = t.size();
  BitVector one            = BitVector::mk_one(size);
  BitVector max, res;

  BitVector min = x.lo().bvudiv(t);
  if (min.compare(one) <= 0)
  {
    if (t.is_uadd_overflow(t))
    {
      /* x = t the only solution */
      return res;
    }
    min = t.bvadd(t);
  }
  else
  {
    min.ibvmul(t);
  }

  /* min / t <= s <= x->hi / t */
  BitVector ones  = BitVector::mk_ones(size);
  BitVector s_min = min.bvudiv(t);
  BitVector s_max = x.hi().bvudiv(t);
  if (s_min.compare(s_max) > 0)
  {
    s_max = ones;
  }
  for (uint32_t i = 0; i < 20; ++i)
  {
    BitVector s_tmp(size, *d_rng, s_min, s_max);
    if (s_tmp.is_umul_overflow(t))
    {
      continue;
    }
    /* for s_tmp, min = s_tmp * t and max = min + s - 1 */
    min = s_tmp.bvmul(t);
    max = s_tmp.bvadd(min);
    if (min.compare(max) > 0)
    {
      max = ones;
    }
    else
    {
      max.ibvdec();
    }
    if (x.is_fixed() && x.lo().compare(min) >= 0 && x.lo().compare(max) <= 0)
    {
      res = x.lo();
      break;
    }
    BitVectorDomainGenerator gen(x, d_rng, min, max);
    if (gen.has_random())
    {
      res = gen.random();
      break;
    }
  }
  return res;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /**
   * IC: pos_x = 0: t = 1 => (s != 0 && lo_x < s) && t = 0 => (hi_x >= s)
   *     pos_x = 1: t = 1 => (s != ones && hi_x > s) && t = 0 => (lo_x <= s)
   */
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

  /**
   * IC_wo: pos_x = 0: t = 0 || s != 0
   *        pos_x = 1: t = 0 || s != ones
   */
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC: pos_x = 0: ~t || x_lo != ones
   *     pos_x = 1: ~t || x_hi != 0
   */

  if (pos_x == 0)
  {
    return t.is_false() || !x.lo().is_ones();
  }
  return t.is_false() || !x.hi().is_zero();
}

const BitVector&
BitVectorUlt::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = s.size();
  bool is_true       = t.is_true();

  /**
   * inverse value:
   *   pos_x = 0: t = 0: random value >= s
   *              t = 1: random value < s
   *   pos_x = 1: t = 0: random value <= s
   *              t = 1: random value > s
   */

  if (pos_x == 0)
  {
    if (is_true)
    {
      assert(!s.is_zero());
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(
            x, d_rng, BitVector::mk_zero(size), s.bvdec());
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(
            new BitVector(size, *d_rng, BitVector::mk_zero(size), s.bvdec()));
      }
    }
    else
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(x, d_rng, s, BitVector::mk_ones(size));
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(
            new BitVector(size, *d_rng, s, BitVector::mk_ones(size)));
      }
    }
  }
  else
  {
    if (is_true)
    {
      assert(!s.is_ones());
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(
            x, d_rng, s.bvinc(), BitVector::mk_ones(size));
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(
            new BitVector(size, *d_rng, s.bvinc(), BitVector::mk_ones(size)));
      }
    }
    else
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainGenerator gen(x, d_rng, BitVector::mk_zero(size), s);
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(
            new BitVector(size, *d_rng, BitVector::mk_zero(size), s));
      }
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvult(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvult(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorUlt::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t size = x.size();
  bool is_ult   = t.is_true();

  /**
   * consistent value:
   *   pos_x = 0: t = 1: random value < ones
   *              t = 0: random value
   *   pos_x = 1: t = 1: random_value > 0
   *              t = 0: random value
   */

  if (pos_x == 0 && is_ult)
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainGenerator gen(x,
                                   d_rng,
                                   BitVector::mk_zero(size),
                                   BitVector::mk_ones(size).ibvdec());
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(
          new BitVector(BitVector(size,
                                  *d_rng,
                                  BitVector::mk_zero(size),
                                  BitVector::mk_ones(size).ibvdec())));
    }
  }
  else if (pos_x == 1 && is_ult)
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainGenerator gen(
          x, d_rng, BitVector::mk_one(size), BitVector::mk_ones(size));
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(new BitVector(BitVector(
          size, *d_rng, BitVector::mk_one(size), BitVector::mk_ones(size))));
    }
  }
  else
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(new BitVector(BitVector(size, *d_rng)));
    }
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /**
   * IC: pos_x = 0: t = 1 => (s != min_signed_value &&
   *                 ((MSB(x) = 0 && lo_x < s) ||
   *                  (MSB(x) != 0 && 1 o lo_x[size-2:0] < s))) &&
   *                t = 0 => ((MSB(x) = 1 && hi_x >= s) ||
   *                          (MSB(x) != 1 && 0 o hi_x[size-2:0] >= s))))
   *     pos_x = 1: t = 1 => (s != max_signed_value &&
   *                          ((MSB(x) = 1 && s < hi_x) ||
   *                           (MSB(x) != 1 && s < 0 o hi_x[size-2:0])))
   *                t = 0 => ((MSB(x) = 0 && s >= lo_x) ||
   *                          (MSB(x) != 0 && s >= 1 o lo_x[size-2:0])))
   */
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

  /**
   * IC_wo: pos_x = 0: t = 0 || s != min_signed_value
   *        pos_x = 1: t = 0 || s != max_signed_value
   */
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /**
   * CC:pos_x = 0: t = false || (const(x) => x_lo != smax)
   *    pos_x = 1: t = false || (const(x) => x_lo != smin)
   */

  if (pos_x == 0)
  {
    return t.is_false() || !x.is_fixed()
           || x.lo().compare(BitVector::mk_max_signed(x.size())) != 0;
  }
  return t.is_false() || !x.is_fixed()
         || x.lo().compare(BitVector::mk_min_signed(x.size())) != 0;
}

const BitVector&
BitVectorSlt::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = s.size();
  bool is_true       = t.is_true();

  /**
   * inverse value:
   *   pos_x = 0: t = 0: random value >=s s
   *              t = 1: random value <s s
   *   pos_x = 1: t = 0: random value <=s s
   *              t = 1: random value >s s
   */

  if (pos_x == 0)
  {
    if (is_true)
    {
      assert(!s.is_min_signed());
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, BitVector::mk_min_signed(size), s.bvdec());
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(new BitVector(
            size, *d_rng, BitVector::mk_min_signed(size), s.bvdec(), true));
      }
    }
    else
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, s, BitVector::mk_max_signed(size));
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(new BitVector(
            size, *d_rng, s, BitVector::mk_max_signed(size), true));
      }
    }
  }
  else
  {
    if (is_true)
    {
      assert(!s.is_max_signed());
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, s.bvinc(), BitVector::mk_max_signed(size));
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(new BitVector(
            size, *d_rng, s.bvinc(), BitVector::mk_max_signed(size), true));
      }
    }
    else
    {
      if (x.has_fixed_bits())
      {
        BitVectorDomainSignedGenerator gen(
            x, d_rng, BitVector::mk_min_signed(size), s);
        assert(gen.has_random());
        d_inverse.reset(new BitVector(gen.random()));
      }
      else
      {
        d_inverse.reset(new BitVector(
            size, *d_rng, BitVector::mk_min_signed(size), s, true));
      }
    }
  }

  assert(pos_x == 1 || t.compare(d_inverse->bvslt(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvslt(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

const BitVector&
BitVectorSlt::consistent_value(const BitVector& t, uint32_t pos_x)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t size = x.size();
  bool is_ult   = t.is_true();

  /**
   * consistent value:
   *   pos_x = 0: t = 1: random value <s max_signed
   *              t = 0: random value
   *   pos_x = 1: t = 1: random_value >s min_signed
   *              t = 0: random value
   */

  if (pos_x == 0 && is_ult)
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainSignedGenerator gen(
          x,
          d_rng,
          BitVector::mk_min_signed(size),
          BitVector::mk_max_signed(size).ibvdec());
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(
          new BitVector(BitVector(size,
                                  *d_rng,
                                  BitVector::mk_min_signed(size),
                                  BitVector::mk_max_signed(size).ibvdec(),
                                  true)));
    }
  }
  else if (pos_x == 1 && is_ult)
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainSignedGenerator gen(
          x,
          d_rng,
          BitVector::mk_min_signed(size).ibvinc(),
          BitVector::mk_max_signed(size));
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(
          new BitVector(BitVector(size,
                                  *d_rng,
                                  BitVector::mk_min_signed(size).ibvinc(),
                                  BitVector::mk_max_signed(size),
                                  true)));
    }
  }
  else
  {
    if (x.has_fixed_bits())
    {
      BitVectorDomainGenerator gen(x, d_rng);
      assert(gen.has_random());
      d_consistent.reset(new BitVector(gen.random()));
    }
    else
    {
      d_consistent.reset(new BitVector(BitVector(size, *d_rng)));
    }
  }
  assert(x.match_fixed_bits(*d_consistent));
  return *d_consistent;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s           = 1 - pos_x;
  const BitVector& s       = d_children[pos_s]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();
  bool ic_wo;

  /**
   * IC_wo: pos_x = 0: ~(-s) >= t
   *        pos_x = 1: (t + t - s) & s >= t
   */
  if (pos_x == 0)
  {
    ic_wo = s.bvneg().ibvnot().compare(t) >= 0;
  }
  else
  {
    assert(pos_x == 1);
    ic_wo = t.bvadd(t).ibvsub(s).ibvand(s).compare(t) >= 0;
  }

  /**
   * IC: pos_x = 0: IC_wo &&
   *                ((s = 0 || t = ones) => mfb(x, t)) &&
   *                ((s != 0 && t != ones) => \exists y. (
   *                    mfb(x, s * y + t) && !umulo(s, y) && !uaddo(s *y, t)))
   *     pos_x = 1: IC_wo &&
   *                (s = t => (lo_x = 0 || hi_x > t)) &&
   *                (s != t => \exists y. (
   *                    mfb(x, y) && y > t && (s - t) mod y = 0)
   */
  if (ic_wo && x.has_fixed_bits())
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
          uint32_t size    = x.size();
          BitVector ones = BitVector::mk_ones(size);
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
                d_inverse.reset(new BitVector(std::move(bv)));
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
        d_inverse.reset(new BitVector(std::move(bv)));
        return true;
      }
      return false;
    }
    return true;
  }

  return ic_wo;
}

bool
BitVectorUrem::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  if (!x.has_fixed_bits()) return true;

  /* CC: pos_x = 0: (t = ones => mfb(x, ones)) &&
   *                (t != ones =>
   *                  (t > (ones - t) => mfb (x, t)) &&
   *                  (t < (ones - t) => mfb(x, t) ||
   *                   \exists y. (mfb(x, y) && y> 2*t))
   *
   *     pos_x = 1: mfb(x, 0) ||
   *                ((t = ones => mfb(x, 0)) &&
   *                 (t != ones => \exists y. (mfb(x, y) && y > t))) */

  bool t_is_ones = t.is_ones();
  uint32_t size  = t.size();

  if (pos_x == 0)
  {
    bool mfb = x.match_fixed_bits(t);

    if (t_is_ones && !mfb) return false;

    int32_t cmp_t = t.compare(BitVector::mk_ones(size).ibvsub(t));

    if (cmp_t > 0 && !mfb)
    {
      return false;
    }

    if (cmp_t < 0 && !mfb)
    {
      /* x > t:
       * pick s > t such that x = s + t does not overflow -> t < s < ones - t
       * -> 2*t + 1 <= x <= ones */
      BitVector bvres = consistent_value_pos0_aux(t);
      bool res        = !bvres.is_null();
      if (res)
      {
        d_consistent.reset(new BitVector(bvres));
      }
      return res;
    }
  }
  else
  {
    if (!x.match_fixed_bits(BitVector::mk_zero(size)))
    {
      if (t_is_ones)
      {
        return false;
      }
      BitVector min = t.bvinc();
      if (x.is_fixed() && x.lo().compare(min) >= 0)
      {
        return true;
      }
      BitVectorDomainGenerator gen(x, d_rng, min, x.hi());
      bool res = gen.has_random();
      if (res)
      {
        d_consistent.reset(new BitVector(gen.random()));
      }
      return res;
    }
  }
  return true;
}

const BitVector&
BitVectorUrem::inverse_value(const BitVector& t, uint32_t pos_x)
{
  return inverse_value(t, pos_x, 0);
}

const BitVector&
BitVectorUrem::inverse_value(const BitVector& t,
                             uint32_t pos_x,
                             uint32_t n_tries)
{
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();
  uint32_t size      = t.size();

  if (d_inverse == nullptr)
  {
    if (pos_x == 0)
    {
      /**
       * inverse value:
       *   s = 0: t
       *   else : - t
       *          - s * n + b
       *            with n such that (s * n + b) does not overflow
       */

      assert(t.is_zero() || !s.is_one());
      if (s.is_zero())
      {
        d_inverse.reset(new BitVector(t));
      }
      else
      {
        assert(s.compare(t) > 0);
        if (d_rng->flip_coin() && x.match_fixed_bits(t))
        {
          d_inverse.reset(new BitVector(t));
        }
        else
        {
          BitVector ones = BitVector::mk_ones(size);
          if (ones.bvsub(s).compare(t) < 0)
          {
            /* overflow for n = 1 -> only simplest solution (t) possible */
            assert(x.match_fixed_bits(t));
            d_inverse.reset(new BitVector(t));
          }
          else
          {
            BitVector zero = BitVector::mk_zero(size);
            /**
             * upper and lower bounds for n such that s * n + t does not
             * overflow in the multiplication and addition:
             *   lo = 0
             *   up = (ones - t) / s
             */
            BitVector up = ones.bvudiv(s);
            BitVector n(size, *d_rng, zero, up);
            /* choose n such that addition in s * n + t does not overflow */
            BitVector mul = s.bvmul(n);
            for (uint32_t i = 0; n_tries == 0 || i < n_tries; ++i)
            {
              if (ones.bvsub(mul).compare(t) >= 0
                  && x.match_fixed_bits(mul.ibvadd(t)))
              {
                d_inverse.reset(new BitVector(std::move(mul)));
                break;
              }
              n   = BitVector(size, *d_rng, zero, up);
              mul = s.bvmul(n);
            }
            if (d_inverse == nullptr && x.match_fixed_bits(t))
            {
              d_inverse.reset(new BitVector(t));
            }
          }
          assert(d_inverse->compare(t) >= 0);
        }
      }
    }
    else
    {
      /**
       * inverse value:
       *   t = ones: 0
       *   s = t   : 0 or random value > t
       *   s > t   : ((s - t) / n) > t
       */
      if (t.is_ones())
      {
        assert(s.is_ones());
        d_inverse.reset(new BitVector(BitVector::mk_zero(size)));
      }
      else if (s.compare(t) == 0)
      {
        BitVector zero = BitVector::mk_zero(size);
        if (d_rng->pick_with_prob(250) && x.match_fixed_bits(zero))
        {
          d_inverse.reset(new BitVector(std::move(zero)));
        }
        else
        {
          if (x.has_fixed_bits())
          {
            BitVectorDomainGenerator gen(
                x, d_rng, t.bvinc(), BitVector::mk_ones(size));
            if (!gen.has_random())
            {
              assert(x.match_fixed_bits(zero));
              d_inverse.reset(new BitVector(std::move(zero)));
            }
            else
            {
              d_inverse.reset(new BitVector(gen.random()));
            }
          }
          else
          {
            d_inverse.reset(new BitVector(
                size, *d_rng, t.bvinc(), BitVector::mk_ones(size)));
          }
        }
      }
      else
      {
        assert(s.compare(t) > 0);
        assert(t.is_zero() || t.compare(s.bvdec()) != 0);

        BitVector sub = s.bvsub(t);
        assert(sub.compare(t) > 0);

        if (d_rng->flip_coin() && x.match_fixed_bits(sub))
        {
          d_inverse.reset(new BitVector(std::move(sub)));
        }
        else
        {
          /**
           * 1 <= n < (s - t) / t (non-truncating)
           * Note: div truncates towards 0!
           *
           * Upper and lower bounds for n:
           * lower = 1
           * upper = s               if t = 0
           *         (s - t) / t - 1 if (s - t) % t = 0
           *         (s - t) / t     if (s - t) % t > 0
           */
          BitVector up;
          if (t.is_zero())
          {
            up = s;
          }
          else
          {
            BitVector rem;
            sub.bvudivurem(t, &up, &rem);
            assert(!up.is_null());
            assert(!rem.is_null());
            if (rem.is_zero())
            {
              /* (s - t) / t is not truncated (remainder is 0) and is therefore
               * the EXclusive upper bound, the inclusive upper bound is:
               * upper = (s - t) / t - 1  */
              up.ibvdec();
            }
          }

          if (up.is_zero())
          {
            d_inverse.reset(new BitVector(std::move(sub.ibvdec())));
          }
          else
          {
            /* choose n such that (s - t) % n = 0 */
            BitVector one = BitVector::mk_one(size);
            BitVector n(size, *d_rng, one, up);
            BitVector rem = sub.bvurem(n);
            for (uint32_t i = 0; n_tries == 0 || i < n_tries; ++i)
            {
              n   = BitVector(size, *d_rng, one, up);
              rem = sub.bvurem(n);
              if (rem.is_zero())
              {
                BitVector div = sub.bvudiv(n);
                if (x.match_fixed_bits(div))
                {
                  /* result: s - t / n */
                  d_inverse.reset(new BitVector(std::move(div)));
                  break;
                }
              }
            }
            if (d_inverse == nullptr && x.match_fixed_bits(sub))
            {
              /* fall back to n = 1 */
              d_inverse.reset(new BitVector(std::move(sub)));
            }
          }
        }
      }
    }
  }

  assert(n_tries != 0 || d_inverse != nullptr);
  assert(d_inverse == nullptr || pos_x == 1
         || t.compare(d_inverse->bvurem(s)) == 0);
  assert(d_inverse == nullptr || pos_x == 0
         || t.compare(s.bvurem(*d_inverse)) == 0);
  assert(d_inverse == nullptr || x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

BitVector
BitVectorUrem::consistent_value_pos0_aux(const BitVector& t)
{
  /* x > t:
   * pick s > t such that x = s + t does not overflow -> t < s < ones - t
   * -> 2*t + 1 <= x <= ones */
  const BitVectorDomain& x = d_children[0]->domain();
  BitVector min            = t.bvinc();
  assert(!min.is_uadd_overflow(t));
  min.ibvadd(t);
  if (x.is_fixed() && x.lo().compare(min) >= 0)
  {
    return x.lo();
  }
  BitVectorDomainGenerator gen(x, d_rng, min, x.hi());
  if (gen.has_random())
  {
    return gen.random();
  }
  return BitVector();
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();

  /** IC_wo: true */
  if (!x.has_fixed_bits()) return true;

  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /** IC: mfb(x, s^t) */
  return x.match_fixed_bits(s.bvxor(t));
}

bool
BitVectorXor::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /** CC: true */
  (void) t;
  (void) pos_x;
  return true;
}

const BitVector&
BitVectorXor::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

#ifndef NDEBUG
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
#endif
  uint32_t pos_s     = 1 - pos_x;
  const BitVector& s = d_children[pos_s]->assignment();

  /** inverse value: s ^ t */
  d_inverse.reset(new BitVector(s.bvxor(t)));

  assert(pos_x == 1 || t.compare(d_inverse->bvxor(s)) == 0);
  assert(pos_x == 0 || t.compare(s.bvxor(*d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  uint32_t pos_s0          = pos_x == 0 ? 1 : 0;
  uint32_t pos_s1          = pos_x == 2 ? 1 : 2;
  const BitVector& s0      = d_children[pos_s0]->assignment();
  const BitVector& s1      = d_children[pos_s1]->assignment();
  const BitVectorDomain& x = d_children[pos_x]->domain();

  /**
   * IC: pos_x = 0: (!is_fixed(x) && (s0 = t || s1 = t)) ||
   *                (is_fixed_true(x) && s0 = t) ||
   *                (is_fixed_false(x) && s1 = t)
   *                with s0 the value for '_t' and s1 the value for '_e'
   *     pos_x = 1: (s0 = true && mfb(x, t)) ||
   *                (s0 = false && s1 = t)
   *                with s0 the value for '_c' and s1 the value for '_e'
   *     pos_x = 2: (s0 == false && mfb(x, t)) ||
   *                (s1 == true && s1 = t)
   *                with s0 the value for '_c' and s1 the value for '_t'
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
      return (s0.is_true() && x.match_fixed_bits(t))
             || (s0.is_false() && s1.compare(t) == 0);
    }
    assert(pos_x == 2);
    return (s0.is_false() && x.match_fixed_bits(t))
           || (s0.is_true() && s1.compare(t) == 0);
  }

  /**
   * IC_wo: pos_x = 0: s0 == t || s1 == t
   *                   with s0 the value for the '_t' branch
   *                   and s1 the value for the '_e' branch
   *        pos_x = 1: s0 == true
   *                   with s0 the value for condition '_c'
   *        pos_x = 2: s0 == false
   *                   with s0 the value for condition '_c'
   */
  if (pos_x == 0)
  {
    return s0.compare(t) == 0 || s1.compare(t) == 0;
  }
  if (pos_x == 1)
  {
    return s0.is_true() || s1.compare(t) == 0;
  }
  assert(pos_x == 2);
  return s0.is_false() || s1.compare(t) == 0;
}

bool
BitVectorIte::is_consistent(const BitVector& t, uint32_t pos_x)
{
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  /** CC: true */
  (void) t;
  (void) pos_x;
  return true;
}

const BitVector&
BitVectorIte::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  uint32_t pos_s0     = pos_x == 0 ? 1 : 0;
  uint32_t pos_s1     = pos_x == 2 ? 1 : 2;
  const BitVector& s0 = d_children[pos_s0]->assignment();
  const BitVector& s1 = d_children[pos_s1]->assignment();

  /**
   * inverse value:
   *   pos_x = 0: t = 0: random value >=s s
   *              t = 1: random value <s s
   *   pos_x = 1: t = 0: random value <=s s
   *              t = 1: random value >s s
   */

  if (pos_x == 0)
  {
    int32_t cmp0 = s0.compare(t) == 0;
    int32_t cmp1 = s1.compare(t) == 0;
    if (cmp0 && cmp1)
    {
      if (x.has_fixed_bits())
      {
        if (d_rng->flip_coin())
        {
          BitVector bv = BitVector::mk_true();
          if (x.match_fixed_bits(bv))
          {
            d_inverse.reset(new BitVector(std::move(bv)));
          }
          else
          {
            d_inverse.reset(new BitVector(BitVector::mk_false()));
          }
        }
        else
        {
          d_inverse.reset(new BitVector(BitVector::mk_false()));
        }
      }
      else
      {
        d_inverse.reset(new BitVector(
            d_rng->flip_coin() ? BitVector::mk_true() : BitVector::mk_false()));
      }
    }
    else if (cmp0)
    {
      d_inverse.reset(new BitVector(BitVector::mk_true()));
    }
    else
    {
      assert(cmp1);
      d_inverse.reset(new BitVector(BitVector::mk_false()));
    }
  }
  else if ((pos_x == 1 && s0.is_zero()) || (pos_x == 2 && s0.is_one()))
  {
    /* return current assignment for disabled branch */
    d_inverse.reset(new BitVector(d_children[pos_x]->assignment()));
  }
  else
  {
    d_inverse.reset(new BitVector(t));
  }

  assert(pos_x != 0 || t.compare(BitVector::bvite(*d_inverse, s0, s1)) == 0);
  assert(pos_x != 1 || t.compare(BitVector::bvite(s0, *d_inverse, s1)) == 0);
  assert(pos_x != 2 || t.compare(BitVector::bvite(s0, s1, *d_inverse)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  (void) pos_x;

  const BitVectorDomain& x = d_children[pos_x]->domain();

  /** IC_wo: true */
  if (!x.has_fixed_bits()) return true;
  // TODO: maybe we should cache the domain extraction
  /** IC: mfb(x[hi:lo], t) */
  return x.bvextract(d_hi, d_lo).match_fixed_bits(t);
}

bool
BitVectorExtract::is_consistent(const BitVector& t, uint32_t pos_x)
{
  /** CC: IC */
  return is_invertible(t, pos_x);
}

const BitVector&
BitVectorExtract::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse == nullptr);
  (void) pos_x;

  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
  const BitVector& x_val = d_children[pos_x]->assignment();

  /**
   * inverse value: x[msb: hi+1] o t o x[lo-1:0]
   *
   * We choose with probability s_prob_keep if we keep the current assignment
   * of the don't care bits, i.e., all bits that are not determined by t, or if
   * we set them randomly.
   */

  uint32_t size = x.size();
  bool keep     = d_rng->pick_with_prob(s_prob_keep);
  BitVector left, propagated, right;

  if (d_hi < size - 1)
  {
    if (keep)
    {
      left = x_val.bvextract(size - 1, d_hi + 1);
    }
    else
    {
      if (x.has_fixed_bits())
      {
        if (d_x_slice_left == nullptr)
        {
          d_x_slice_left.reset(
              new BitVectorDomain(x.bvextract(size - 1, d_hi + 1)));
        }
        if (d_x_slice_left->is_fixed())
        {
          left = d_x_slice_left->lo();
        }
        else
        {
          BitVectorDomainGenerator gen(*d_x_slice_left, d_rng);
          assert(gen.has_random());
          left = gen.random();
        }
      }
      else
      {
        left = BitVector(size - 1 - d_hi, *d_rng);
      }
    }
  }

  if (d_lo > 0)
  {
    if (keep)
    {
      right = x_val.bvextract(d_lo - 1, 0);
    }
    else
    {
      if (x.has_fixed_bits())
      {
        if (d_x_slice_right == nullptr)
        {
          d_x_slice_right.reset(new BitVectorDomain(x.bvextract(d_lo - 1, 0)));
        }
        if (d_x_slice_right->is_fixed())
        {
          right = d_x_slice_right->lo();
        }
        else
        {
          BitVectorDomainGenerator gen(*d_x_slice_right, d_rng);
          assert(gen.has_random());
          right = gen.random();
        }
      }
      else
      {
        right = BitVector(d_lo, *d_rng);
      }
    }
  }

  if (left.is_null())
  {
    if (right.is_null())
    {
      d_inverse.reset(new BitVector(t));
    }
    else
    {
      d_inverse.reset(new BitVector(t.bvconcat(right)));
    }
  }
  else if (right.is_null())
  {
    d_inverse.reset(new BitVector(left.bvconcat(t)));
  }
  else
  {
    d_inverse.reset(new BitVector(left.bvconcat(t).ibvconcat(right)));
  }

  assert(t.compare(d_inverse->bvextract(d_hi, d_lo)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
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
  d_inverse.reset(nullptr);
  d_consistent.reset(nullptr);

  (void) pos_x;

  const BitVectorDomain& x = d_children[pos_x]->domain();
  uint32_t size            = t.size();
  BitVector t_x            = t.bvextract(size - 1 - d_n, 0);
  BitVector t_ext          = t.bvextract(size - 1, size - 1 - d_n);

  /**
   * IC_wo: t_ext == ones || t_ext == zero
   *         and t_x   = t[t_size - 1 - n : 0]
   *         and t_ext = t[t_size - 1, t_size - 1 - n]
   *         (i.e., it includes MSB of t_x)
   */
  bool ic_wo = t_ext.is_zero() || t_ext.is_ones();

  /** IC: IC_wo && mfb(x, t_x) */
  if (ic_wo && x.has_fixed_bits())
  {
    ic_wo = x.match_fixed_bits(t_x);
  }
  if (ic_wo) d_inverse.reset(new BitVector(t_x));

  return ic_wo;
}

bool
BitVectorSignExtend::is_consistent(const BitVector& t, uint32_t pos_x)
{
  /** CC: IC */
  return is_invertible(t, pos_x);
}

const BitVector&
BitVectorSignExtend::inverse_value(const BitVector& t, uint32_t pos_x)
{
  assert(d_inverse != nullptr);
  (void) t;
  (void) pos_x;
#ifndef NDEBUG
  const BitVectorDomain& x = d_children[pos_x]->domain();
  assert(!x.is_fixed());
#endif
  assert(t.compare(d_inverse->bvsext(d_n)) == 0);
  assert(x.match_fixed_bits(*d_inverse));
  return *d_inverse;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzlals
