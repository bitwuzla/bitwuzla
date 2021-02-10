#ifndef BZLALS__BITVECTOR_OP_H
#define BZLALS__BITVECTOR_OP_H

#include "bitvector.h"
#include "bitvector_domain.h"

namespace bzlals {

class RNG;

/* -------------------------------------------------------------------------- */

class BitVectorOp
{
 public:
  /** Constructor. */
  BitVectorOp(RNG* rng, uint32_t size, BitVectorOp* child0);
  BitVectorOp(RNG* rng,
              uint32_t size,
              BitVectorOp* child0,
              BitVectorOp* child1);
  BitVectorOp(RNG* rng,
              uint32_t size,
              BitVectorOp* child0,
              BitVectorOp* child1,
              BitVectorOp* child2);
  BitVectorOp(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain,
              BitVectorOp* child0);
  BitVectorOp(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain,
              BitVectorOp* child0,
              BitVectorOp* child1);
  BitVectorOp(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain,
              BitVectorOp* child0,
              BitVectorOp* child1,
              BitVectorOp* child2);
  /** Destructor. */
  virtual ~BitVectorOp() {}

  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   */
  virtual bool is_invertible(const BitVector& t, uint32_t pos_x) = 0;
  /**
   * Check consistency condition for x at index pos_x with respect to constant
   * bits and target value t.
   */
  virtual bool is_consistent(const BitVector& t, uint32_t pos_x) = 0;

  /** Get the cached inverse result. */
  virtual BitVector* inverse() { return nullptr; }
  /** Get the cached consistent result. */
  virtual BitVector* consistent() { return nullptr; }

  /** Get child at given index. */
  BitVectorOp* operator[](uint32_t pos) const;

  /** Return the arity of this operation. */
  uint32_t arity() const { return d_arity; }
  /** Get the assignment of this operation. */
  const BitVector& assignment() const { return d_assignment; }
  /** Get the domain of this operation. */
  const BitVectorDomain& domain() const { return d_domain; }

 protected:
  std::unique_ptr<BitVectorOp*[]> d_children = nullptr;
  RNG* d_rng                                 = nullptr;
  uint32_t d_arity                           = 2;
  BitVector d_assignment;
  BitVectorDomain d_domain;
};

/* -------------------------------------------------------------------------- */

class BitVectorAdd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAdd(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorAdd(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o  const bits: true
   *   with const bits: mfb(x, t - s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * IC:
   *   w/o  const bits: true
   *   with const bits: true
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorAnd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAnd(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorAnd(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo): (t & s) = t
   *   with const bits       : IC_wo && ((s & x_hi) & m) = (t & m)
   *                         with m = ~(x_lo ^ x_hi)
   *                              ... mask out all non-const bits
   * Intuition:
   * 1) x & s = t on all const bits of x
   * 2) s & t = t on all non-const bits of x
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: t & x_hi = t
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;
};

/* -------------------------------------------------------------------------- */

class BitVectorConcat : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorConcat(RNG* rng,
                  uint32_t size,
                  BitVectorOp* child0,
                  BitVectorOp* child1);
  BitVectorConcat(RNG* rng,
                  const BitVector& assignment,
                  const BitVectorDomain& domain,
                  BitVectorOp* child0,
                  BitVectorOp* child1);
  /**
   * x o s = tx o ts
   * s o x = ts o tx
   *
   * IC:
   *   w/o  const bits: s = ts
   *     pos_x = 0: ts = t[bw(s) - 1 : 0]
   *     pos_x = 1: ts = t[bw(t) - 1 : bw(t) - bw(s)]
   *
   * with const bits: mfb(x, tx) && s = ts
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *
   *   with const bits: mfb(x, tx)
   *     pos_x = 0: tx = t[bw(t) - 1 : bw(t) - bw(x)]
   *     pos_x = 1: tx = t[bw(x) - 1 : 0]
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorEq : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorEq(RNG* rng,
              uint32_t size,
              BitVectorOp* child0,
              BitVectorOp* child1);
  BitVectorEq(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain,
              BitVectorOp* child0,
              BitVectorOp* child1);
  /**
   * IC:
   *   w/o  const bits: true
   *   with const bits:
   *    t = 0: (x_hi != x_lo) || (x_hi != s)
   *    t = 1: mfb(x, s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: true
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;
};

/* -------------------------------------------------------------------------- */

class BitVectorMul : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorMul(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorMul(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo): ((-s | s) & t) = t
   *   with const bits       : IC_wo &&
   *                           (s = 0 ||
   *                            ((odd(s) => mfb(x, t * s^-1)) &&
   *                             (!odd(s) => mfb (x << c, y << c))))
   *                    with c = ctz(s) and y = (t >> c) * (s >> c)^-1
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: (t != 0 => x_hi != 0) &&
   *                    (odd(t) => x_hi[lsb] != 0) &&
   *                    (!odd(t) => \exists y. (mfb(x, y) && ctz(t) >= ctz(y))
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override
  {
    return nullptr; /* TODO choose from d_inverse */
  }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorShl : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorShl(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorShl(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: (t >> s) << s = t
   *       pos_x = 1: ctz(s) <= ctz(t) &&
   *                  ((t = 0) || (s << (ctz(t) - ctz(s))) = t)
   *
   *   with const bits:
   *       pos_x = 0: IC_wo && mfb(x << s, t)
   *       pos_x = 1: IC_wo &&
   *                  ((t = 0) => (x_hi >= ctz(t) - ctz(s) || (s = 0))) &&
   *                  ((t != 0) => mfb(x, ctz(t) - ctz(s)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits:
   *     pos_x = 0: \exists y. (y <= ctz(t) && mfb(x << y, t))
   *     pos_x = 1: t = 0 || \exists y. (y <= ctz(t) && mfb(x, y))
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorShr : public BitVectorOp
{
 public:
  /**
   * Additional interface / helper for is_invertible.
   * Cached result is stored in 'inverse'.
   */
  static bool is_invertible(RNG* rng,
                            const BitVector& t,
                            const BitVector& s,
                            const BitVectorDomain& x,
                            uint32_t pos_x,
                            std::unique_ptr<BitVector>& inverse);

  /** Constructors. */
  BitVectorShr(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorShr(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);

  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: (t << s) >> s = t
   *       pos_x = 1: clz(s) <= clz(t) &&
   *                  ((t = 0) || (s >> (clz(t) - clz(s))) = t)
   *
   *   with const bits:
   *       pos_x = 0: IC_wo && mfb(x >> s, t)
   *       pos_x = 1: IC_wo &&
   *                  ((t = 0) => (x_hi >= clz(t) - clz(s) || (s = 0))) &&
   *                  ((t != 0) => mfb(x, clz(t) - clz(s)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits:
   *     pos_x = 0: \exists y. (y <= clz(t) && mfb(x >> y, t))
   *     pos_x = 1: t = 0 || \exists y. (y <= clz(t) && mfb(x, y))
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorAshr : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAshr(RNG* rng,
                uint32_t size,
                BitVectorOp* child0,
                BitVectorOp* child1);
  BitVectorAshr(RNG* rng,
                const BitVector& assignment,
                const BitVectorDomain& domain,
                BitVectorOp* child0,
                BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: (s < bw(s) => (t << s) >>a s = t) &&
   *                  (s >= bw(s) => (t = ones || t = 0))
   *       pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
   *                  (s[msb] = 1 => IC_shr(~s >> x = ~t))
   *
   *   with const bits:
   *       pos_x = 0: IC_wo && mfb(x >>a s, t)
   *       pos_x = 1: IC_wo &&
   *                  (s[msb ] = 0 => IC_shr) &&
   *                  (s[msb] = 1 => IC_shr(~s >> x = ~t))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits:
   *     pos_x = 0:
   *     ((t = 0 || t = ones) => \exists y. (y[msb] = t[msb] && mfb(x, y))) &&
   *     ((t != 0 && t != ones) => \exists y. (
   *        c => y <= clo(t) && ~c => y <= clz(t) && mfb(x, y))
   *     with c = ((t << y)[msb] = 1)
   *
   *     pos_x = 1:
   *     t = 0 || t = ones ||
   *     \exists y. (c => y < clo(t) && ~c => y < clz(t) && mfb(x, y)
   *     with c = (t[msb] = 1)
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorUdiv : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorUdiv(RNG* rng,
                uint32_t size,
                BitVectorOp* child0,
                BitVectorOp* child1);
  BitVectorUdiv(RNG* rng,
                const BitVector& assignment,
                const BitVectorDomain& domain,
                BitVectorOp* child0,
                BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: (s * t) / s = t
   *       pos_x = 1: s / (s / t) = t
   *
   *   with const bits:
   *       pos_x = 0: IC_wo &&
   *                  (t = 0 => x_lo < s) &&
   *                  ((t != 0 && s != 0 ) => \exists y. (
   *                    mfb(x, y) && (~c => y < s * t + 1) && (c => y <= ones)))
   *                  with c = umulo(s, t + 1) && uaddo(t, 1)
   *       pos_x = 1: IC_wo &&
   *                  (t != ones => x_hi > 0) &&
   *                  ((s != 0 || t != 0) => (s / x_hi <= t) && \exists y. (
   *                      mfb(x, y) &&
   *                      (t = ones => y <= s / t) &&
   *                      (t != ones => y > t + 1 && y <= s / t)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *
   *   with const bits:
   *     pos_x = 0:
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
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override
  {
    return nullptr; /* TODO choose from d_inverse */
  }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

 private:
  /**
   * Try to find a consistent value for pos_x = 0 other than x = t.
   * Returns a null bit-vector if no such value can be found.
   */
  BitVector consistent_value_pos0_aux(const BitVector& t);
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorUlt : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorUlt(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorUlt(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: t = 0 || s != 0
   *       pos_x = 1: t = 0 || s != ones
   *
   *   with const bits:
   *       pos_x = 0: t = 1 => (s != 0 && x_lo < s) && t = 0 => (x_hi >= s)
   *       pos_x = 1: t = 1 => (s != ones && x_hi > s) && t = 0 => (x_lo <= s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: pos_x = 0: t = false || x_lo != ones
   *                    pos_x = 1: t = false || x_hi != 0
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;
};

/* -------------------------------------------------------------------------- */

class BitVectorSlt : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorSlt(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorSlt(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: t = 0 || s != min_signed_value
   *       pos_x = 1: t = 0 || s != max_signed_value
   *
   *   with const bits:
   *       pos_x = 0: t = 1 => (s != min_signed_value &&
   *                   ((MSB(x) = 0 && x_lo < s) ||
   *                    (MSB(x) != 0 && 1 o x_lo[bw-2:0] < s))) &&
   *                  t = 0 => ((MSB(x) = 1 && x_hi >= s) ||
   *                            (MSB(x) != 1 && 0 o x_hi[bw-2:0] >= s))))
   *       pos_x = 1: t = 1 => (s != max_signed_value &&
   *                            ((MSB(x) = 1 && s < x_hi) ||
   *                             (MSB(x) != 1 && s < 0 o x_hi[bw-2:0])))
   *                  t = 0 => ((MSB(x) = 0 && s >= x_lo) ||
   *                            (MSB(x) != 0 && s >= 1 o x_lo[bw-2:0])))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: pos_x = 0: t = false || (const(x) => x_lo != smax)
   *                    pos_x = 1: t = false || (const(x) => x_lo != smin)
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;
};

/* -------------------------------------------------------------------------- */

class BitVectorUrem : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorUrem(RNG* rng,
                uint32_t size,
                BitVectorOp* child0,
                BitVectorOp* child1);
  BitVectorUrem(RNG* rng,
                const BitVector& assignment,
                const BitVectorDomain& domain,
                BitVectorOp* child0,
                BitVectorOp* child1);
  /**
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: ~(-s) >= t
   *       pos_x = 1: (t + t - s) & s >= t
   *
   *   with const bits:
   *       pos_x = 0: IC_wo &&
   *                  ((s = 0 || t = ones) => mfb(x, t)) &&
   *                  ((s != 0 && t != ones) => \exists y. (
   *                      mfb(x, s * y + t) && !umulo(s, y) && !uaddo(s *y, t)))
   *       pos_x = 1: IC_wo &&
   *                  (s = t => (x_lo = 0 || x_hi > t)) &&
   *                  (s != t => \exists y. (
   *                      mfb(x, y) && y > t && (s - t) mod y = 0)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *  w/o  const bits: true
   *
   *  with const bits:
   *     pos_x = 0: (t = ones => mfb(x, ones)) &&
   *                (t != ones =>
   *                  (t > (ones - t) => mfb (x, t)) &&
   *                  (t < (ones - t) => mfb(x, t) ||
   *                   \exists y. (mfb(x, y) && y> 2*t))
   *
   *     pos_x = 1: mfb(x, 0) ||
   *                ((t = ones => mfb(x, 0)) &&
   *                 (t != ones => \exists y. (mfb(x, y) && y > t)))
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override
  {
    return nullptr; /* TODO choose from d_inverse */
  }

  /** Get the cached consistent result. */
  BitVector* consistent() override { return d_consistent.get(); }

 private:
  /**
   * Pick a consistent value for pos_x = 0 with x > t.
   * Returns a null bit-vector if no such value can be found.
   */
  BitVector consistent_value_pos0_aux(const BitVector& t);
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
  /** Cached consistent result. */
  std::unique_ptr<BitVector> d_consistent = nullptr;
};

/* -------------------------------------------------------------------------- */

class BitVectorXor : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorXor(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1);
  BitVectorXor(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1);
  /**
   * IC:
   *   w/o  const bits: true
   *   with const bits: mfb(x, s^t)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: TODO
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;
};

/* -------------------------------------------------------------------------- */

class BitVectorIte : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorIte(RNG* rng,
               uint32_t size,
               BitVectorOp* child0,
               BitVectorOp* child1,
               BitVectorOp* child2);
  BitVectorIte(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain,
               BitVectorOp* child0,
               BitVectorOp* child1,
               BitVectorOp* child2);
  /**
   * ite(_c, _t, _e)
   *
   * IC:
   *   w/o const bits (IC_wo):
   *       pos_x = 0: s0 == t || s1 == t
   *                  with s0 the value for '_t' branch
   *                  and s1 the value for '_e'
   *       pos_x = 1: s0 == true
   *                  with s0 the value for '_c'
   *       pos_x = 2: s0 == false
   *                  with s0 the value for '_c'
   *
   *   with const bits:
   *       pos_x = 0: (!is_fixed(x) && (s0 = t || s1 = t)) ||
   *                  (is_fixed_true(x) && s0 = t) ||
   *                  (is_fixed_false(x) && s1 = t)
   *                  with s0 the value for '_t' and s1 the value for '_e'
   *       pos_x = 1: s0 = true && mfb(x, t)
   *                  with s0 the value for '_c'
   *       pos_x = 2: s0 == false && mfb(x, t)
   *                  with s0 the value for '_c'
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: TODO
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override
  {
    return nullptr; /* TODO choose from d_inverse */
  }
};

/* -------------------------------------------------------------------------- */

class BitVectorExtract : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorExtract(
      RNG* rng, uint32_t size, BitVectorOp* child0, uint32_t hi, uint32_t lo);
  BitVectorExtract(RNG* rng,
                   const BitVector& assignment,
                   const BitVectorDomain& domain,
                   BitVectorOp* child0,
                   uint32_t hi,
                   uint32_t lo);
  /**
   * IC:
   *   w/o  const bits: true
   *   with const bits: mfb(x[hi:lo], t)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: TODO
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

 private:
  /** The upper index. */
  uint32_t d_hi;
  /** The lower index. */
  uint32_t d_lo;
};

/* -------------------------------------------------------------------------- */

class BitVectorSignExtend : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorSignExtend(RNG* rng, uint32_t size, BitVectorOp* child0, uint32_t n);
  BitVectorSignExtend(RNG* rng,
                      const BitVector& assignment,
                      const BitVectorDomain& domain,
                      BitVectorOp* child0,
                      uint32_t n);
  /**
   * IC:
   *   w/o  const bits (IC_wo): t_ext == ones || t_ext == zero
   *                            and t_x   = t[t_size - 1 - n : 0]
   *                            and t_ext = t[t_size - 1, t_size - 1 - n]
   *                            (i.e., it includes MSB of t_x)
   *
   *   with const bits: IC_wo && mfb(x, t_x)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x) override;

  /**
   * CC:
   *   w/o  const bits: true
   *   with const bits: TODO
   */
  bool is_consistent(const BitVector& t, uint32_t pos_x) override;

  /** Get the cached inverse result. */
  BitVector* inverse() override { return d_inverse.get(); }

 private:
  /** The number of bits to extend with. */
  uint32_t d_n;
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

/* -------------------------------------------------------------------------- */

}  // namespace bzlals
#endif
