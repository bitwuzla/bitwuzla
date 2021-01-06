#ifndef BZLALS__BITVECTOR_OP_H
#define BZLALS__BITVECTOR_OP_H

#include "bitvector.h"
#include "bitvector_domain.h"

namespace bzlals {

class RNG;

class BitVectorOp
{
 public:
  /** Constructor. */
  BitVectorOp(RNG* rng, uint32_t size);
  BitVectorOp(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain);
  /** Destructor. */
  virtual ~BitVectorOp() {}

  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   */
  virtual bool is_invertible(const BitVector& t, uint32_t pos_x) = 0;

  /** Access child at given index. */
  BitVectorOp*& operator[](uint32_t pos) const;

  /** Return the arity of this operation. */
  uint32_t arity() const { return 2; }
  /** Get the assignment of this operation. */
  const BitVector& assignment() const { return d_assignment; }
  /** Get the domain of this operation. */
  const BitVectorDomain& domain() const { return d_domain; }

 protected:
  std::unique_ptr<BitVectorOp*[]> d_children = nullptr;
  RNG* d_rng                                 = nullptr;
  BitVector d_assignment;
  BitVectorDomain d_domain;
};

class BitVectorAdd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAdd(RNG* rng, uint32_t size);
  BitVectorAdd(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: true
   * with const bits: mfb(x, t - s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorAnd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAnd(RNG* rng, uint32_t size);
  BitVectorAnd(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: (t & s) = t
   * with const bits: (t & s) = t && ((s & hi_x) & m) = (t & m)
   *                  with m = ~(lo_x ^ hi_x)  ... mask out all non-const bits
   *
   * Intuition:
   * 1) x & s = t on all const bits of x
   * 2) s & t = t on all non-const bits of x
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorConcat : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorConcat(RNG* rng, uint32_t size);
  BitVectorConcat(RNG* rng,
                  const BitVector& assignment,
                  const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * x o s = tx o ts
   * s o x = ts o tx
   *
   * w/o  const bits: s = ts
   *   pos_x = 0: ts = t[bw(s) - 1 : 0]
   *   pos_x = 1: ts = t[bw(t) - 1 : bw(t) - bw(s)]
   *
   * with const bits: mfb(x, tx) && s = ts
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorEq : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorEq(RNG* rng, uint32_t size);
  BitVectorEq(RNG* rng,
              const BitVector& assignment,
              const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: true
   * with const bits:
   *  t = 0: (hi_x != lo_x) || (hi_x != s)
   *  t = 1: mfb(x, s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorMul : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorMul(RNG* rng, uint32_t size);
  BitVectorMul(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: ((-s | s) & t) = t
   * with const bits: (((-s | s) & t) = t) &&
   *                  (s = 0 || ((odd(s) => mfb(x, t * s^-1)) &&
   *                            (!odd(s) => mfb (x << c, y << c))))
   *                  with c = ctz(s) and y = (t >> c) * (s >> c)^-1
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
};

/**
 * w/o const bits (IC_shift):
 *   ASHR:
 *     pos_x = 0: (s < bw(s) => (t << s) >>a s = t) &&
 *                (s >= bw(s) => (t = ones || t = 0))
 *     pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
 *                (s[msb] = 1 => IC_shr(~s >> x = ~t)
 *
 * with const bits:
 *   ASHR:
 *     pos_x = 0: IC_ashr && mfb(x >>a s, t)
 *
 *     pos_x = 1: IC_ashr &&
 *                (s[msb] = 0 => IC_shr) &&
 *                (s[msb] = 1 => IC_shr(~s >> x = ~t))
 */

class BitVectorShl : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorShl(RNG* rng, uint32_t size);
  BitVectorShl(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: (t >> s) << s = t
   *     pos_x = 1: ctz(s) <= ctz(t) &&
   *                ((t = 0) || (s << (ctz(t) - ctz(s))) = t)
   *
   * with const bits:
   *     pos_x = 0: IC_wo && mfb(x << s, t)
   *     pos_x = 1: IC_wo &&
   *                ((t = 0) => (hi_x >= ctz(t) - ctz(s) || (s = 0))) &&
   *                ((t != 0) => mfb(x, ctz(t) - ctz(s)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorShr : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorShr(RNG* rng, uint32_t size);
  BitVectorShr(RNG* rng,
               const BitVector& assignment,
               const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: (t << s) >> s = t
   *     pos_x = 1: clz(s) <= clz(t) &&
   *                ((t = 0) || (s >> (clz(t) - clz(s))) = t)
   *
   * with const bits:
   *     pos_x = 0: IC_wo && mfb(x >> s, t)
   *     pos_x = 1: IC_wo &&
   *                ((t = 0) => (hi_x >= clz(t) - clz(s) || (s = 0))) &&
   *                ((t != 0) => mfb(x, clz(t) - clz(s)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

}  // namespace bzlals
#endif
