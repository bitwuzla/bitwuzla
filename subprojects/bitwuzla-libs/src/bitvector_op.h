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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: true
   * with const bits: mfb(x, t - s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo): (t & s) = t
   * with const bits       : IC_wo && ((s & hi_x) & m) = (t & m)
   *                         with m = ~(lo_x ^ hi_x)
   *                              ... mask out all non-const bits
   * Intuition:
   * 1) x & s = t on all const bits of x
   * 2) s & t = t on all non-const bits of x
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: true
   * with const bits:
   *  t = 0: (hi_x != lo_x) || (hi_x != s)
   *  t = 1: mfb(x, s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo): ((-s | s) & t) = t
   * with const bits       : IC_wo &&
   *                         (s = 0 ||
   *                          ((odd(s) => mfb(x, t * s^-1)) &&
   *                           (!odd(s) => mfb (x << c, y << c))))
   *                  with c = ctz(s) and y = (t >> c) * (s >> c)^-1
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVectorDomain* inverse() { return d_inverse.get(); }

  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
};

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

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

class BitVectorShr : public BitVectorOp
{
 public:
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits, target value t and assignment s of the operator at index 1 - pos_x.
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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits, target value t and assignment s of at d_children[1 - pos_x].
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: (s < bw(s) => (t << s) >>a s = t) &&
   *                (s >= bw(s) => (t = ones || t = 0))
   *     pos_x = 1: (s[msb] = 0 => IC_shr(s >> x = t) &&
   *                (s[msb] = 1 => IC_shr(~s >> x = ~t))
   *
   * with const bits:
   *     pos_x = 0: IC_wo && mfb(x >>a s, t)
   *     pos_x = 1: IC_wo &&
   *                (s[msb ] = 0 => IC_shr) &&
   *                (s[msb] = 1 => IC_shr(~s >> x = ~t))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: (s * t) / s = t
   *     pos_x = 1: s / (s / t) = t
   *
   * with const bits:
   *     pos_x = 0: IC_wo &&
   *                (t = 0 => lo_x < s) &&
   *                ((t != 0 && s != 0 ) => \exists y. (
   *                    mfb(x, y) && (~c => y < s * t + 1) && (c => y <= ones)))
   *                with c = umulo(s, t + 1) && uaddo(t, 1)
   *     pos_x = 1: IC_wo &&
   *                (t != ones => hi_x > 0) &&
   *                ((s != 0 || t != 0) => (s / hi_x <= t) && \exists y. (
   *                    mfb(x, y) &&
   *                    (t = ones => y <= s / t) &&
   *                    (t != ones => y > t + 1 && y <= s / t)))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVectorDomain* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: t = 0 || s != 0
   *     pos_x = 1: t = 0 || s != ones
   *
   * with const bits:
   *     pos_x = 0: t = 1 => (s != 0 && lo_x < s) && t = 0 => (hi_x >= s)
   *     pos_x = 1: t = 1 => (s != ones && hi_x > s) && t = 0 => (lo_x <= s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: t = 0 || s != min_signed_value
   *     pos_x = 1: t = 0 || s != max_signed_value
   *
   * with const bits:
   *     pos_x = 0: t = 1 => (s != min_signed_value &&
   *                 ((MSB(x) = 0 && lo_x < s) ||
   *                  (MSB(x) != 0 && 1 o lo_x[bw-2:0] < s))) &&
   *                t = 0 => ((MSB(x) = 1 && hi_x >= s) ||
   *                          (MSB(x) != 1 && 0 o hi_x[bw-2:0] >= s))))
   *     pos_x = 1: t = 1 => (s != max_signed_value &&
   *                          ((MSB(x) = 1 && s < hi_x) ||
   *                           (MSB(x) != 1 && s < 0 o hi_x[bw-2:0])))
   *                t = 0 => ((MSB(x) = 0 && s >= lo_x) ||
   *                          (MSB(x) != 0 && s >= 1 o lo_x[bw-2:0])))
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVector* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVector> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: ~(-s) >= t
   *     pos_x = 1: (t + t - s) & s >= t
   *
   * with const bits:
   *     pos_x = 0: IC_wo &&
   *                ((s = 0 || t = ones) => mfb(x, t)) &&
   *                ((s != 0 && t != ones) => \exists y. (
   *                    mfb(x, s * y + t) && !umulo(s, y) && !uaddo(s *y, t)))
   *     pos_x = 1: IC_wo &&
   *                (s = t => (lo_x = 0 || hi_x > t)) &&
   *                (s != t => \exists y. (
   *                    mfb(x, y) && y > t && (s - t) mod y = 0)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVectorDomain* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
};

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
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * ite(_c, _t, _e)
   *
   * w/o const bits (IC_wo):
   *     pos_x = 0: s0 == t || s1 == t
   *                with s0 the value for '_t' branch and s1 the value for '_e'
   *     pos_x = 1: s0 == true
   *                with s0 the value for '_c'
   *     pos_x = 2: s0 == false
   *                with s0 the value for '_c'
   *
   * with const bits:
   *     pos_x = 0: (!is_fixed(x) && (s0 = t || s1 = t)) ||
   *                (is_fixed_true(x) && s0 = t) ||
   *                (is_fixed_false(x) && s1 = t)
   *                with s0 the value for '_t' and s1 the value for '_e'
   *     pos_x = 1: s0 = true && mfb(x, t)
   *                with s0 the value for '_c'
   *     pos_x = 2: s0 == false && mfb(x, t)
   *                with s0 the value for '_c'
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);

  /** Get the cached inverse result. */
  BitVectorDomain* inverse() { return d_inverse.get(); }

 private:
  /** Cached inverse result. */
  std::unique_ptr<BitVectorDomain> d_inverse = nullptr;
};

}  // namespace bzlals
#endif
