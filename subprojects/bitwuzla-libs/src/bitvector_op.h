#ifndef BZLALS__BITVECTOR_OP_H
#define BZLALS__BITVECTOR_OP_H

#include "bitvector.h"
#include "bitvector_domain.h"

namespace bzlals {

class BitVectorOp
{
 public:
  /** Constructor. */
  BitVectorOp(uint32_t size)
      : d_assignment(BitVector::mk_zero(size)), d_domain(BitVectorDomain(size))
  {
    d_children.reset(new BitVectorOp*[arity()]);
  }
  BitVectorOp(const BitVector& assignment, const BitVectorDomain& domain)
      : d_assignment(assignment), d_domain(domain)
  {
    d_children.reset(new BitVectorOp*[arity()]);
  }
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
  BitVector d_assignment;
  BitVectorDomain d_domain;
};

class BitVectorAdd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAdd(uint32_t size);
  BitVectorAdd(const BitVector& assignment, const BitVectorDomain& domain);
  /**
   * Check invertibility condition for x at index pos_x with respect to constant
   * bits and target value t.
   *
   * w/o  const bits: true
   * with const bits: mfb(x, t - s)
   */
  bool is_invertible(const BitVector& t, uint32_t pos_x);
};

class BitVectorAnd : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorAnd(uint32_t size);
  BitVectorAnd(const BitVector& assignment, const BitVectorDomain& domain);
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
};

class BitVectorConcat : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorConcat(uint32_t size);
  BitVectorConcat(const BitVector& assignment, const BitVectorDomain& domain);
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
};

class BitVectorEq : public BitVectorOp
{
 public:
  /** Constructors. */
  BitVectorEq(uint32_t size);
  BitVectorEq(const BitVector& assignment, const BitVectorDomain& domain);
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
};

}  // namespace bzlals
#endif
