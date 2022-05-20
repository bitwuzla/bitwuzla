#ifndef BZLA__BB_BITBLAST_H
#define BZLA__BB_BITBLAST_H

#include <cassert>
#include <cmath>
#include <cstddef>
#include <vector>

#include "bitvector.h"

namespace bzla::bb {

/**
 * Interface for providing bit-level operations used by the bit-blaster
 * interface.
 */
template <class T>
class BitInterface
{
 public:
  /** Create bit representing false. */
  T mk_false();
  /** Create bit representing true. */
  T mk_true();
  /** Create constant representing a bit. */
  T mk_bit();
  /** Create negation of bit `a`. */
  T mk_not(const T& a);
  /** Create logical and of bits `a` and `b`. */
  T mk_and(const T& a, const T& b);
  /** Create logical or of bits `a` and `b`. */
  T mk_or(const T& a, const T& b);
  /** Create equality of bits `a` and `b`. */
  T mk_iff(const T& a, const T& b);
  /** Create if-then-else over condition `c`, if branch `a` and then `b`. */
  T mk_ite(const T& c, const T& a, const T& b);
};

template <class T>
class BitblasterInterface
{
 public:
  using Bits = std::vector<T>;

  virtual Bits bv_value(const BitVector& bv_value)
  {
    Bits res;
    for (size_t i = 0, j = bv_value.size() - 1; i < bv_value.size(); ++i)
    {
      res.emplace_back(bv_value.get_bit(j - i) ? d_bit_mgr.mk_true()
                                               : d_bit_mgr.mk_false());
    }
    return res;
  }

  virtual Bits bv_constant(size_t size)
  {
    Bits res;
    res.reserve(size);
    for (size_t i = 0; i < size; ++i)
    {
      res.emplace_back(d_bit_mgr.mk_bit());
    }
    return res;
  }

  /* Bitwise */

  virtual Bits bv_not(const Bits& bits)
  {
    Bits res;
    res.reserve((bits.size()));
    for (const T& bit : bits)
    {
      res.emplace_back(d_bit_mgr.mk_not(bit));
    }
    return res;
  }

  virtual Bits bv_and(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());
    Bits res;
    res.reserve(a.size());
    for (size_t i = 0; i < a.size(); ++i)
    {
      res.emplace_back(d_bit_mgr.mk_and(a[i], b[i]));
    }
    return res;
  }

  virtual Bits bv_or(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());
    Bits res;
    res.reserve(a.size());
    for (size_t i = 0; i < a.size(); ++i)
    {
      res.emplace_back(d_bit_mgr.mk_or(a[i], b[i]));
    }
    return res;
  }

  virtual Bits bv_extract(const Bits& bits, size_t upper, size_t lower)
  {
    assert(lower <= upper);
    assert(upper < bits.size());
    Bits res(bits.begin() + (bits.size() - 1 - upper), bits.end() - lower);
    assert(res.size() == upper - lower + 1);
    return res;
  }

 private:

  BitInterface<T> d_bit_mgr;
};

}  // namespace bzla::bb
#endif
