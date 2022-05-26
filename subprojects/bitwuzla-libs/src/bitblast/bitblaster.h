#ifndef BZLA__BITBLAST_BITBLASTER_H
#define BZLA__BITBLAST_BITBLASTER_H

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

  virtual Bits bv_shl(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());

    size_t size = a.size();
    if (size == 1)
    {
      return Bits{d_bit_mgr.mk_and(a[0], d_bit_mgr.mk_not(b[0]))};
    }

    size_t shift_size = std::ceil(std::log2(b.size()));
    assert(shift_size <= b.size());

    Bits shift_result = a;
    for (size_t i = 0; i < shift_size; ++i)
    {
      size_t shift_step = std::pow(2, i);
      size_t shift_bit  = b.size() - 1 - i;
      assert(shift_step < size);

      // Perform left shift by `shift_step` bits.
      for (size_t j = 0; j < size - shift_step; ++j)
      {
        shift_result[j] = d_bit_mgr.mk_ite(
            b[shift_bit], shift_result[j + shift_step], shift_result[j]);
      }

      // The last `shift_step` bits either stay the same or become zero.
      T not_shift = d_bit_mgr.mk_not(b[shift_bit]);
      for (size_t j = size - shift_step; j < size; ++j)
      {
        shift_result[j] = d_bit_mgr.mk_and(not_shift, shift_result[j]);
      }
    }

    Bits res = bv_ite(ult_helper(b, bv_value(BitVector(b.size(), size))),
                      shift_result,
                      bv_value(BitVector(size, 0)));

    return res;
  }

  virtual Bits bv_shr(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());

    size_t size = a.size();
    if (size == 1)
    {
      return Bits{d_bit_mgr.mk_and(a[0], d_bit_mgr.mk_not(b[0]))};
    }

    size_t shift_size = std::ceil(std::log2(b.size()));
    assert(shift_size <= b.size());

    Bits shift_result = a;
    for (size_t i = 0; i < shift_size; ++i)
    {
      size_t shift_step = std::pow(2, i);
      size_t shift_bit  = b.size() - 1 - i;
      assert(shift_step < size);

      // Perform left right by `shift_step` bits.
      for (size_t j = 0, k = size - 1; j < size - shift_step; ++j, --k)
      {
        shift_result[k] = d_bit_mgr.mk_ite(
            b[shift_bit], shift_result[k - shift_step], shift_result[k]);
      }

      // The first `shift_step` bits either stay the same or become zero.
      T not_shift = d_bit_mgr.mk_not(b[shift_bit]);
      for (size_t j = 0; j < shift_step; ++j)
      {
        shift_result[j] = d_bit_mgr.mk_and(not_shift, shift_result[j]);
      }
    }

    Bits res = bv_ite(ult_helper(b, bv_value(BitVector(b.size(), size))),
                      shift_result,
                      bv_value(BitVector(size, 0)));

    return res;
  }

  virtual Bits bv_ashr(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());

    size_t size = a.size();
    if (size == 1)
    {
      return a;
    }

    size_t shift_size = std::ceil(std::log2(b.size()));
    assert(shift_size <= b.size());

    Bits shift_result = a;
    for (size_t i = 0; i < shift_size; ++i)
    {
      size_t shift_step = std::pow(2, i);
      size_t shift_bit  = b.size() - 1 - i;
      assert(shift_step < size);

      // Perform left right by `shift_step` bits.
      for (size_t j = 0, k = size - 1; j < size - shift_step; ++j, --k)
      {
        shift_result[k] = d_bit_mgr.mk_ite(
            b[shift_bit], shift_result[k - shift_step], shift_result[k]);
      }

      // The first `shift_step` bits either stay the same or become one/zero
      // depending on msb.
      for (size_t j = 0; j < shift_step; ++j)
      {
        shift_result[j] =
            d_bit_mgr.mk_ite(b[shift_bit], shift_result[0], shift_result[j]);
      }
    }

    T shift_less_than_size = ult_helper(b, bv_value(BitVector(b.size(), size)));
    for (size_t i = 0; i < size; ++i)
    {
      shift_result[i] =
          d_bit_mgr.mk_ite(shift_less_than_size, shift_result[i], a[0]);
    }

    return Bits{shift_result};
  }

  virtual Bits bv_extract(const Bits& bits, size_t upper, size_t lower)
  {
    assert(lower <= upper);
    assert(upper < bits.size());
    Bits res(bits.begin() + (bits.size() - 1 - upper), bits.end() - lower);
    assert(res.size() == upper - lower + 1);
    return res;
  }

  /**
   * Bit-blast concatenation of bit-vectors `a` and `b`.
   */
  virtual Bits bv_concat(const Bits& a, const Bits& b)
  {
    Bits res;
    res.reserve(a.size() + b.size());
    res.insert(res.end(), a.begin(), a.end());
    res.insert(res.end(), b.begin(), b.end());
    return res;
  }

  /* Predicates */

  virtual Bits bv_eq(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());
    T res = d_bit_mgr.mk_iff(a[0], b[0]);
    for (size_t i = 1; i < a.size(); ++i)
    {
      res = d_bit_mgr.mk_and(res, d_bit_mgr.mk_iff(a[i], b[i]));
    }
    return Bits{res};
  }

  virtual Bits bv_ult(const Bits& a, const Bits& b)
  {
    assert(a.size() == b.size());
    return Bits{ult_helper(a, b)};
  }

  virtual Bits bv_slt(const Bits& a, const Bits& b)
  {
    size_t msb_pos  = a.size() - 1;
    const T& a_sign = a[0];
    const T& b_sign = b[0];

    // a[msb] = 1, b[msb] = 0: true
    T strict_neg = d_bit_mgr.mk_and(a_sign, d_bit_mgr.mk_not(b_sign));

    if (a.size() == 1)
    {
      return Bits{strict_neg};
    }

    // a[0:msb-1] < b[0:msb-1]
    Bits a_rem = bv_extract(a, msb_pos - 1, 0);
    Bits b_rem = bv_extract(b, msb_pos - 1, 0);
    T ult      = ult_helper(a_rem, b_rem);

    // a[msb] = 0, b[msb] = 1: false
    T strict_pos = d_bit_mgr.mk_and(d_bit_mgr.mk_not(a_sign), b_sign);
    // a[msb] = b[msb]: a[0:msb-1] < b[0:msb-1]
    T eq_sign = d_bit_mgr.mk_and(d_bit_mgr.mk_not(strict_neg),
                                 d_bit_mgr.mk_not(strict_pos));

    T res = d_bit_mgr.mk_or(strict_neg, d_bit_mgr.mk_and(eq_sign, ult));
    return Bits{res};
  }

  /* Arithmetic */

  virtual Bits bv_add(const Bits& a, const Bits& b)
  {
    Bits res;
    size_t size = a.size();
    res.resize(size);

    T cout;
    std::tie(res[size - 1], cout) = half_adder(a[size - 1], b[size - 1]);
    for (size_t i = 1, j = size - 2; i < size; ++i, --j)
    {
      std::tie(res[j], cout) = full_adder(a[j], b[j], cout);
    }
    return res;
  }

  virtual Bits bv_mul(const Bits& a, const Bits& b)
  {
    Bits res;
    size_t size = a.size();
    res.reserve(size);

    for (size_t i = 0; i < size; ++i)
    {
      res.emplace_back(d_bit_mgr.mk_and(a[i], b[size - 1]));
    }

    for (size_t i = 1, ib = size - 2; i < size; ++i, --ib)
    {
      T cout;
      const T& b_bit = b[ib];

      std::tie(res[ib], cout) =
          half_adder(res[ib], d_bit_mgr.mk_and(a[size - 1], b_bit));
      for (size_t j = 1, ir = ib - 1, ia = size - 2; j <= ib; ++j, --ir, --ia)
      {
        std::tie(res[ir], cout) =
            full_adder(res[ir], d_bit_mgr.mk_and(a[ia], b_bit), cout);
      }
    }
    return res;
  }

  /**
   * Bit-blast if-then-else over bit-vectors `a` and `b` of size k, and a
   * condition `cond` of size 1.
   */
  virtual Bits bv_ite(const T cond, const Bits& a, const Bits& b)
  {
    Bits res;
    res.reserve(a.size());
    for (size_t i = 0; i < a.size(); ++i)
    {
      res.emplace_back(d_bit_mgr.mk_ite(cond, a[i], b[i]));
    }
    return res;
  }

 private:
  T ult_helper(const Bits& a, const Bits& b)
  {
    size_t lsb = a.size() - 1;
    // a[lsb] < b[lsb]
    T res = d_bit_mgr.mk_and(d_bit_mgr.mk_not(a[lsb]), b[lsb]);
    for (size_t i = 1, j = a.size() - 2; i < a.size(); ++i, --j)
    {
      res = d_bit_mgr.mk_or(
          // a[i] < b[i]
          d_bit_mgr.mk_and(d_bit_mgr.mk_not(a[j]), b[j]),
          // ~(a[i] = 1 /\ b[i] = 0) /\ res
          d_bit_mgr.mk_and(
              d_bit_mgr.mk_not(d_bit_mgr.mk_and(a[j], d_bit_mgr.mk_not(b[j]))),
              res));
    }
    return res;
  }

  /**
   * Create half adder of `a` and `b`.
   *
   * Returns a pair consisting of the sum of the two bits and the carry out bit.
   */
  std::pair<T, T> half_adder(const T& a, const T& b)
  {
    // Carry out bit
    T a_and_b = d_bit_mgr.mk_and(a, b);

    // Sum of a and b: a xor b
    T a_or_b  = d_bit_mgr.mk_or(a, b);
    T a_xor_b = d_bit_mgr.mk_and(d_bit_mgr.mk_not(a_and_b), a_or_b);

    // Return <sum, carry bit>
    return std::make_pair(a_xor_b, a_and_b);
  }

  /**
   * Create full adder of `a`, `b` and carry bit `carry_in`.
   *
   * Returns a pair consisting of the sum of a, b, and carry_in, and the carry
   * out bit.
   */
  std::pair<T, T> full_adder(const T& a, const T& b, const T& carry_in)
  {
    auto [sum, cout1] = half_adder(a, b);
    auto [res, cout2] = half_adder(sum, carry_in);
    return std::make_pair(res, d_bit_mgr.mk_or(cout1, cout2));
  }

  BitInterface<T> d_bit_mgr;
};

}  // namespace bzla::bb
#endif
