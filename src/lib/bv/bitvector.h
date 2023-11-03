/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BV_BITVECTOR_H
#define BZLA__BV_BITVECTOR_H

#include <gmpxx.h>

#include <cstdint>
#include <memory>
#include <string>

namespace bzla {

struct GMPMpz;
class RNG;

class BitVector
{
 public:
  /** Prime numbers used for hashing. */
  static inline uint32_t s_hash_primes[] = {333444569u, 76891121u, 456790003u};
  /** Number of prime numbers used for hashing. */
  static constexpr uint32_t s_n_primes =
      ((uint32_t) (sizeof s_hash_primes / sizeof *s_hash_primes));
  // mpz_*_ui functions have unsigned long (or mp_bitcnt_t) arguments, which is
  // represented as 64 bit on Linux and macOS 64-bit systems. On 64-bit Windows
  // unsigned long has a size of 32 bit, which affects the values stored in
  // d_val_uint64 if being passed to a mpz_*_ui function.
  // In order to avoid values being truncated, for Windows we store all values
  // that require more than 32 bit as GMP integer. Else, we store values up to
  // 64-bit in d_val_uint64.
  static constexpr size_t s_native_size = sizeof(unsigned long) * 8;
  static_assert(s_native_size == sizeof(mp_bitcnt_t) * 8, "");

  /**
   * Determine if given string representation of a value in the given numeric
   * base fits into a bit-vector of given size.
   * @param size The size of the bit-vector.
   * @param str The string represent of the value.
   * @param base The numeric base the value is given in.
   * @return True if string in base fits into a bit-vector of given size.
   */
  static bool fits_in_size(uint64_t size,
                           const std::string& str,
                           uint32_t base);
  /**
   * Determine if given integer value fits into a bit-vector of given size.
   * @param size The size of the bit-vector.
   * @param value The integer value.
   * @param sign True if given value is to be interpreted as signed.
   * @return True if given value fits into a bit-vecgtor of given size.
   */
  static bool fits_in_size(uint64_t size, uint64_t value, bool sign = false);

  /**
   * Construct a bit-vector of given size from given uint64 value.
   *
   * Truncates value if `truncate` is true and the value cannot be
   * represented with `size` bits.
   *
   * @note For signed values, use `from_si()` instead. It guarantees that
   *       negative values are sign extended to `size` if `size > 64`, which
   *       is not the case with `from_ui()` (which zero extends the value).
   *
   * @param size     The size of the bit-vector.
   * @param value    A uint64 representing the bit-vector value. The value must
   *                 be representable with `size` bits if `truncate` is false.
   * @param truncate True to allow truncating the value if it is not
   *                 representable with `size` bits.
   */
  static BitVector from_ui(uint64_t size,
                           uint64_t value,
                           bool truncate = false);
  /**
   * Construct a bit-vector of given size from given int64 value.
   *
   * Truncates value if `truncate` is true and the value cannot be
   * represented with `size` bits.
   *
   * @note For signed values, always use this function. It guarantees that
   *       negative values are sign extended to `size` if `size > 64`, which
   *       is not the case with `from_ui()` (which zero extends the value).
   *
   * @param size  The size of the bit-vector.
   * @param value A int64 representing the bit-vector value. The value must be
   *              representable with `size` bits if `truncate` is false.
   * @param truncate True to allow truncating the value if it is not
   *                 representable with `size` bits.
   */
  static BitVector from_si(uint64_t size, int64_t value, bool truncate = false);

  /**
   * Create a true bit-vector (value 1 of size 1).
   * @return A bit-vector representing True.
   */
  static BitVector mk_true();
  /**
   * Create a false bit-vector (value 0 of size 1).
   * @return A bit-vector representing False.
   */
  static BitVector mk_false();
  /**
   * Create a zero bit-vector of given size.
   * @param size The size of the bit-vector.
   * @return A bit-vector representing zero of given size..
   */
  static BitVector mk_zero(uint64_t size);
  /**
   * Create a one bit-vector of given size.
   * @param size The size of the bit-vector.
   * @return A bit-vector representing one of given size.
   */
  static BitVector mk_one(uint64_t size);
  /**
   * Create a ones bit-vector of given size.
   * @param size The size of the bit-vector.
   * @return A bit-vector representing ones of given size.
   */
  static BitVector mk_ones(uint64_t size);
  /**
   * Create a minimum signed value (10..0) bit-vector of given size.
   * @param size The size of the bit-vector.
   * @return A bit-vector representing the minimum signed value of given size.
   */
  static BitVector mk_min_signed(uint64_t size);
  /**
   * Create a maximum signed value (01..1) bit-vector of given size.
   * @param size The size of the bit-vector.
   * @return A bit-vector representing the maximum signed value of given size.
   */
  static BitVector mk_max_signed(uint64_t size);

  /**
   * Create an if-then-else (ite) over the given bit-vectors.
   * @param c A bit-vector representing the condition of the ite.
   * @param t A bit-vector representing the then branch of the ite.
   * @param e A bit-vector representing the else branch of the ite.
   * @return A bit-vector representing the ite.
   */
  static BitVector bvite(const BitVector& c,
                         const BitVector& t,
                         const BitVector& e);

  /** Default constructor. */
  BitVector();
  /**
   * Construct a zero bit-vector of given size.
   * @param size The size of the bit-vector.
   */
  BitVector(uint64_t size);
  /**
   * Construct a random bit-vector of given size.
   * @param size The size of the bit-vector.
   * @param rng The random number generator.
   */
  BitVector(uint64_t size, RNG& rng);

  /**
   * Construct a random bit-vector of given size with the given range.
   * @param size The size of the bit-vector.
   * @param rng  The random number generator.
   * @param from A bit-vector representing the lower bound of given range
   *             (inclusive).
   * @param to   A bit-vector representing the upper bound of given range
   *             (inclusive).
   * @param sign True to interpret the given range as signed, else unsigned.
   */
  BitVector(uint64_t size,
            RNG& rng,
            const BitVector& from,
            const BitVector& to,
            bool sign = false);
  /**
   * Construct a random bit-vector of given size with one of the given ranges.
   * @param size The size of the bit-vector.
   * @param rng  The random number generator.
   * @param from0 A bit-vector representing the lower bound of the first given
   *              range (inclusive). Ignored if null.
   * @param to0   A bit-vector representing the upper bound of the first given
   *              range (inclusive). Must be null if `from0` is null. Ignored
   *              if null.
   * @param from1 A bit-vector representing the lower bound of the second given
   *              range (inclusive). Ignored if null.
   * @param to1   A bit-vector representing the upper bound of the second given
   *              range (inclusive). Must be null if `from1` is null. Ignored
   *              if null.
   * @param sign True to interpret the given range as signed, else unsigned.
   */
  BitVector(uint64_t size,
            RNG& rng,
            const BitVector& from0,
            const BitVector& to0,
            const BitVector& from1,
            const BitVector& to1,
            bool sign = false);
  /**
   * Construct a new bit-vector of given size and randomly set bits within given
   * index range. Bits outside of given index range are initialized with zero.
   * @param size   The size of the bit-vector.
   * @param rng    The random number generator.
   * @param idx_hi The upper index of the range.
   * @param idx_lo The lower index of the range.
   */
  BitVector(uint64_t size, RNG& rng, uint64_t idx_hi, uint64_t idx_lo);

  /**
   * Construct a bit-vector of given size from given binary string.
   * @param size  The size of the bit-vector, must be >= the length of `value`.
   * @param value A string representing the value of the bit-vector. If the
   *              length of this string is > `size`, the value is zero extended.
   * @param base  The base the string is given in (2 for binary, 10 for decimal,
   *              16 for hexadecimal).
   */
  BitVector(uint64_t size, const std::string& value, uint32_t base = 2);

  /** Copy constructor. */
  BitVector(const BitVector& other);
  /** Move constructor. */
  BitVector(BitVector&& other);

  /** Destructor. */
  ~BitVector();

  /** Copy assignment operator. */
  BitVector& operator=(const BitVector& other);

  /** @return The hash value of this bit-vector. */
  size_t hash() const;

  /** @return True if this is an uninitialized bit-vector. */
  bool is_null() const { return d_size == 0; }

  /**
   * Set the value of this bit-vector to the given unsigned (in-place).
   * @param value The value to set.
   */
  void iset(uint64_t value);
  /**
   * Set the value of this bit-vector to the value of `bv` (in-place).
   * @param bv A bit-vector representing the value this bit-vector is to between
   *           set to.
   */
  void iset(const BitVector& bv);
  /**
   * Set the value of this bit-vector to a random value between `from` and `to`
   * (in-place).
   * @param rng  The random number generator.
   * @param from A bit-vector representing the `from` value.
   * @param to   A bit-vector representing the `to` value.
   */
  void iset(RNG& rng,
            const BitVector& from,
            const BitVector& to,
            bool is_signed);

  /**
   * Equality comparison operator.
   * @param bv The bit-vector to compare this bit-vector to.
   */
  bool operator==(const BitVector& bv) const;
  /**
   * Disequality comparison operator.
   * @param bv The bit-vector to compare this bit-vector to.
   */
  bool operator!=(const BitVector& bv) const;

  /**
   * Get the string representation of this bit-vector.
   * @param base 2 for binary representation, 10 for decimal representation, 16
   *             for hexadecimal representation.
   * @return The string representation.
   */
  std::string str(uint32_t base = 2) const;
  /**
   * Get the uint64_t representation of this bit-vector.
   * @param size The size of this bit-vector, must be <= 64.
   * @param truncate True to allow truncating the value if it is not
   *                 representable with 64 bits.
   * @return The uint64_t representation.
   */
  uint64_t to_uint64(bool truncate = false) const;

  /** @return the size of this bit-vector. */
  uint64_t size() const { return d_size; }

  /**
   * Compare this bit-vector with given bit-vector (unsigned).
   *
   * @param bv The bit-vector to compare this bit-vector with.
   * @return 0 if the bit-vectors are equal, -1 if their sizes don't match or
   *         if `this` is unsigned less than `bv`, and 1 if `this` is unsigned
   *         greater than `bv`.
   */
  int32_t compare(const BitVector& bv) const;
  /**
   * Compare this bit-vector with given bit-vector (signed).
   *
   * @param bv The bit-vector to compare this bit-vector with.
   * @return 0 if the bit-vectors are equal, -1 if their sizes don't match or
   *         if `this` is signed less than `bv`, and 1 if `this` is signed
   *         greater than `bv`.
   */
  int32_t signed_compare(const BitVector& bv) const;

  /**
   * Determine the value of the bit at given index.
   * @param idx The index of the bit.
   * @return True if the bit at given index is 1, and false otherwise.
   */
  bool bit(uint64_t idx) const;
  /**
   * Set the bit at given index to the given value.
   * @param idx   The index of the bit.
   * @param value The value.
   */
  void set_bit(uint64_t idx, bool value);
  /**
   * Flip the bit at given index (in-place).
   * @param The index of the bit.
   */
  void flip_bit(uint64_t idx);
  /** @return True if the lsb (index 0) is 1, and false otherwise. */
  bool lsb() const;
  /** @return True if the msb (index size - 1) is 1, and false otherwise. */
  bool msb() const;

  /** @return True if this bit-vector is one and of size 1. */
  bool is_true() const;
  /** @return True if this bit-vector is zero and of size 1. */
  bool is_false() const;
  /** @return True if this bit-vector is zero. */
  bool is_zero() const;
  /** @return True if this bit-vector is ones (a bit-vector of all 1 bits). */
  bool is_ones() const;
  /** @return True if this bit-vector is one. */
  bool is_one() const;
  /** @return True if this bit-vector is the minimum signed value. */
  bool is_min_signed() const;
  /** @return True if this bit-vector is the maximum signed value. */
  bool is_max_signed() const;

  /** @return True if this bit-vector is a power of two. */
  bool is_power_of_two() const;

  /**
   * Determine if the addition of this and the given bit-vector produces
   * an overflow.
   * @param bv The bit-vector to add to this bit-vector.
   * @return True if it produces an overflow.
   */
  bool is_uadd_overflow(const BitVector& bv) const;
  /**
   * Determine if the multiplication of this and the given bit-vector produces
   * an overflow.
   * @param bv The bit-vector to multiply this bit-vector with.
   * @return True if it produces an overflow.
   */
  bool is_umul_overflow(const BitVector& bv) const;

  /** @return The number of trailing zeros (counted from lsb). */
  uint64_t count_trailing_zeros() const;
  /** @return The number of leading zeros (counted from msb). */
  uint64_t count_leading_zeros() const;
  /** @return The number of leading ones (counted from msb). */
  uint64_t count_leading_ones() const;

  /* ----------------------------------------------------------------------- */
  /* Bit-vector operations.                                                  */
  /* ----------------------------------------------------------------------- */

  /**
   * Create a bit-vector representing the two's complement negation of this
   * bit-vector.
   * @return The two's complement of this bit-vector.
   */
  BitVector bvneg() const;
  /**
   * Create a bit-vector representing the bit-wise negation of this bit-vector.
   * @return The bit-wise negation of this bit-vector.
   */
  BitVector bvnot() const;
  /**
   * Create a bit-vector representing the increment (+ 1) of this bit-vector.
   * @return The increment of this bit-vector.
   */
  BitVector bvinc() const;
  /**
   * Create a bit-vector representing the decrement (- 1) of this bit-vector.
   * @return The decrement of this bit-vector.
   */
  BitVector bvdec() const;
  /**
   * Create a bit-vector representing the and reduction of this bit-vector.
   * @return A bit-vector of size 1, representing the result of the and
   *         reduction of this bit-vector (1 if all bits of this bit-vector are
   *         one, and 0 otherwise).
   */
  BitVector bvredand() const;
  /**
   * Create a bit-vector representing the or reduction of this bit-vector.
   * @return A bit-vector of size 1, representing the result of the or
   *         reduction of this bit-vector (1 if at least one bit of this
   *         bit-vector is one, and 0 otherwise).
   */
  BitVector bvredor() const;

  /**
   * Create a bit-vector representing the addition of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the addition.
   */
  BitVector bvadd(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the subtraction of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the subtraction.
   */
  BitVector bvsub(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise and of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise and.
   */
  BitVector bvand(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the implication of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the implication.
   */
  BitVector bvimplies(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise nand of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise nand.
   */
  BitVector bvnand(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise nor of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise nor.
   */
  BitVector bvnor(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise or of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise or.
   */
  BitVector bvor(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise xnor of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise xnor.
   */
  BitVector bvxnor(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the bit-wise xor of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the bit-wise xor.
   */
  BitVector bvxor(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the equality of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the equality.
   */
  BitVector bveq(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the disequality of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the disequality.
   */
  BitVector bvne(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned less than of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned less than.
   */
  BitVector bvult(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned less than or equal of this
   * bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned less than or
   *         equal.
   */
  BitVector bvule(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned greater than of this
   * bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned greater than.
   */
  BitVector bvugt(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned greater than or equal of
   * this bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned greater than
   *         or equal.
   */
  BitVector bvuge(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed less than of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed less than.
   */
  BitVector bvslt(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed less than or equal of this
   * bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed less than or
   *         equal.
   */
  BitVector bvsle(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed greater than of this
   * bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed greater than.
   */
  BitVector bvsgt(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed greater than or equal of this
   * bit-vector and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed greater than or
   *         equal.
   */
  BitVector bvsge(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the logical left shift of this bit-vector
   * by the given unsigned integer shift value.
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the left.
   * @return A bit-vector representing the result of the logical left shift.
   */
  BitVector bvshl(uint64_t shift) const;
  /**
   * Create a bit-vector representing the logical left shift of this bit-vector
   * by the given bit-vector shift value.
   * @param shift A bit-vector representing he number of bits to shift this
   *              bit-vector to the left.
   * @return A bit-vector representing the result of the logical left shift.
   */
  BitVector bvshl(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the logical right shift of this
   * bit-vector by the given unsigned integer shift value.
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A bit-vector representing the result of the logical right shift.
   */
  BitVector bvshr(uint64_t shift) const;
  /**
   * Create a bit-vector representing the logical right shift of this
   * bit-vector by the given bit-vector shift value.
   * @param shift A bit-vector representing he number of bits to shift this
   *              bit-vector to the right.
   * @return A bit-vector representing the result of the logical right shift.
   */
  BitVector bvshr(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the arithmetic right shift of this
   * bit-vector by the given unsigned integer shift value.
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A bit-vector representing the result of the arithmetic right shift.
   */
  BitVector bvashr(uint64_t shift) const;
  /**
   * Create a bit-vector representing the arithmetic right shift of this
   * bit-vector by the given bit-vector shift value.
   * @param shift A bit-vector representing he number of bits to shift this
   *              bit-vector to the right.
   * @return A bit-vector representing the result of the arithmetic right shift.
   */
  BitVector bvashr(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the multiplication of this bit-vector and
   * the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the multiplication.
   */
  BitVector bvmul(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned division of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned division.
   */
  BitVector bvudiv(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the unsigned remainder of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the unsigned remainder.
   */
  BitVector bvurem(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed division of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed division.
   */
  BitVector bvsdiv(const BitVector& bv) const;
  /**
   * Create a bit-vector representing the signed remainder of this bit-vector
   * and the given bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the signed remainder.
   */
  BitVector bvsrem(const BitVector& bv) const;

  /**
   * Create a bit-vector representing the concatenation of this bit-vector and
   * the given bit-vector. The given bit-vector is concatenated (at the right,
   * the lsb side) to this bit-vector.
   * @param bv The other bit-vector.
   * @return A bit-vector representing the result of the concatenation.
   */
  BitVector bvconcat(const BitVector& bv) const;

  /**
   * Create a bit-vector representing the extract of a given bit range from
   * this bit-vector.
   * @param idx_hi The upper bit-index of the range (inclusive).
   * @param idx_lo The lower bit-index of the range (inclusive).
   * @return A bit-vector representing the extracted bit range.
   */
  BitVector bvextract(uint64_t idx_hi, uint64_t idx_lo) const;

  /**
   * Create a bit-vector representing the zero extension of this bit-vector
   * by the given number of bits.
   * @param n The number of bits to extend this bit-vector with.
   * @return A bit-vector representing the zero extension.
   */
  BitVector bvzext(uint64_t n) const;
  /**
   * Create a bit-vector representing the sign extension of this bit-vector
   * by the given number of bits.
   * @param n The number of bits to extend this bit-vector with.
   * @return A bit-vector representing the sign extension.
   */
  BitVector bvsext(uint64_t n) const;

  /**
   * Calculate modular inverse for this bit-vector by means of the Extended
   * Euclidean Algorithm.
   *
   * @note Bit-vector must be odd. The greatest common divisor gcd (c, 2^bw)
   *       must be (and is, in this case) always 1.
   *
   * @return A bit-vector representing the modular inverse of this bit-vector.
   */
  BitVector bvmodinv() const;

  /* ----------------------------------------------------------------------- */
  /* In-place versions of bit-vector operations.                             */
  /*                                                                         */
  /* Note: This bit-vector may not be null.                                  */
  /*                                                                         */
  /* Result is stored in this bit-vector.                                    */
  /* Return a reference to this bit-vector.                                  */
  /* ----------------------------------------------------------------------- */

  /**
   * Two's complement negation (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the two's complement for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         two's complement of `bv`.
   */
  BitVector& ibvneg(const BitVector& bv);
  /**
   * Two's complement negation (in-place) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @return A reference to this bit-vector, overwritten with the result of the
   *         two's complement of this bit-vector.
   */
  BitVector& ibvneg();

  /**
   * Bit-wise negation (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the bit-wise negation for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise negation of `bv`.
   */
  BitVector& ibvnot(const BitVector& bv);
  /**
   * Bit-wise negation (in-place) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the bit-wise negation for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise negation of this bit-vector.
   */
  BitVector& ibvnot();

  /**
   * Increment (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the increment for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         increment of `bv`.
   */
  BitVector& ibvinc(const BitVector& bv);
  /**
   * Increment (in-place, chainable) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the increment for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         increment of this bit-vector.
   */
  BitVector& ibvinc();

  /**
   * Decrement (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the decrement for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         decrement of `bv`.
   */
  BitVector& ibvdec(const BitVector& bv);
  /**
   * Decrement (in-place, chainable) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the decrement for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         decrement of this bit-vector.
   */
  BitVector& ibvdec();

  /**
   * And reduction (in-place) of the given bit-vector.
   *
   * Result is a bit-vector of size 1, representing the result of the and
   * reduction of this bit-vector (1 if all bits of this bit-vector are one,
   * and 0 otherwise).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the and reduction for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         and reduction of `bv`.
   */
  BitVector& ibvredand(const BitVector& bv);
  /**
   * And reduction (in-place, chainable) of this bit-vector.
   *
   * Result is a bit-vector of size 1, representing the result of the and
   * reduction of this bit-vector (1 if all bits of this bit-vector are one,
   * and 0 otherwise).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the and reduction for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         and reduction of this bit-vector.
   */
  BitVector& ibvredand();

  /**
   * Or reduction (in-place) of the given bit-vector.
   *
   * Result is a bit-vector of size 1, representing the result of the or
   * reduction of this bit-vector (1 if at least one bit of this bit-vector is
   * one, and 0 otherwise).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the or reduction for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         or reduction of `bv`.
   */
  BitVector& ibvredor(const BitVector& bv);
  /**
   * Or reduction (in-place, chainable) of this bit-vector.
   *
   * Result is a bit-vector of size 1, representing the result of the or
   * reduction of this bit-vector (1 if at least one bit of this bit-vector is
   * one, and 0 otherwise).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the or reduction for.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         or reduction of this bit-vector.
   */
  BitVector& ibvredor();

  /**
   * Addition (in-place) of given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the addition.
   * @param bv1 The second operand of the addition.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         addition of the given bit-vectors.
   */
  BitVector& ibvadd(const BitVector& bv0, const BitVector& bv1);
  /**
   * Addition (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         addition of this and the given bit-vector.
   */
  BitVector& ibvadd(const BitVector& bv);

  /**
   * Bit-wise and (in-place) of given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise and.
   * @param bv1 The second operand of the bit-wise and.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise and of the given bit-vectors.
   */
  BitVector& ibvand(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise and (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise and of this and the given bit-vector.
   */
  BitVector& ibvand(const BitVector& bv);

  /**
   * Implication (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the implication.
   * @param bv1 The second operand of the implication.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         implication of the given bit-vectors.
   */
  BitVector& ibvimplies(const BitVector& bv0, const BitVector& bv1);
  /**
   * Implication (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         implication of this and the given bit-vector.
   */
  BitVector& ibvimplies(const BitVector& bv);

  /**
   * Bit-wise nand (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise nand.
   * @param bv1 The second operand of the bit-wise nand.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise nand of the given bit-vectors.
   */
  BitVector& ibvnand(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise nand (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise nand of this and the given bit-vector.
   */
  BitVector& ibvnand(const BitVector& bv);

  /**
   * Bit-wise nor (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise nor.
   * @param bv1 The second operand of the bit-wise nor.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise nor of the given bit-vectors.
   */
  BitVector& ibvnor(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise nor (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise nor of this and the given bit-vector.
   */
  BitVector& ibvnor(const BitVector& bv);

  /**
   * Bit-wise or (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise or.
   * @param bv1 The second operand of the bit-wise or.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise or of the given bit-vectors.
   */
  BitVector& ibvor(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise or (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise or of this and the given bit-vector.
   */
  BitVector& ibvor(const BitVector& bv);

  /**
   * Subtraction (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the subtraction.
   * @param bv1 The second operand of the subtraction.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         subtraction of the given bit-vectors.
   */
  BitVector& ibvsub(const BitVector& bv0, const BitVector& bv1);
  /**
   * Subtraction (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         subtraction of this and the given bit-vector.
   */
  BitVector& ibvsub(const BitVector& bv);

  /**
   * Bit-wise xnor (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise xnor.
   * @param bv1 The second operand of the bit-wise xnor.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise xnor of the given bit-vectors.
   */
  BitVector& ibvxnor(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise xnor (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise xnor of this and the given bit-vector.
   */
  BitVector& ibvxnor(const BitVector& bv);

  /**
   * Bit-wise xor (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the bit-wise xor.
   * @param bv1 The second operand of the bit-wise xor.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise xor of the given bit-vectors.
   */
  BitVector& ibvxor(const BitVector& bv0, const BitVector& bv1);
  /**
   * Bit-wise xor (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         bit-wise xor of this and the given bit-vector.
   */
  BitVector& ibvxor(const BitVector& bv);

  /**
   * Equality (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the equality.
   * @param bv1 The second operand of the equality.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         equality of the given bit-vectors.
   */
  BitVector& ibveq(const BitVector& bv0, const BitVector& bv1);
  /**
   * Equality (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         equality of this and the given bit-vector.
   */
  BitVector& ibveq(const BitVector& bv);

  /**
   * Disequality (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the disequality.
   * @param bv1 The second operand of the disequality.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         disequality of the given bit-vectors.
   */
  BitVector& ibvne(const BitVector& bv0, const BitVector& bv1);
  /**
   * Disequality (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         disequality of this and the given bit-vector.
   */
  BitVector& ibvne(const BitVector& bv);

  /**
   * Unsigned less than (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned less than.
   * @param bv1 The second operand of the unsigned less than.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned less than of the given bit-vectors.
   */
  BitVector& ibvult(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned less than (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned less than of this and the given bit-vector.
   */
  BitVector& ibvult(const BitVector& bv);

  /**
   * Unsigned less than or equal (in-place) of the given bit-vectors `bv0`
   * and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned less than or equal.
   * @param bv1 The second operand of the unsigned less than or equal.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned less or equal of the given bit-vectors.
   */
  BitVector& ibvule(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned less than or equal (in-place) of this bit-vector and the given
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned less than or equal of this and the given bit-vector.
   */
  BitVector& ibvule(const BitVector& bv);

  /**
   * Unsigned greater than (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned greater than.
   * @param bv1 The second operand of the unsigned greater than.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned greater than of the given bit-vectors.
   */
  BitVector& ibvugt(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned greater than (in-place) of this bit-vector and the given
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned greater than of this and the given bit-vector.
   */
  BitVector& ibvugt(const BitVector& bv);

  /**
   * Unsigned greater than or equal (in-place) of the given bit-vectors `bv0`
   * and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned greater than or equal.
   * @param bv1 The second operand of the unsigned greater than or equal.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned greater or equal of the given bit-vectors.
   */
  BitVector& ibvuge(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned greater than or equal (in-place) of this bit-vector and the given
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned greater than or equal of this and the given bit-vector.
   */
  BitVector& ibvuge(const BitVector& bv);

  /**
   * Signed less than (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the signed less than.
   * @param bv1 The second operand of the signed less than.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed less than of the given bit-vectors.
   */
  BitVector& ibvslt(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed less than (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed less than or equal of this and the given bit-vector.
   */
  BitVector& ibvslt(const BitVector& bv);

  /**
   * Signed less than or equal (in-place) of the given bit-vectors `bv0` and
   * `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned less than or equal.
   * @param bv1 The second operand of the unsigned less than or equal.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned less or equal of the given bit-vectors.
   */
  BitVector& ibvsle(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed less than or equal (in-place) of this bit-vector and the given
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed less than or equal of this and the given bit-vector.
   */
  BitVector& ibvsle(const BitVector& bv);

  /**
   * Signed greater than (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the signed greater than.
   * @param bv1 The second operand of the signed greater than.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed greater than of the given bit-vectors.
   */
  BitVector& ibvsgt(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed greater than (in-place) of this bit-vector and the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed greater than of this and the given bit-vector.
   */
  BitVector& ibvsgt(const BitVector& bv);

  /**
   * Signed greater than or equal (in-place) of the given bit-vectors `bv0` and
   * `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the signed greater than or equal.
   * @param bv1 The second operand of the signed greater than or equal.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed greater or equal of the given bit-vectors.
   */
  BitVector& ibvsge(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed greater than or equal (in-place) of this bit-vector and the given
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed greater than or equal of this and the given bit-vector.
   */
  BitVector& ibvsge(const BitVector& bv);

  /**
   * Logical left shift (in-place) of the given bit-vector by the given
   * unsigned integer value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to shift.
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the left.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical left shift.
   */
  BitVector& ibvshl(const BitVector& bv, uint64_t shift);
  /**
   * Logical left shift (in-place) of this bit-vector by the given unsigned
   * integer value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the left.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical left shift.
   */
  BitVector& ibvshl(uint64_t shift);

  /**
   * Logical left shift (in-place) of the given bit-vector by the given
   * bit-vector shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv    The bit-vector to shift.
   * @param shift The bit-vector representing the number of bits to shift `bv`.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical left shift.
   */
  BitVector& ibvshl(const BitVector& bv, const BitVector& shift);
  /**
   * Logical left shift (in-place) of this bit-vector by the given bit-vector
   * shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv A bit-vector representing the number of bits to shift
   *           this bit-vector to the left.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical left shift.
   */
  BitVector& ibvshl(const BitVector& bv);

  /**
   * Logical right shift (in-place) of of the given bit-vector by the given
   * unsigned integer shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to shift.
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical right shift.
   */
  BitVector& ibvshr(const BitVector& bv, uint64_t shift);
  /**
   * Logical right shift (in-place) of this bit-vector by the given unsigned
   * integer value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical right shift.
   */
  BitVector& ibvshr(uint64_t shift);

  /**
   * Logical right shift (in-place) of the given bit-vector by the given
   * bit-vector shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv    The bit-vector to shift.
   * @param shift The bit-vector representing the number of bits to shift `bv`.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical right shift.
   */
  BitVector& ibvshr(const BitVector& bv, const BitVector& shift);
  /**
   * Logical right shift (in-place) of this bit-vector by the given bit-vector
   * shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv A bit-vector representing the number of bits to shift
   *           this bit-vector to the right.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         logical right shift.
   */
  BitVector& ibvshr(const BitVector& bv);

  /**
   * Arithmetic right shift (in-place) of the given bit-vector by the given
   * unsigned integer shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv    The bit-vector to shift.
   * @param shift The bit-vector representing the number of bits to shift `bv`.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         arithmetic right shift.
   */
  BitVector& ibvashr(const BitVector& bv, uint64_t shift);
  /**
   * Arithmetic right shift (in-place) of this bit-vector by the given unsigned
   * integer shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param shift An unsigned integer representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         arithmetic right shift.
   */
  BitVector& ibvashr(uint64_t shift);

  /**
   * Arithmetic right shift (in-place) of the given bit-vector by the given
   * bit-vector shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv    The bit-vector to shift.
   * @param shift The bit-vector representing the number of bits to shift `bv`.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         arithmetic right shift.
   */
  BitVector& ibvashr(const BitVector& bv, const BitVector& arithmetic);
  /**
   * Arithmetic right shift (in-place) of this bit-vector by the given
   * bit-vector shift value.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param shift A bit-vector representing the number of bits to shift
   *              this bit-vector to the right.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         arithmetic right shift.
   */
  BitVector& ibvashr(const BitVector& bv);

  /**
   * Multiplication (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the multiplication.
   * @param bv1 The second operand of the multiplication.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         multiplication of the given bit-vectors.
   */
  BitVector& ibvmul(const BitVector& bv0, const BitVector& bv1);
  /**
   * Multiplication (in-place) of this bit-vector by the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         multiplication of this and the given bit-vector.
   */
  BitVector& ibvmul(const BitVector& bv);

  /**
   * Unsigned division (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned division.
   * @param bv1 The second operand of the unsigned division.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned division of the given bit-vectors.
   */
  BitVector& ibvudiv(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned division (in-place) of this bit-vector by the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned division of this and the given bit-vector.
   */
  BitVector& ibvudiv(const BitVector& bv);

  /**
   * Unsigned remainder (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the unsigned remainder.
   * @param bv1 The second operand of the unsigned remainder.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned remainder of the given bit-vectors.
   */
  BitVector& ibvurem(const BitVector& bv0, const BitVector& bv1);
  /**
   * Unsigned division (in-place) of this bit-vector by the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         unsigned remainder of this and the given bit-vector.
   */
  BitVector& ibvurem(const BitVector& bv);

  /**
   * Signed division (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the signed division.
   * @param bv1 The second operand of the signed division.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed division of the given bit-vectors.
   */
  BitVector& ibvsdiv(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed division (in-place) of this bit-vector by the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed division of this and the given bit-vector.
   */
  BitVector& ibvsdiv(const BitVector& bv);

  /**
   * Signed remainder (in-place) of the given bit-vectors `bv0` and `bv1`.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv0 The first operand of the signed remainder.
   * @param bv1 The second operand of the signed remainder.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed remainder of the given bit-vectors.
   */
  BitVector& ibvsrem(const BitVector& bv0, const BitVector& bv1);
  /**
   * Signed remainder (in-place) of this bit-vector by the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         signed remainder of this and the given bit-vector.
   */
  BitVector& ibvsrem(const BitVector& bv);

  /**
   * Concatenation (in-place) of the given bit-vectors.
   * Bit-vector `bv1` is concatenated (at the right, the lsb side) to `bv0`.
   * @param bv0 The first operand of the concatenation.
   * @param bv1 The second operand of the concatenation.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         concatenation of the given bit-vectors.
   */
  BitVector& ibvconcat(const BitVector& bv0, const BitVector& bv1);
  /**
   * Concatenation (in-place) of this bit-vector and the given bit-vector.
   * Bit-vector `bv` is concatenated (at the right, the lsb side) to this
   * bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The other bit-vector.
   * @return A reference to this bit-vector, overwritten with the result of the
   *         concatenation of this and the given bit-vector.
   */
  BitVector& ibvconcat(const BitVector& bv);

  /**
   * Extract a bit range from bit-vector `bv` (in-place).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to extract a bit range from.
   * @param idx_hi The upper bit-index of the range (inclusive).
   * @param idx_lo The lower bit-index of the range (inclusive).
   * @return A reference to this bit-vector, overwritten with the extracted
   *         bit range.
   */
  BitVector& ibvextract(const BitVector& bv, uint64_t idx_hi, uint64_t idx_lo);
  /**
   * Extract a bit range from this bit-vector (in-place).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param idx_hi The upper bit-index of the range (inclusive).
   * @param idx_lo The lower bit-index of the range (inclusive).
   * @return A reference to this bit-vector, overwritten with the extracted
   *         bit range.
   */
  BitVector& ibvextract(uint64_t idx_hi, uint64_t idx_lo);

  /**
   * Zero extension (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to zero extend.
   * @param n The number of bits to extend bit-vector `bv` with.
   * @return A reference to this bit-vector, overwritten with the zero
   *         extension.
   */
  BitVector& ibvzext(const BitVector& bv, uint64_t n);
  /**
   * Zero extension (in-place) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param n The number of bits to extend bit-vector `bv` with.
   * @return A reference to this bit-vector, overwritten with the zero
   *         extension.
   */
  BitVector& ibvzext(uint64_t n);

  /**
   * Sign extension (in-place) of the given bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to sign extend.
   * @param n The number of bits to extend bit-vector `bv` with.
   * @return A reference to this bit-vector, overwritten with the sign
   *         extension.
   */
  BitVector& ibvsext(const BitVector& bv, uint64_t n);
  /**
   * Sign extension (in-place) of this bit-vector.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param n The number of bits to extend bit-vector `bv` with.
   * @return A reference to this bit-vector, overwritten with the sign
   *         extension.
   */
  BitVector& ibvsext(uint64_t n);

  /**
   * Create an if-then-else over the given bit-vectors (in-place).
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param c A bit-vector representing the condition of the ite.
   * @param t A bit-vector representing the then branch of the ite.
   * @param e A bit-vector representing the else branch of the ite.
   * @return A reference to this bit-vector, overwritten with the ite.
   */
  BitVector& ibvite(const BitVector& c, const BitVector& t, const BitVector& e);

  /**
   * Calculate modular inverse of the given bit-vector by means of the Extended
   * Euclidean Algorithm (in-place).
   *
   * @note Bit-vector `bv` must be odd. The greatest common divisor
   *       gcd (c, 2^bw) must be (and is, in this case) always 1.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @param bv The bit-vector to compute the modular inverse for.
   * @return A reference to this bit-vector, overwritten with the modular
   *         inverse.
   */
  BitVector& ibvmodinv(const BitVector& bv);
  /**
   * Calculate modular inverse of this bit-vector by means of the Extended
   * Euclidean Algorithm (in-place).
   *
   * @note This bit-vector must be odd. The greatest common divisor
   *       gcd (c, 2^bw) must be (and is, in this case) always 1.
   *
   * @note The result of this operation is stored in-place, in this bit-vector.
   *
   * @return A reference to this bit-vector, overwritten with the modular
   *         inverse.
   */
  BitVector& ibvmodinv();

  /** Merged bit-vector operations. ----------------------------------------- */

  /**
   * Calculate the unsigned division and remainder of this bit-vector with `bv`.
   * The result of the division is stored in `quot`, and the result of the
   * remainder operation is stored in `rem`.
   * @param bv   The bit-vector to divide by.
   * @param quot The bit-vector to store the result of the division in.
   * @param rem  The bit-vector to store the result of the remainder in.
   */
  void bvudivurem(const BitVector& bv, BitVector* quot, BitVector* rem) const;

 private:
  /**
   * Normalize uint64_t value for a given bit-width.
   * The equivalent of mpz_fdiv_r_2exp for uint64_t values.
   * Compute the remainder of the division of val by 2^size, implemented
   * with shifts and a bit mask.
   * @param size The bit-width.
   * @param val  The value.
   * @return The normalized value.
   */
  static uint64_t uint64_fdiv_r_2exp(uint64_t size, uint64_t val);
  /**
   * Count leading zeros or ones.
   * @param zeros True to determine number of leading zeros, false to count
   *              number of leading ones.
   * @return The number of leading zeros/ones.
   */
  uint64_t count_leading(bool zeros) const;
  /**
   * Determine if this bit-vector can be represented with a uint64_t.
   * @param res If true, uint64_t representation is stored in `res`.
   * @return True if it can.
   */
  bool shift_is_uint64(uint64_t* res) const;
  /**
   * Get the first limb and return the number of limbs needed to represent
   * this bit-vector if all zero limbs are disregarded.
   * @param limb      The result pointer for the first limb.
   * @param nbits_rem The number of bits that spill over into the most
   *                  significant limb, assuming that all bits are
   *                  represented). Zero if the bit-width is a multiple of
   *                  n_bits_per_limb.
   * @param zeros     True for leading zeros, else ones.
   * @return The number of limbs needed to represent this bit-vector.
   */
  uint64_t get_limb(void* limb, uint64_t nbits_rem, bool zeros) const;

  /**
   * Determine whether value is stored as GMP value or uint64_t. This check
   * depends on s_native_size, i.e., for 64-bit Windows values exceeding 32
   * bit are stored as GMP value, for 64-bit Linux and macOS values exceeding
   * 64 bit are stored as GMP value.
   *
   * @return True if bit-vector wraps a GMPMpz.
   */
  bool is_gmp() const { return d_size > s_native_size; }

  /** The size of this bit-vector. */
  uint64_t d_size = 0;
  /**
   * The bit-vector value.
   *
   * Note: We use a union instead of std::variant here in order to avoid the
   *       overhead of the latter, since we already have a "tracking variable"
   *       (the size of the bit-vector, d_size). Further, we do not use a
   *       unique_ptr for d_val_gmp because we don't gain anything if it is in
   *       a union -- we have to manually destruct it anyways.
   */
  union
  {
    uint64_t d_val_uint64;
    // GMPMpz* d_val_gmp;
    mpz_t d_val_gmp;
  };
};

std::ostream& operator<<(std::ostream& out, const BitVector& bv);

}  // namespace bzla

namespace std {

/** Hash function. */
template <>
struct hash<bzla::BitVector>
{
  size_t operator()(const bzla::BitVector& bv) const;
};

}  // namespace std

#endif
