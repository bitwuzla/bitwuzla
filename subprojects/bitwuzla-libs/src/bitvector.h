#ifndef BZLALS__BITVECTOR_H
#define BZLALS__BITVECTOR_H

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

  /** Return true if string in base fits into a BitVector of given size. */
  static bool fits_in_size(uint32_t size,
                           const std::string& str,
                           uint32_t base);
  /** Return true if given value fits into a BitVector of given size. */
  static bool fits_in_size(uint32_t size, uint64_t value, bool sign = false);
  /** Create a true bit-vector (value 1 of size 1). */
  static BitVector mk_true();
  /** Create a false bit-vector (value 0 of size 1). */
  static BitVector mk_false();
  /** Create a zero bit-vector of given size. */
  static BitVector mk_zero(uint32_t size);
  /** Create a one bit-vector of given size. */
  static BitVector mk_one(uint32_t size);
  /** Create a ones bit-vector of given size. */
  static BitVector mk_ones(uint32_t size);
  /** Create a minimum signed value bit-vector of given size. */
  static BitVector mk_min_signed(uint32_t size);
  /** Create a maximum signed value bit-vector of given size. */
  static BitVector mk_max_signed(uint32_t size);

  /**
   * Create a if-then-else over the given bit-vectors.
   * c: The condition.
   * t: The then branch.
   * e: The else branch.
   */
  static BitVector bvite(const BitVector& c,
                         const BitVector& t,
                         const BitVector& e);

  /** Default constructor. */
  BitVector();
  /** Construct a zero bit-vector of given size. */
  BitVector(uint32_t size);
  /** Construct a random bit-vector of given size. */
  BitVector(uint32_t size, RNG& rng);

  /**
   * Construct a random bit-vector of given size with the given range.
   * size: The size of the bit-vector.
   * rng : Random number generator.
   * from: Lower bound of given range (inclusive).
   * to  : Upper bound of given range (inclusive).
   * sign: True to interpret the given range as signed, else unsigned.
   */
  BitVector(uint32_t size,
            RNG& rng,
            const BitVector& from,
            const BitVector& to,
            bool sign = false);
  /**
   * Construct a new bit-vector of given size and randomly set bits within given
   * index range. Bits outside of given index range are initialized with zero.
   */
  BitVector(uint32_t size, RNG& rng, uint32_t idx_hi, uint32_t idx_lo);

  /**
   * Construct a bit-vector of given size from given binary string.
   * size : The bit-vector size, must be >= the length of 'value'.
   * value: A string representing the value of the bit-vector. If the
   *        length of this string is > 'size', the value is zero extended.
   * base : The base the string is given in, 2 for binary, 10 for decimal,
   *        16 for hexadecimal.
   */
  BitVector(uint32_t size, const std::string& value, uint32_t base = 2);

  /**
   * Construct a bit-vector of given size from given uint64 value.
   * size : The bit-vector size.
   * value: A uint64 (when unsigned) or int64 (when signed) representing the
   *        bit-vector value. The value must be representable with 'size' bits.
   * sign : True if given value should be interpreted as signed integer.
   */
  BitVector(uint32_t size, uint64_t value, bool sign = false);

  /** Copy constructor. */
  BitVector(const BitVector& other);
  /** Move constructor. */
  BitVector(BitVector&& other);

  /** Destructor. */
  ~BitVector();

  /** Copy assignment operator. */
  BitVector& operator=(const BitVector& other);

  size_t hash() const;

  /** Return true if this is an uninitialized bit-vector. */
  bool is_null() const { return d_size == 0; }

  /** Set the value of this bit-vector to the given unsigned (in-place). */
  void iset(uint64_t value);
  /** Set the value of this bit-vector to the value of 'bv' (in-place). */
  void iset(const BitVector& bv);
  /**
   * Set the value of this bit-vector to a random value between 'from' and 'to'
   * (in-place).
   */
  void iset(RNG& rng,
            const BitVector& from,
            const BitVector& to,
            bool is_signed);

  /** Equality comparison operator. */
  bool operator==(const BitVector& bv);
  /** Disequality comparison operator. */
  bool operator!=(const BitVector& bv);

  /**
   * Return a string representation of this bit-vector.
   * base: 2 for binary representation, 10 for decimal representation, 16 for
   *       hexadecimal representation.
   */
  std::string to_string(uint32_t base = 2) const;
  /**
   * Return a uint64_t representation of this bit-vector.
   * Size of this bit-vector must be <= 64.
   */
  uint64_t to_uint64() const;

  /** Return the size of this bit-vector. */
  uint32_t size() const { return d_size; }

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

  /** Return true if the bit at given index is 1, and false otherwise. */
  bool get_bit(uint32_t idx) const;
  /** Set the bit at given index to the given value. */
  void set_bit(uint32_t idx, bool value);
  /** Flip the bit at given index (in-place). */
  void flip_bit(uint32_t idx);
  /** Return true if the lsb (index 0) is 1, and false otherwise. */
  bool get_lsb() const;
  /** Return true if the msb (index size - 1) is 1, and false otherwise. */
  bool get_msb() const;

  /** Return true if this bit-vector is one and of size 1. */
  bool is_true() const;
  /** Return true if this bit-vector is zero and of size 1. */
  bool is_false() const;
  /** Return true if this bit-vector is zero. */
  bool is_zero() const;
  /** Return true if this bit-vector is ones (a bit-vector of all 1 bits). */
  bool is_ones() const;
  /** Return true if this bit-vector is one. */
  bool is_one() const;
  /** Return true if this bit-vector is the minimum signed value. */
  bool is_min_signed() const;
  /** Return true if this bit-vector is the maximum signed value. */
  bool is_max_signed() const;

  /** Return true if this bit-vector is a power of two. */
  bool is_power_of_two() const;

  /**
   * Return true if the addition of this and the given bit-vector produces an
   * overflow.
   */
  bool is_uadd_overflow(const BitVector& bv) const;
  /**
   * Return true if the multiplication of this and the given bit-vector
   * produces an overflow.
   */
  bool is_umul_overflow(const BitVector& bv) const;

  /** Get number of trailing zeros (counted from lsb). */
  uint32_t count_trailing_zeros() const;
  /** Get number of leading zeros (counted from msb). */
  uint32_t count_leading_zeros() const;
  /** Get number of leading ones (counted from msb). */
  uint32_t count_leading_ones() const;

  /* ----------------------------------------------------------------------- */
  /* Bit-vector operations.                                                  */
  /* ----------------------------------------------------------------------- */

  /** Two's complement negation. */
  BitVector bvneg() const;
  /** Bit-wise negation. */
  BitVector bvnot() const;
  /** Increment. */
  BitVector bvinc() const;
  /** Decrement. */
  BitVector bvdec() const;
  /** And reduction. Returns true bit-vector if all bits are 1, else false. */
  BitVector bvredand() const;
  /** Or reduction. Returns true bit-vector if one bit is 1, else false. */
  BitVector bvredor() const;

  /** Addition. */
  BitVector bvadd(const BitVector& bv) const;
  /** Subtraction. */
  BitVector bvsub(const BitVector& bv) const;
  /** Bit-wise and. */
  BitVector bvand(const BitVector& bv) const;
  /** Implication. */
  BitVector bvimplies(const BitVector& bv) const;
  /** Bit-wise nand. */
  BitVector bvnand(const BitVector& bv) const;
  /** Bit-wise nor. */
  BitVector bvnor(const BitVector& bv) const;
  /** Bit-wise or. */
  BitVector bvor(const BitVector& bv) const;
  /** Bit-wise xnor. */
  BitVector bvxnor(const BitVector& bv) const;
  /** Bit-wise xor. */
  BitVector bvxor(const BitVector& bv) const;
  /** Equality. */
  BitVector bveq(const BitVector& bv) const;
  /** Disequality. */
  BitVector bvne(const BitVector& bv) const;
  /** Unsigned less than. */
  BitVector bvult(const BitVector& bv) const;
  /** Unsigned less than or equal. */
  BitVector bvule(const BitVector& bv) const;
  /** Unsigned greater than. */
  BitVector bvugt(const BitVector& bv) const;
  /** Unsigned greater than or equal. */
  BitVector bvuge(const BitVector& bv) const;
  /** Signed less than. */
  BitVector bvslt(const BitVector& bv) const;
  /** Signed less than or equal. */
  BitVector bvsle(const BitVector& bv) const;
  /** Signed greater than. */
  BitVector bvsgt(const BitVector& bv) const;
  /** Signed greater than or equal. */
  BitVector bvsge(const BitVector& bv) const;
  /** Logical left shift. Shift value is given as an unsigned integer. */
  BitVector bvshl(uint32_t shift) const;
  /** Logical left shift. Shift value is given as a bit-vector. */
  BitVector bvshl(const BitVector& bv) const;
  /** Logical right shift. Shift value is given as an unsigned integer. */
  BitVector bvshr(uint32_t shift) const;
  /** Logical right shift. Shift value is given as a bit-vector. */
  BitVector bvshr(const BitVector& bv) const;
  /** Arightmetic right shift. Shift value is given as an unsigned integer. */
  BitVector bvashr(uint32_t shift) const;
  /** Arithmetic right shift. Shift value is given as a bit-vector. */
  BitVector bvashr(const BitVector& bv) const;
  /** Multiplication. */
  BitVector bvmul(const BitVector& bv) const;
  /** Unsigned division. */
  BitVector bvudiv(const BitVector& bv) const;
  /** Unsigned remainder. */
  BitVector bvurem(const BitVector& bv) const;
  /** Signed division. */
  BitVector bvsdiv(const BitVector& bv) const;
  /** Signed remainder. */
  BitVector bvsrem(const BitVector& bv) const;

  /**
   * Concatenation.
   * Given bit-vector is concatenated (at the right, the lsb side) to this
   * bit-vector.
   */
  BitVector bvconcat(const BitVector& bv) const;

  /**
   * Extract a bit range from this bit-vector.
   * idx_hi: The upper bit-index of the range (inclusive).
   * idx_lo: The lower bit-index of the range (inclusive).
   */
  BitVector bvextract(uint32_t idx_hi, uint32_t idx_lo) const;

  /**
   * Zero extension.
   * n: The number of bits to extend this bit-vector with.
   */
  BitVector bvzext(uint32_t n) const;
  /**
   * Sign extension.
   * n: The number of bits to extend this bit-vector with.
   */
  BitVector bvsext(uint32_t n) const;

  /**
   * Calculate modular inverse for this bit-vector by means of the Extended
   * Euclidian Algorithm.
   *
   * Note: Bit-vector must be odd. The greatest common divisor gcd (c, 2^bw)
   *       must be (and is, in this case) always 1.
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

  /** Two's complement negation (in-place) of 'bv'. */
  BitVector& ibvneg(const BitVector& bv);
  /** Two's complement negation (in-place) of this bit-vector. */
  BitVector& ibvneg();

  /** Bit-wise negation (in-place) of 'bv'. */
  BitVector& ibvnot(const BitVector& bv);
  /** Bit-wise negation (in-place) of this bit-vector. */
  BitVector& ibvnot();

  /** Increment (in-place) of 'bv'.  */
  BitVector& ibvinc(const BitVector& bv);
  /** Increment (in-place, chainable) of this bit-vector. */
  BitVector& ibvinc();

  /** Decrement (in-place) of 'bv'. */
  BitVector& ibvdec(const BitVector& bv);
  /** Decrement (in-place, chainable) of this bit-vector. */
  BitVector& ibvdec();

  /**
   * And reduction (in-place) of 'bv'.
   * Result is a true bit-vector if all bits of 'bv' are 1, and a false
   * bit-vector otherwise.
   */
  BitVector& ibvredand(const BitVector& bv);
  /**
   * And reduction (in-place, chainable) of this bit-vector.
   * Result is a true bit-vector if all bits of this bit-vector are 1, and a
   * false bit-vector otherwise.
   */
  BitVector& ibvredand();

  /**
   * Or reduction (in-place) of 'bv'.
   * Result is a true bit-vector if one bit of 'bv' is 1, and a false
   * bit-vector otherwise.
   */
  BitVector& ibvredor(const BitVector& bv);
  /**
   * Or reduction (in-place, chainable) of this bit-vector.
   * Result is a true bit-vector if one bit of this bit-vector is 1, and a
   * false bit-vector otherwise.
   */
  BitVector& ibvredor();

  /** Addition (in-place)  'bv0' and 'bv1'. */
  BitVector& ibvadd(const BitVector& bv0, const BitVector& bv1);
  /** Addition (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvadd(const BitVector& bv);

  /** Bit-wise and (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvand(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise and (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvand(const BitVector& bv);

  /** Implication (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvimplies(const BitVector& bv0, const BitVector& bv1);
  /** Implication (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvimplies(const BitVector& bv);

  /** Bit-wise nand (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvnand(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise nand (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvnand(const BitVector& bv);

  /** Bit-wise nor (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvnor(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise nor (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvnor(const BitVector& bv);

  /** Bit-wise or (in-place). */
  BitVector& ibvor(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise or (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvor(const BitVector& bv);

  /** Subtraction (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsub(const BitVector& bv0, const BitVector& bv1);
  /** Subtraction (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvsub(const BitVector& bv);

  /** Bit-wise xnor (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvxnor(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise xnor (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvxnor(const BitVector& bv);

  /** Bit-wise xor (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvxor(const BitVector& bv0, const BitVector& bv1);
  /** Bit-wise xor (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvxor(const BitVector& bv);

  /** Equality (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibveq(const BitVector& bv0, const BitVector& bv1);
  /** Equality (in-place) of this bit-vector and 'bv'. */
  BitVector& ibveq(const BitVector& bv);

  /** Disequality (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvne(const BitVector& bv0, const BitVector& bv1);
  /** Disequality (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvne(const BitVector& bv);

  /** Unsigned less than (in-place) of 'bv0' and 'bv1. */
  BitVector& ibvult(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned less than (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvult(const BitVector& bv);

  /** Unsigned less than or equal (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvule(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned less than or equal (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvule(const BitVector& bv);

  /** Unsigned greater than (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvugt(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned greater than (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvugt(const BitVector& bv);

  /** Unsigned greater than or equal (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvuge(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned greater than or equal (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvuge(const BitVector& bv);

  /** Signed less than (in-place) of 'bv0' and 'bv1. */
  BitVector& ibvslt(const BitVector& bv0, const BitVector& bv1);
  /** Signed less than (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvslt(const BitVector& bv);

  /** Signed less than or equal (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsle(const BitVector& bv0, const BitVector& bv1);
  /** Signed less than or equal (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvsle(const BitVector& bv);

  /** Signed greater than (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsgt(const BitVector& bv0, const BitVector& bv1);
  /** Signed greater than (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvsgt(const BitVector& bv);

  /** Signed greater than or equal (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsge(const BitVector& bv0, const BitVector& bv1);
  /** Signed greater than or equal (in-place) of this bit-vector and 'bv'. */
  BitVector& ibvsge(const BitVector& bv);

  /**
   * Logical left shift (in-place) of 'bv' by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvshl(const BitVector& bv, uint32_t shift);
  /**
   * Logical left shift (in-place) of this bit-vector by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvshl(uint32_t shift);

  /**
   * Logical left shift (in-place) of 'bv0' by 'bv1'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvshl(const BitVector& bv0, const BitVector& bv1);
  /**
   * Logical left shift (in-place) of this bit-vector by 'bv'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvshl(const BitVector& bv);

  /**
   * Logical right shift (in-place) of 'bv' by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvshr(const BitVector& bv, uint32_t shift);
  /**
   * Logical right shift (in-place) of this bit-vector by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvshr(uint32_t shift);

  /**
   * Logical right shift (in-place) of 'bv0' by 'bv1'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvshr(const BitVector& bv0, const BitVector& bv1);
  /**
   * Logical right shift (in-place) of this bit-vector by 'bv'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvshr(const BitVector& bv);

  /**
   * Arithmetic right shift (in-place) of 'bv' by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvashr(const BitVector& bv0, uint32_t shift);
  /**
   * Arithmetic right shift (in-place) of this bit-vector by 'shift'.
   * Shift value is given as an unsigned integer.
   */
  BitVector& ibvashr(uint32_t shift);

  /**
   * Arithmetic right shift (in-place) of 'bv0' by 'bv1'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvashr(const BitVector& bv0, const BitVector& bv1);
  /**
   * Arithmetic right shift (in-place) of this bit-vector by 'bv'.
   * Shift value is given as a bit-vector.
   */
  BitVector& ibvashr(const BitVector& bv);

  /** Multiplication (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvmul(const BitVector& bv0, const BitVector& bv1);
  /** Multiplication (in-place) of this bit-vector by 'bv'. */
  BitVector& ibvmul(const BitVector& bv);

  /** Unsigned division (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvudiv(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned division (in-place) of this bit-vector by 'bv'. */
  BitVector& ibvudiv(const BitVector& bv);

  /** Unsigned remainder (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvurem(const BitVector& bv0, const BitVector& bv1);
  /** Unsigned division (in-place) of this bit-vector by 'bv'. */
  BitVector& ibvurem(const BitVector& bv);

  /** Signed division (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsdiv(const BitVector& bv0, const BitVector& bv1);
  /** Signed division (in-place) of this bit-vector by 'bv'. */
  BitVector& ibvsdiv(const BitVector& bv);

  /** Signed remainder (in-place) of 'bv0' and 'bv1'. */
  BitVector& ibvsrem(const BitVector& bv0, const BitVector& bv1);
  /** Signed remainder (in-place) of this bit-vector by 'bv'. */
  BitVector& ibvsrem(const BitVector& bv);

  /**
   * Concatenation (in-place) of 'bv0' and 'bv1'.
   * Bit-vector 'bv1' is concatenated (at the right, the lsb side) to 'bv0'.
   */
  BitVector& ibvconcat(const BitVector& bv0, const BitVector& bv1);
  /**
   * Concatenation (in-place) of this bit-vector and 'bv'.
   * Bit-vector 'bv' is concatenated (at the right, the lsb side) to this
   * bit-vector.
   */
  BitVector& ibvconcat(const BitVector& bv);

  /**
   * Extract a bit range from bit-vector 'bv' (in-place).
   * idx_hi: The upper bit-index of the range (inclusive).
   * idx_lo: The lower bit-index of the range (inclusive).
   */
  BitVector& ibvextract(const BitVector& bv, uint32_t idx_hi, uint32_t idx_lo);
  /**
   * Extract a bit range from this bit-vector (in-place).
   * idx_hi: The upper bit-index of the range (inclusive).
   * idx_lo: The lower bit-index of the range (inclusive).
   */
  BitVector& ibvextract(uint32_t idx_hi, uint32_t idx_lo);

  /**
   * Zero extension (in-place) of 'bv'.
   * n: The number of bits to extend bit-vector 'bv' with.
   */
  BitVector& ibvzext(const BitVector& bv, uint32_t n);
  /**
   * Zero extension (in-place) of this bit-vector.
   * n: The number of bits to extend bit-vector 'bv' with.
   */
  BitVector& ibvzext(uint32_t n);

  /**
   * Sign extension (in-place).
   * n: The number of bits to extend bit-vector 'bv' with.
   */
  BitVector& ibvsext(const BitVector& bv, uint32_t n);
  /**
   * Sign extension (in-place) of this bit-vector.
   * n: The number of bits to extend bit-vector 'bv' with.
   */
  BitVector& ibvsext(uint32_t n);

  /**
   * Create an if-then-else over the given bit-vectors (in-place).
   * c: The condition.
   * t: The then branch.
   * e: The else branch.
   */
  BitVector& ibvite(const BitVector& c, const BitVector& t, const BitVector& e);

  /**
   * Calculate modular inverse for 'bv' by means of the Extended
   * Euclidian Algorithm (in-place).
   *
   * Note: Bit-vector 'bv' must be odd. The greatest common divisor
   *       gcd (c, 2^bw) must be (and is, in this case) always 1.
   */
  BitVector& ibvmodinv(const BitVector& bv);
  /**
   * Calculate modular inverse for this bit-vector by means of the Extended
   * Euclidian Algorithm (in-place).
   *
   * Note: This bit-vector must be odd. The greatest common divisor
   *       gcd (c, 2^bw) must be (and is, in this case) always 1.
   */
  BitVector& ibvmodinv();

  /** Merged bit-vector operations. ----------------------------------------- */

  /**
   * Calculate the unsigned division and remainder of this bit-vector with 'bv'.
   * The result of the division is stored in 'quot', and the result of the
   * remainder operation is stored in 'rem'.
   */
  void bvudivurem(const BitVector& bv, BitVector* quot, BitVector* rem) const;

 private:
  /**
   * Normalize uint64_t value for a given bit-width.
   * The equivalent of mpz_fdiv_r_2exp for uint64_t values.
   * Compute the remainder of the division of val by 2^size, implemented
   * with shifts and a bit mask.
   */
  static uint64_t uint64_fdiv_r_2exp(uint32_t size, uint64_t val);
  /**
   * Count leading zeros or ones.
   * zeros: True to determine number of leading zeros, false to count number
   *        of leading ones.
   */
  uint32_t count_leading(bool zeros) const;
  /**
   * Return true if this bit-vector can be represented with a uint64_t.
   * If true, uint64_t representation is stored in 'res'.
   */
  bool shift_is_uint64(uint32_t* res) const;
  /**
   * Get the first limb and return the number of limbs needed to represented
   * given bit-vector if all zero limbs are disregarded.
   */
  uint32_t get_limb(void* limb, uint32_t nbits_rem, bool zeros) const;

  /** True if bit-vector is of size > 64 and thus wraps a GMPMpz. */
  bool is_gmp() const { return d_size > 64; }

  /** The size of this bit-vector. */
  uint32_t d_size = 0;
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
