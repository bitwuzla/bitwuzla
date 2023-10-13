/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__LS_BITVECTOR_DOMAIN_H
#define BZLA__LS_BITVECTOR_DOMAIN_H

#include "bv/bitvector.h"

namespace bzla {
namespace ls {

class BitVectorDomainGenerator;

/*----------------------------------------------------------------------------*/

class BitVectorDomain
{
  friend BitVectorDomainGenerator;

 public:
  /**
   * Default constructor.
   * @note Creates null (uninitialized) domain. Only to be used for
   * pre-declaration.
   */
  BitVectorDomain() {}
  /** Construct a bit-vector domain of given size. */
  BitVectorDomain(uint64_t size);
  /** Construct a bit-vector domain ranging from 'lo' to 'hi'. */
  BitVectorDomain(const BitVector &lo, const BitVector &hi);
  /** Construct a bit-vector domain from a 3-valued string representation. */
  BitVectorDomain(const std::string &value);
  /** Construct a fixed bit-vector domain with lo = 'bv' and hi = 'bv'. */
  BitVectorDomain(const BitVector &bv);
  /** Construct a fixed bit-vector domain of given size from a uint value. */
  BitVectorDomain(uint64_t size, uint64_t value);
  /** Copy constructor. */
  BitVectorDomain(const BitVectorDomain &other);
  /** Destructor. */
  ~BitVectorDomain();

  /**
   * Determine if this domain is an uninitialized domain.
   * @return True if this domain is uninitialized.
   */
  bool is_null() const { return d_lo.is_null(); }

  /**
   * Get the size of this bit-vector domain.
   * @return The size of this domain.
   */
  uint64_t size() const;

  /**
   * Get the lower bound of this domain.
   * @return The lower bound of this domain.
   */
  const BitVector &lo() const { return d_lo; }
  /**
   * Get the upper bound of this domain.
   * @return The upper bound of this domain.
   */
  const BitVector &hi() const { return d_hi; }

  /**
   * Determine if this bit-vector domain is valid, i.e., `~lo | hi == ones`.
   * @return True if this bit-vector domain is valid, i.e., `~lo | hi == ones`.
   */
  bool is_valid() const;

  /**
   * Determine if this bit-vector domain is fixed, i.e., `lo == hi`.
   * @return True if this bit-vector domain is fixed, i.e., lo == hi.
   */
  bool is_fixed() const;
  /**
   * Determine if this bit-vector domain has fixed bits, i.e., bits that are
   * assigned to the same value in both 'hi' and 'lo'.
   * @note This check may only be called on VALID domains.
   * @return True if this domain has fixed bits.
   */
  bool has_fixed_bits() const;
  /**
   * Determine if this bit-vector domain has fixed true bits, i.e., bits that
   * are assigned true in both 'hi' and 'lo'.
   * @note This check may only be called on VALID domains.
   * @return True if this domain has fixed true bits.
   */
  bool has_fixed_bits_true() const;
  /**
   * Determine if this bit-vector domain has fixed false bits, i.e., bits that
   * are assigned false in both 'hi' and 'lo'.
   * @note This check may only be called on VALID domains.
   * @return false if this domain has fixed false bits.
   */
  bool has_fixed_bits_false() const;
  /**
   * Determine if this bit-vector domain has only fixed true bits, i.e., all
   * bits that are fixed are true bits.
   * @note This check may only be called on VALID domains.
   * @return True if this domain has only fixed true bits.
   */
  bool has_fixed_bits_true_only() const;
  /**
   * Determine if this bit-vector domain has only fixed false bits, i.e., all
   * bits that are fixed are false bits.
   * @note This check may only be called on VALID domains.
   * @return false if this domain has only fixed false bits.
   */
  bool has_fixed_bits_false_only() const;
  /**
   * Determine if bit at given index is fixed.
   * @return True if bit at given index is fixed.
   */
  bool is_fixed_bit(uint64_t idx) const;
  /**
   * Determine if bit at given index is fixed and true.
   * @return True if bit at given index is fixed and true.
   */
  bool is_fixed_bit_true(uint64_t idx) const;
  /**
   * Determine if bit at given index is fixed and false.
   * @return True if bit at given index is fixed and false.
   */
  bool is_fixed_bit_false(uint64_t idx) const;

  /**
   * Fix bit at given index to given value.
   * @param idx   The index of the bit to fix.
   * @param value The fixed value of the bit.
   */
  void fix_bit(uint64_t idx, bool value);
  /**
   * Fix domain to given value.
   * @param val The value this domain is to be fixed to.
   */
  void fix(const BitVector &val);

  /**
   * Determine if the fixed bits of this bit-vector domain are consistent with
   * the corresponding bits of the given bit-vector. That is, if a bit is fixed
   * to a value, it must have the same value in the bit-vector.
   * @param bv The bit-vector to check for consistency against.
   * @return True if the fixed bits of this domain are consistent with `bv`.
   */
  bool match_fixed_bits(const BitVector &bv) const;

  /**
   * Return a copy of the given bit-vector with all bits that are fixed in
   * this domain set to their fixed value, i.e., the returned bit-vector
   * matches all fixed bits in this domain.
   * @param bv The bit-vector.
   * @return A copy of the given bit-vector, except that all fixed bits of this
   *         domain are set to their fixed value.
   */
  BitVector get_copy_with_fixed_bits(const BitVector &bv) const;

  /** Copy assignment operator. */
  BitVectorDomain &operator=(const BitVectorDomain &other);
  /** Equality comparison operator. */
  bool operator==(const BitVectorDomain &other) const;

  /**
   * Create a bit-vector domain that represents a bit-wise not of this domain.
   * @return A domain representing the bit-wise not of this domain.
   */
  BitVectorDomain bvnot() const;
  /**
   * Create a bit-vector domain that represents a logical left shift of this
   * domain by the shift value represented as bit-vector `bv`.
   * @param bv A bit-vector representing the shift value.
   * @return A domain representing the logical left shift by `bv` of this
   *         domain.
   */
  BitVectorDomain bvshl(const BitVector &shift) const;
  /**
   * Create a bit-vector domain that represents a logical right shift of this
   * domain by the shift value represented as bit-vector `bv`.
   * @param bv A bit-vector representing the shift value.
   * @return A domain representing the logical right shift by `bv` of this
   *         domain.
   */
  BitVectorDomain bvshr(const BitVector &shift) const;
  /**
   * Create a bit-vector domain that represents an arithmetic right shift of
   * this domain by the shift value represented as bit-vector `bv`.
   * @param bv A bit-vector representing the shift value.
   * @return A domain representing the arithmetic right shift by `bv` of this
   *         domain.
   */
  BitVectorDomain bvashr(const BitVector &shift) const;
  /**
   * Create a bit-vector domain that represents a concatenation of this domain
   * with bit-vector `bv`.
   * @param bv The bit-vector to concatenate this domain with.
   * @return A domain representing a concatenation of this domain with `bv`.
   */
  BitVectorDomain bvconcat(const BitVector &bv) const;
  /**
   * Create a bit-vector domain that represents a concatenation of this domain
   * with domain `d`.
   * @param d The bit-vector domain to concatenate this domain with.
   * @return A domain representing a concatenation of this domain with `d`.
   */
  BitVectorDomain bvconcat(const BitVectorDomain &d) const;

  /**
   * Extract a bit range from this bit-vector domain.
   * @param idx_hi The upper bit-index of the range (inclusive).
   * @param idx_lo The lower bit-index of the range (inclusive).
   * @return A domain representing the given bit range of this domain.
   */
  BitVectorDomain bvextract(uint64_t idx_hi, uint64_t idx_lo) const;

  /**
   * Determine a random factor of `num > t`.
   * @param rng      The associated random number generator.
   * @param num      The value to factorize.
   * @param excl_min The exclusive minimum value of the factor.
   * @param limit    The maximum numbers of iterations in the wheel factorizer.
   * @return A null bit-vector if no such factor exists, or if computation
   *         exceeds `limit` iterations in the wheel factorizer.
   */
  BitVector get_factor(RNG *rng,
                       const BitVector &num,
                       const BitVector &excl_min,
                       uint64_t limit) const;

  /**
   * Get a string representation of this bit-vector domain.
   * Unset bits are represented as `x`, invalid bits are represented as `i`.
   * @return A string representation of this bit-vector domain.
   */
  std::string str() const;

 private:
  /**
   * The lower bound of this bit-vector domain.
   * Bits that are not fixed are set to 0. If a bit is `1` in `lo` and `0` in
   * `hi`, the domain is invalid.
   */
  BitVector d_lo;
  /**
   * The upper bound of this bit-vector domain.
   * Bits that are not fixed are set to 1. If a bit is `1` in `lo` and `0` in
   * `hi`, the domain is invalid.
   */
  BitVector d_hi;
  /** True if this domain has fixed bits. */
  bool d_has_fixed_bits = false;
};

std::ostream &operator<<(std::ostream &out, const BitVectorDomain &d);

/*----------------------------------------------------------------------------*/

class BitVectorDomainGenerator
{
 public:
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param min    The minimum value to start enumeration with.
   * @param max    The maximum value to enumerate until.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           const BitVector &min,
                           const BitVector &max);
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param rng    The associated random number generator.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain, RNG *rng);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param rng    The associated random number generator.
   * @param min    The minimum value to start enumeration with.
   * @param max    The maximum value to enumerate until.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           RNG *rng,
                           const BitVector &min,
                           const BitVector &max);
  /** Destructor. */
  ~BitVectorDomainGenerator();

  /**
   * Determine if there is a next element in the sequence.
   * @return True if not all possible values have been generated yet.
   */
  bool has_next() const;
  /**
   * Determine if generating random values is possible.
   * @return True if generating random values is possible.
   */
  bool has_random() const;
  /**
   * Generate next element in the sequence.
   * @return The next element in the sequence.
   */
  BitVector next();
  /**
   * Generate random element in the sequence.
   * @return A random element in the sequence.
   */
  BitVector random();

 private:
  /**
   * Helper for next() and random().
   * @param random True to generate a random value, else get the next value.
   */
  BitVector generate_next(bool random);
  /* The domain to enumerate values for. */
  BitVectorDomain d_domain;
  /* The associated RNG (may be 0). */
  RNG *d_rng = nullptr;
#ifndef NDEBUG
  /* We only need to cache these for debugging purposes. */
  BitVector d_min; /* the min value (in case of ranged init) */
  BitVector d_max; /* the max value (in case of ranged init) */
#endif
  /* Unconstrained bits, most LSB is farthest right. */
  std::unique_ptr<BitVector> d_bits;
  /* Min value of unconstrained bits. */
  std::unique_ptr<BitVector> d_bits_min;
  /* Max value of unconstrained bits. */
  std::unique_ptr<BitVector> d_bits_max;
};

class BitVectorDomainDualGenerator
{
 public:
  /**
   * Construct generator for values within given ranges (non-overlapping,
   * bounds are inclusive), interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param min_lo The minimum value to of the lower range (between zero and
   *               the max_signed value).
   * @param max_lo The maximum value of the lower range (between zero and
   *               the max_signed value).
   * @param min_hi The minimum value to of the upper range (between
   *               min_signed and ones).
   * @param max_hi The maximum value of the upper range (between min_signed
   *               and ones).
   */
  BitVectorDomainDualGenerator(const BitVectorDomain &domain,
                               const BitVector *min_lo,
                               const BitVector *max_lo,
                               const BitVector *min_hi,
                               const BitVector *max_hi);
  /**
   * Construct generator for values within given ranges (inclusive),
   * interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param rng    The associated random number generator.
   * @param min_lo The minimum value to of the lower range (between zero and
   *               the max_signed value).
   * @param max_lo The maximum value of the lower range (between zero and
   *               the max_signed value).
   * @param min_hi The minimum value to of the upper range (between
   *               min_signed and ones).
   * @param max_hi The maximum value of the upper range (between min_signed
   *               and ones).
   */
  BitVectorDomainDualGenerator(const BitVectorDomain &domain,
                               RNG *rng,
                               const BitVector *min_lo,
                               const BitVector *max_lo,
                               const BitVector *min_hi,
                               const BitVector *max_hi);
  /** Destructor. */
  ~BitVectorDomainDualGenerator();

  /**
   * Determine if there is a next element in the sequence.
   * @return True if not all possible values have been generated yet.
   */
  bool has_next();
  /**
   * Determine if generating random values is possible.
   * @return True if generating random values is possible.
   */
  bool has_random();
  /**
   * Generate next element in the sequence.
   * @return The next element in the sequence.
   */
  BitVector next();
  /**
   * Generate random element in the sequence.
   * @return A random element in the sequence.
   */
  BitVector random();

 protected:
  /* The associated RNG (may be 0). */
  RNG *d_rng = nullptr;
  /** The generator covering the lower range < 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_lo;
  /** The generator covering the upper range >= 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_hi;
  /** The currently active generator. */
  BitVectorDomainGenerator *d_gen_cur = nullptr;
};

class BitVectorDomainSignedGenerator
{
 public:
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as signed.
   * @param domain The domain to enumerate values for.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as signed.
   * @param domain The domain to enumerate values for.
   * @param min    The minimum value to start enumeration with.
   * @param max    The maximum value to enumerate until.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 const BitVector &min,
                                 const BitVector &max);
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as signed.
   * @param domain The domain to enumerate values for.
   * @param rng    The associated random number generator.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain, RNG *rng);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as signed.
   * @param domain The domain to enumerate values for.
   * @param rng    The associated random number generator.
   * @param min    The minimum value to start enumeration with.
   * @param max    The maximum value to enumerate until.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 RNG *rng,
                                 const BitVector &min,
                                 const BitVector &max);
  /** Destructor. */
  ~BitVectorDomainSignedGenerator();

  /**
   * Determine if there is a next element in the sequence.
   * @return True if not all possible values have been generated yet.
   */
  bool has_next();
  /**
   * Determine if generating random values is possible.
   * @return True if generating random values is possible.
   */
  bool has_random();
  /**
   * Generate next element in the sequence.
   * @return The next element in the sequence.
   */
  BitVector next();
  /**
   * Generate random element in the sequence.
   * @return A random element in the sequence.
   */
  BitVector random();

 private:
  /* The associated RNG (may be 0). */
  RNG *d_rng = nullptr;
  /** The generator covering the lower range < 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_lo;
  /** The generator covering the upper range >= 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_hi;
  /** The currently active generator. */
  BitVectorDomainGenerator *d_gen_cur = nullptr;
};

/*----------------------------------------------------------------------------*/

}  // namespace ls
}  // namespace bzla

#endif
