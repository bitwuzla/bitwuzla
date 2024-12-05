/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BV_BITVECTOR_DOMAIN_H
#define BZLA__BV_BITVECTOR_DOMAIN_H

#include "bv/bitvector.h"

namespace bzla {

struct BitVectorRange;
struct BitVectorBounds;
class BitVectorDomainGenerator;

/*----------------------------------------------------------------------------*/

class BitVectorDomain
{
  friend BitVectorDomainGenerator;

 public:
  /**
   * Default constructor.
   * @note Creates null (uninitialized) domain.
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
   * @param bounds   The inclusive value bounds for the factor.
   * @param limit    The maximum numbers of iterations in the wheel factorizer.
   * @return A null bit-vector if no such factor exists, or if computation
   *         exceeds `limit` iterations in the wheel factorizer.
   */
  BitVector get_factor(RNG *rng,
                       const BitVector &num,
                       const BitVectorBounds &bounds,
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
   * @param range  The inclusive value range for generated values.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           const BitVectorRange &range);
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
   * @param range  The inclusive value range for generated values.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           RNG *rng,
                           const BitVectorRange &range);
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
   * @note This function does not change the value of `d_bits` in order to not
   *       disturb sequences generated via calls to `next()` if calls to
   *       `random()` are interleaved.
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
  /** True if domain of this generator is fixed. */
  bool d_is_fixed = false;
  /** True if domain of this generator has fixed bits. */
  bool d_has_fixed_bits = false;
  /*
   * Unconstrained bits, most LSB is farthest right. Null if no next value
   * can be generated.
   * @note In the case of fixed domains, this does not represent the current
   *       value of the unconstrained bits, but the value of the fixed domain.
   */
  BitVector *d_bits = nullptr;
  /*
   * Min value of unconstrained bits.
   * @note In the case of fixed domains, this does not represent the current
   *       value of the unconstrained bits, but the value of the fixed domain.
   */
  BitVector *d_bits_min = nullptr;
  /* Max value of unconstrained bits.
   * @note In the case of fixed domains, this does not represent the current
   *       value of the unconstrained bits, but the value of the fixed domain.
   */
  BitVector *d_bits_max = nullptr;
  /* Value cache for current value, most LSB is farthest right. */
  BitVector d__bits;
  /* Value cache for min value of unconstrained bits. */
  BitVector d__bits_min;
  /* Value cache for max value of unconstrained bits. */
  BitVector d__bits_max;
};

class BitVectorDomainDualGenerator
{
 public:
  /**
   * Construct generator for values within given ranges (non-overlapping,
   * bounds are inclusive), interpreted as unsigned.
   * @param domain The domain to enumerate values for.
   * @param bounds The lower and upper range bounds.
   * @param rng    The associated random number generator. Nullptr if no
   *               random generation required.
   */
  BitVectorDomainDualGenerator(const BitVectorDomain &domain,
                               const BitVectorBounds &bounds,
                               RNG *rng = nullptr);
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
   * @note This does not change the state of the generator, i.e., the `d_bits`
   *       will not be updated. Thus, it is possible to iterate values via
   *       `next()` while interspersing calls to `random()` without disturbing
   *       the sequence of next values.
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
   * @param range  The inclusive value range for generated values.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 const BitVectorRange &range);
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
   * @param range  The inclusive value range for generated values.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 RNG *rng,
                                 const BitVectorRange &range);
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

}  // namespace bzla

#endif
