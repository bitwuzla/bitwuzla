#ifndef BZLALS__BITVECTOR_DOMAIN_H
#define BZLALS__BITVECTOR_DOMAIN_H

#include "bitvector.h"

namespace bzlals {

class BitVectorDomainGenerator;

/*----------------------------------------------------------------------------*/

class BitVectorDomain
{
  friend BitVectorDomainGenerator;

 public:
  /** Construct a bit-vector domain of given size. */
  BitVectorDomain(uint32_t size);
  /** Construct a bit-vector domain ranging from 'lo' to 'hi'. */
  BitVectorDomain(const BitVector &lo, const BitVector &hi);
  /** Construct a bit-vector domain from a 3-valued string representation. */
  BitVectorDomain(const std::string &value);
  /** Construct a fixed bit-vector domain with lo = 'bv' and hi = 'bv'. */
  BitVectorDomain(const BitVector &bv);
  /** Construct a fixed bit-vector domain of given size from a uint value. */
  BitVectorDomain(uint32_t size, uint64_t value);
  /** Copy constructor. */
  BitVectorDomain(const BitVectorDomain &other);
  /** Destructor. */
  ~BitVectorDomain();

  /** Return the size of this bit-vector. */
  uint32_t size() const;

  /** Get the lower bound of this domain. */
  const BitVector& lo() const { return d_lo; }
  /** Get the upper bound of this domain. */
  const BitVector& hi() const { return d_hi; }

  /** Return true if this bit-vector domain is valid, i.e., ~lo | hi == ones. */
  bool is_valid() const;

  /** Return true if this bit-vector domain is fixed, i.e., lo == hi. */
  bool is_fixed() const;
  /**
   * Return true if this bit-vector domain has fixed bits, i.e., bits that are
   * assigned to the same value in both 'hi' and 'lo'.
   * Note: This check may only be called on VALID domains.
   */
  bool has_fixed_bits() const;
  /** Return true if bit at given index is fixed. */
  bool is_fixed_bit(uint32_t idx) const;
  /** Return true if bit at given index is fixed and true. */
  bool is_fixed_bit_true(uint32_t idx) const;
  /** Return true if bit at given index is fixed and false. */
  bool is_fixed_bit_false(uint32_t idx) const;

  /** Fix bit at given index to given value. */
  void fix_bit(uint32_t idx, bool value);

  /**
   * Return true if fixed bits of this bit-vector domain are consistent with
   * the corresponding bits of the given bit-vector. That is, if a bit is fixed
   * to a value, it must have the same value in the bit-vector.
   */
  bool match_fixed_bits(const BitVector &bv) const;

  /** Copy assignment operator. */
  BitVectorDomain &operator=(const BitVectorDomain &other);
  /** Equality comparison operator. */
  bool operator==(const BitVectorDomain &other) const;

  /**
   * Create a bit-vector domain that represents a bit-wise not of this domain.
   */
  BitVectorDomain bvnot() const;
  /**
   * Create a bit-vector domain that represents a logial left shift of this
   * domain by the shift value represented as bit-vector 'bv'.
   */
  BitVectorDomain bvshl(const BitVector &shift) const;
  /**
   * Create a bit-vector domain that represents a logial right shift of this
   * domain by the shift value represented as bit-vector 'bv'.
   */
  BitVectorDomain bvshr(const BitVector &shift) const;
  /**
   * Create a bit-vector domain that represents an arithmetic right shift of
   * this domain by the shift value represented as bit-vector 'bv'.
   */
  BitVectorDomain bvashr(const BitVector &shift) const;

  /**
   * Extract a bit range from this bit-vector domain.
   * idx_hi: The upper bit-index of the range (inclusive).
   * idx_lo: The lower bit-index of the range (inclusive).
   */
  BitVectorDomain bvextract(uint32_t idx_hi, uint32_t idx_lo) const;

  /**
   * Return a string representation of this bit-vector domain.
   * Unset bits are represented as 'x', invalid bits are represented as 'i'.
   */
  std::string to_string() const;

 private:
  /**
   * The lower bound of this bit-vector domain.
   * Bits that are not fixed are set to 0. If a bit is '1' in 'lo' and '0' in
   * 'hi', the domain is invalid.
   */
  BitVector d_lo;
  /**
   * The upper bound of this bit-vector domain.
   * Bits that are not fixed are set to 1. If a bit is '1' in 'lo' and '0' in
   * 'hi', the domain is invalid.
   */
  BitVector d_hi;
  /** True if this domain has fixed bits. */
  bool d_has_fixed_bits = false;
};

/*----------------------------------------------------------------------------*/

class BitVectorDomainGenerator
{
 public:
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as unsigned.
   * domain: The domain to enumerate values for.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as unsigned.
   * domain: The domain to enumerate values for.
   * min   : The minimum value to start enumeration with.
   * max   : The maximum value to enumerate until.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           const BitVector &min,
                           const BitVector &max);
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as unsigned.
   * domain: The domain to enumerate values for.
   * rng   : The associated random number generator.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain, RNG *rng);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as unsigned.
   * domain: The domain to enumerate values for.
   * rng   : The associated random number generator.
   * min   : The minimum value to start enumeration with.
   * max   : The maximum value to enumerate until.
   */
  BitVectorDomainGenerator(const BitVectorDomain &domain,
                           RNG *rng,
                           const BitVector &min,
                           const BitVector &max);
  /** Destructor. */
  ~BitVectorDomainGenerator();

  /** Return true if not all possible values have been generated yet. */
  bool has_next() const;
  /** Return true if generating random values is possible. */
  bool has_random() const;
  /** Generate next element in the sequence. */
  BitVector next();
  /** Generate random element in the sequence. */
  BitVector random();

 private:
  BitVector generate_next(bool random);
  /* The domain to enumerate values for. */
  BitVectorDomain d_domain;
  /* The associated RNG (may be 0). */
  RNG *d_rng = nullptr;
#ifndef NDEBUG
  /* We only need to cache these for debugging purposes. */
  BitVector d_min;          /* the min value (in case of ranged init) */
  BitVector d_max;          /* the max value (in case of ranged init) */
#endif
  /* Unconstrained bits, most LSB is farthest right. */
  std::unique_ptr<BitVector> d_bits = nullptr;
  /* Min value of unconstrained bits. */
  std::unique_ptr<BitVector> d_bits_min = nullptr;
  /* Max value of unconstrained bits. */
  std::unique_ptr<BitVector> d_bits_max = nullptr;
};

class BitVectorDomainSignedGenerator
{
 public:
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as signed.
   * domain: The domain to enumerate values for.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as signed.
   * domain: The domain to enumerate values for.
   * min   : The minimum value to start enumeration with.
   * max   : The maximum value to enumerate until.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 const BitVector &min,
                                 const BitVector &max);
  /**
   * Construct generator for values within the range defined by the given
   * bit-vector domain, interpreted as signed.
   * domain: The domain to enumerate values for.
   * rng   : The associated random number generator.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain, RNG *rng);
  /**
   * Construct generator for values within given range (inclusive),
   * interpreted as signed.
   * domain: The domain to enumerate values for.
   * rng   : The associated random number generator.
   * min   : The minimum value to start enumeration with.
   * max   : The maximum value to enumerate until.
   */
  BitVectorDomainSignedGenerator(const BitVectorDomain &domain,
                                 RNG *rng,
                                 const BitVector &min,
                                 const BitVector &max);
  /** Destructor. */
  ~BitVectorDomainSignedGenerator();

  /** Return true if not all possible values have been generated yet. */
  bool has_next();
  /** Return true if generating random values is possible. */
  bool has_random();
  /** Generate next element in the sequence. */
  BitVector next();
  /** Generate random element in the sequence. */
  BitVector random();

 private:
  /* The associated RNG (may be 0). */
  RNG *d_rng = nullptr;
  /** The generator covering the lower range < 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_lo = nullptr;
  /** The generator covering the upper range >= 0. */
  std::unique_ptr<BitVectorDomainGenerator> d_gen_hi = nullptr;
  /** The currently active generator. */
  BitVectorDomainGenerator *d_gen_cur = nullptr;
};

/*----------------------------------------------------------------------------*/

}  // namespace bzlals

#endif
