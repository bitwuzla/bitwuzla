/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLABVDOMAIN_H_INCLUDED
#define BZLABVDOMAIN_H_INCLUDED

#include "bzlabv.h"

struct BzlaBvDomain
{
  BzlaBitVector *lo;
  BzlaBitVector *hi;
};

typedef struct BzlaBvDomain BzlaBvDomain;

/** Create new bit-vector domain of width 'width' with low 0 and high ~0. */
BzlaBvDomain *bzla_bvdomain_new_init(BzlaMemMgr *mm, uint32_t width);

/**
 * Create new bit-vector domain with low 'lo' and high 'hi'.
 * Creates copies of lo and hi.
 */
BzlaBvDomain *bzla_bvdomain_new(BzlaMemMgr *mm,
                                const BzlaBitVector *lo,
                                const BzlaBitVector *hi);
/**
 * Create new bit-vector domain from a 3-valued string representation.
 */
BzlaBvDomain *bzla_bvdomain_new_from_char(BzlaMemMgr *mm, const char *val);

/**
 * Create new (fixed) bit-vector domain with low 'bv' and high 'bv'.
 * Creates copies of bv.
 */
BzlaBvDomain *bzla_bvdomain_new_fixed(BzlaMemMgr *mm, const BzlaBitVector *bv);

/**
 * Create new (fixed) bit-vector domain with low 'val' and high 'val'.
 * Note: 'val' must be representable with max. 64 bits.
 */
BzlaBvDomain *bzla_bvdomain_new_fixed_uint64(BzlaMemMgr *mm,
                                             uint64_t val,
                                             uint32_t width);

/** Delete bit-vector domain. */
void bzla_bvdomain_free(BzlaMemMgr *mm, BzlaBvDomain *d);

/** Copy bit-vector domain 'd'. */
BzlaBvDomain *bzla_bvdomain_copy(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Create a new domain that represents the slice of a given domain from bit
 * index 'hi' to bit index 'lo'.
 *
 * The resulting domain 'res' is defined such that
 *   res->lo = x->lo[hi:lo] and
 *   res->hi = x->hi[hi:lo].
 */
/** Create the slice from bit index upper to lower of given the bit-vector. */
BzlaBvDomain *bzla_bvdomain_slice(BzlaMemMgr *mm,
                                  const BzlaBvDomain *d,
                                  uint32_t hi,
                                  uint32_t lo);

/** Invert fixed bits of domain 'd'. */
BzlaBvDomain *bzla_bvdomain_not(BzlaMemMgr *mm, const BzlaBvDomain *d);

/** Shift fixed bits of domain 'd' by 'bv'. */
BzlaBvDomain *bzla_bvdomain_sll(BzlaMemMgr *mm,
                                const BzlaBvDomain *d,
                                const BzlaBitVector *bv);

/*----------------------------------------------------------------------------*/

/** Get the width of the given domain.  */
uint32_t bzla_bvdomain_get_width(const BzlaBvDomain *d);

/**
 * Compare two bit-vector domains.
 * Returns true if they are equal, and false otherwise.
 */
bool bzla_bvdomain_is_equal(const BzlaBvDomain *a, const BzlaBvDomain *b);

/** Check if bit-vector domain is valid, i.e., ~lo | hi == ones. */
bool bzla_bvdomain_is_valid(BzlaMemMgr *mm, const BzlaBvDomain *d);

/** Check if bit-vector domain is fixed, i.e., lo == hi */
bool bzla_bvdomain_is_fixed(BzlaMemMgr *mm, const BzlaBvDomain *d);

/** Check if bit-vector domain has some fixed bits. */
bool bzla_bvdomain_has_fixed_bits(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Set bit at given position to fixed value (index 0 is LSB, width - 1 is MSB).
 */
void bzla_bvdomain_fix_bit(const BzlaBvDomain *d, uint32_t pos, bool value);

/** Check if bit at given position is fixed. */
bool bzla_bvdomain_is_fixed_bit(const BzlaBvDomain *d, uint32_t pos);

/** Check if bit at given position is fixed and true. */
bool bzla_bvdomain_is_fixed_bit_true(const BzlaBvDomain *d, uint32_t pos);

/** Check if bit at given position is fixed and false. */
bool bzla_bvdomain_is_fixed_bit_false(const BzlaBvDomain *d, uint32_t pos);

/**
 * Check if all fixed bits of domain 'd' match with their corresponding bits
 * of bit-vector 'bv'.
 */
bool bzla_bvdomain_check_fixed_bits(BzlaMemMgr *mm,
                                    const BzlaBvDomain *d,
                                    const BzlaBitVector *bv);

/*----------------------------------------------------------------------------*/

/**
 * Get a string representation of the given domain.
 * Unset bits are represented as 'x', invalid bits are represented as 'i'.
 * The result string must be released via bzla_mem_freestr.
 */
char *bzla_bvdomain_to_char(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Prints domain 'd' to stdout. 'print_short' indicates whether 'lo' and 'hi'
 * should be printed separately.
 */
void bzla_bvdomain_print(BzlaMemMgr *mm,
                         const BzlaBvDomain *d,
                         bool print_short);

const char *bzla_bvdomain_to_str(const BzlaBvDomain *d);

/*----------------------------------------------------------------------------*/

BzlaBitVector *bzla_bvdomain_get_factor(BzlaMemMgr *mm,
                                        const BzlaBitVector *num,
                                        const BzlaBvDomain *x,
                                        const BzlaBitVector *excl_min_val,
                                        uint64_t limit,
                                        BzlaRNG *rng);

/*----------------------------------------------------------------------------*/
/* Generator                                                                  */
/*----------------------------------------------------------------------------*/

/** A generator to enumerate all possible values of a given domain. */
struct BzlaBvDomainGenerator
{
  BzlaMemMgr *mm;          /* the associated memory manager */
  BzlaRNG *rng;            /* the associated RNG (may be 0) */
  BzlaBitVector *bits;     /* unconstrained bits, most LSB is farthest right. */
  BzlaBitVector *bits_min; /* min value of unconstrained bits */
  BzlaBitVector *bits_max; /* max value of unconstrained bits */
  BzlaBitVector *cur;      /* current value */
  BzlaBvDomain *domain;    /* the domain to enumerate values for */
  BzlaBitVector *min;      /* the min value (in case of ranged init) */
  BzlaBitVector *max;      /* the max value (in case of ranged init) */
};

typedef struct BzlaBvDomainGenerator BzlaBvDomainGenerator;

/**
 * Initialize domain generator (for unsigned value enumeration).
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 */
void bzla_bvdomain_gen_init(BzlaMemMgr *mm,
                            BzlaRNG *rng,
                            BzlaBvDomainGenerator *gen,
                            const BzlaBvDomain *d);

/**
 * Initialize generator for values within given range (inclusive),
 * interpreted as unsigned.
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 * min: the minimum value to start enumeration with
 * max: the maximum value to enumerate until
 */
void bzla_bvdomain_gen_init_range(BzlaMemMgr *mm,
                                  BzlaRNG *rng,
                                  BzlaBvDomainGenerator *gen,
                                  const BzlaBvDomain *d,
                                  const BzlaBitVector *min,
                                  const BzlaBitVector *max);

/**
 * Return true if not all possible values have been generated yet.
 *
 * Note: For bzla_bvdomain_gen_random(), this always returns true if there
 *       are any values to enumerate (i.e., the initial call to
 *       bzla_bvdomain_gen_has_next() is true).
 */
bool bzla_bvdomain_gen_has_next(const BzlaBvDomainGenerator *gen);

/** Generate next element in the sequence. */
BzlaBitVector *bzla_bvdomain_gen_next(BzlaBvDomainGenerator *gen);

/** Generate random element in the sequence. */
BzlaBitVector *bzla_bvdomain_gen_random(BzlaBvDomainGenerator *gen);

/** Delete generator and release all associated memory. */
void bzla_bvdomain_gen_delete(const BzlaBvDomainGenerator *gen);

/*----------------------------------------------------------------------------*/
/* Signed generator                                                           */
/*----------------------------------------------------------------------------*/

/** A generator to enumerate all possible values of a given domain. */
struct BzlaBvDomainSignedGenerator
{
  BzlaMemMgr *mm;                 /* the associated memory manager */
  BzlaRNG *rng;                   /* the associated RNG (may be 0) */
  BzlaBvDomain *domain;           /* the domain to enumerate values for */
  BzlaBvDomainGenerator *gen_lo;  /* generator covering the lower range < 0 */
  BzlaBvDomainGenerator *gen_hi;  /* generator covering the upper range >= 0 */
  BzlaBvDomainGenerator *gen_cur; /* the currently active generator */
};

typedef struct BzlaBvDomainSignedGenerator BzlaBvDomainSignedGenerator;

/**
 * Initialize domain generator (for signed value enumeration).
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 */
void bzla_bvdomain_gen_signed_init(BzlaMemMgr *mm,
                                   BzlaRNG *rng,
                                   BzlaBvDomainSignedGenerator *gen,
                                   const BzlaBvDomain *d);

/**
 * Initialize generator for values within given range (inclusive),
 * interpreted as signed.
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 * min: the minimum value to start enumeration with
 * max: the maximum value to enumerate until
 */
void bzla_bvdomain_gen_signed_init_range(BzlaMemMgr *mm,
                                         BzlaRNG *rng,
                                         BzlaBvDomainSignedGenerator *gen,
                                         const BzlaBvDomain *d,
                                         const BzlaBitVector *min,
                                         const BzlaBitVector *max);

/**
 * Return true if not all possible values have been generated yet.
 *
 * Note: For bzla_bvdomain_gen_signed_random(), this is always returns true if
 *       there are any values to enumerate (i.e., the initial call to
 *       bzla_bvdomain_gen_has_next() is true).
 */
bool bzla_bvdomain_gen_signed_has_next(BzlaBvDomainSignedGenerator *gen);

/** Generate next element in the sequence. */
BzlaBitVector *bzla_bvdomain_gen_signed_next(BzlaBvDomainSignedGenerator *gen);

/** Generate random element in the sequence. */
BzlaBitVector *bzla_bvdomain_gen_signed_random(
    BzlaBvDomainSignedGenerator *gen);

/** Delete generator and release all associated memory. */
void bzla_bvdomain_gen_signed_delete(const BzlaBvDomainSignedGenerator *gen);

/*----------------------------------------------------------------------------*/

#endif
