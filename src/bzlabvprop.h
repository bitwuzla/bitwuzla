/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018-2020 Mathias Preiner.
 *  Copyright (C) 2018-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLABVPROP_H_INCLUDED
#define BZLABVPROP_H_INCLUDED

#include "bzlabv.h"

/*----------------------------------------------------------------------------*/

struct BzlaBvDomain
{
  BzlaBitVector *lo;
  BzlaBitVector *hi;
};

typedef struct BzlaBvDomain BzlaBvDomain;

/*----------------------------------------------------------------------------*/

/** Create new bit-vector domain of width 'width' with low 0 and high ~0. */
BzlaBvDomain *bzla_bvprop_new_init(BzlaMemMgr *mm, uint32_t width);

/**
 * Create new bit-vector domain with low 'lo' and high 'hi'.
 * Creates copies of lo and hi.
 */
BzlaBvDomain *bzla_bvprop_new(BzlaMemMgr *mm,
                              const BzlaBitVector *lo,
                              const BzlaBitVector *hi);
/**
 * Create new bit-vector domain from a 3-valued string representation.
 */
BzlaBvDomain *bzla_bvprop_new_from_char(BzlaMemMgr *mm, const char *val);

/**
 * Create new (fixed) bit-vector domain with low 'bv' and high 'bv'.
 * Creates copies of bv.
 */
BzlaBvDomain *bzla_bvprop_new_fixed(BzlaMemMgr *mm, const BzlaBitVector *bv);

/**
 * Create new (fixed) bit-vector domain with low 'val' and high 'val'.
 * Note: 'val' must be representable with max. 64 bits.
 */
BzlaBvDomain *bzla_bvprop_new_fixed_uint64(BzlaMemMgr *mm,
                                           uint64_t val,
                                           uint32_t width);

/** Delete bit-vector domain. */
void bzla_bvprop_free(BzlaMemMgr *mm, BzlaBvDomain *d);

/** Copy bit-vector domain 'd'. */
BzlaBvDomain *bzla_bvprop_copy(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Compare two bit-vector domains.
 * Returns true if they are equal, and false otherwise.
 */
bool bzla_bvprop_is_equal(const BzlaBvDomain *a, const BzlaBvDomain *b);

/*----------------------------------------------------------------------------*/

/** Get the width of the given domain.  */
uint32_t bzla_bvprop_get_width(const BzlaBvDomain *d);

/** Check if bit-vector domain is valid, i.e., ~lo | hi == ones. */
bool bzla_bvprop_is_valid(BzlaMemMgr *mm, const BzlaBvDomain *d);

/** Check if bit-vector domain is fixed, i.e., lo == hi */
bool bzla_bvprop_is_fixed(BzlaMemMgr *mm, const BzlaBvDomain *d);

/** Check if bit-vector domain has some fixed bits. */
bool bzla_bvprop_has_fixed_bits(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Set bit at given position to fixed value (index 0 is LSB, width - 1 is MSB).
 */
void bzla_bvprop_fix_bit(const BzlaBvDomain *d, uint32_t pos, bool value);

/** Check if bit at given position is fixed. */
bool bzla_bvprop_is_fixed_bit(const BzlaBvDomain *d, uint32_t pos);

/** Check if bit at given position is fixed and true. */
bool bzla_bvprop_is_fixed_bit_true(const BzlaBvDomain *d, uint32_t pos);

/** Check if bit at given position is fixed and false. */
bool bzla_bvprop_is_fixed_bit_false(const BzlaBvDomain *d, uint32_t pos);

/**
 * Check if fixed bit of given domain are consistent with given bit-vector,
 * i.e., if a bit is fixed to a value in the domain, it must have the same
 * value in the bit-vector.
 */
bool bzla_bvprop_is_consistent(BzlaBvDomain *d, BzlaBitVector *bv);

/**
 * Check if all fixed bits of domain 'd' match with their corresponding bits
 * of bit-vector 'bv'.
 */
bool bzla_bvprop_check_fixed_bits(BzlaMemMgr *mm,
                                  const BzlaBvDomain *d,
                                  const BzlaBitVector *bv);

/*----------------------------------------------------------------------------*/

/**
 * Get a string representation of the given domain.
 * Unset bits are represented as 'x', invalid bits are represented as 'i'.
 * The result string must be released via bzla_mem_freestr.
 */
char *bzla_bvprop_to_char(BzlaMemMgr *mm, const BzlaBvDomain *d);

/**
 * Prints domain 'd' to stdout. 'print_short' indicates whether 'lo' and 'hi'
 * should be printed separately.
 */
void bzla_bvprop_print(BzlaMemMgr *mm, const BzlaBvDomain *d, bool print_short);

/*----------------------------------------------------------------------------*/

/**
 * Propagate domains 'd_x', 'd_y', and 'd_z' of z = (x = y).
 * If 'res_d_*' is NULL no result will be stored. Note that the propagator will
 * stop propagating as soon as one invalid domain was computed.
 */
bool bzla_bvprop_eq(BzlaMemMgr *mm,
                    BzlaBvDomain *d_x,
                    BzlaBvDomain *d_y,
                    BzlaBvDomain *d_z,
                    BzlaBvDomain **res_d_x,
                    BzlaBvDomain **res_d_y,
                    BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x' and 'd_z' of z = ~x. */
bool bzla_bvprop_not(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x' and 'd_z' of z = x << n where n is const. */
bool bzla_bvprop_sll_const(BzlaMemMgr *mm,
                           BzlaBvDomain *d_x,
                           BzlaBvDomain *d_z,
                           BzlaBitVector *n,
                           BzlaBvDomain **res_d_x,
                           BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x' and 'd_z' of z = x >> n where n is const. */
bool bzla_bvprop_srl_const(BzlaMemMgr *mm,
                           BzlaBvDomain *d_x,
                           BzlaBvDomain *d_z,
                           BzlaBitVector *n,
                           BzlaBvDomain **res_d_x,
                           BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x & y. */
bool bzla_bvprop_and(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x' and 'd_z' of z = x << y where y is not const.
 * Note: bw(y) = log_2 bw(y).
 */
bool bzla_bvprop_sll(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x' and 'd_z' of z = x >> y where y is not const.
 * Note: bw(y) = log_2 bw(y).
 */
bool bzla_bvprop_srl(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool bzla_bvprop_or(BzlaMemMgr *mm,
                    BzlaBvDomain *d_x,
                    BzlaBvDomain *d_y,
                    BzlaBvDomain *d_z,
                    BzlaBvDomain **res_d_x,
                    BzlaBvDomain **res_d_y,
                    BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x | y. */
bool bzla_bvprop_xor(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x' and 'd_z' of z = x[upper:lower]. */
bool bzla_bvprop_slice(BzlaMemMgr *mm,
                       BzlaBvDomain *d_x,
                       BzlaBvDomain *d_z,
                       uint32_t upper,
                       uint32_t lower,
                       BzlaBvDomain **res_d_x,
                       BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x o y. */
bool bzla_bvprop_concat(BzlaMemMgr *mm,
                        BzlaBvDomain *d_x,
                        BzlaBvDomain *d_y,
                        BzlaBvDomain *d_z,
                        BzlaBvDomain **res_d_y,
                        BzlaBvDomain **res_d_x,
                        BzlaBvDomain **res_d_z);

/** Propagate domains 'd_x' and 'd_z' of z = sext(x, n). */
bool bzla_bvprop_sext(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z);

/** Propagate domains 'd_c', 'd_x', 'd_y' and 'd_z' of z = ite(c, x, y). */
bool bzla_bvprop_ite(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain *d_c,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z,
                     BzlaBvDomain **res_d_c);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x + y. */
bool bzla_bvprop_add(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x', 'd_y' and 'd_z' of z = x + y where + does not
 * overflow if no_overflows = true.
 */
bool bzla_bvprop_add_aux(BzlaMemMgr *mm,
                         BzlaBvDomain *d_x,
                         BzlaBvDomain *d_y,
                         BzlaBvDomain *d_z,
                         BzlaBvDomain **res_d_x,
                         BzlaBvDomain **res_d_y,
                         BzlaBvDomain **res_d_z,
                         bool no_overflows);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x * y. */
bool bzla_bvprop_mul(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x', 'd_y' and 'd_z' of z = x * y where * does not
 * overflow if no_overflows = true.
 */
bool bzla_bvprop_mul_aux(BzlaMemMgr *mm,
                         BzlaBvDomain *d_x,
                         BzlaBvDomain *d_y,
                         BzlaBvDomain *d_z,
                         BzlaBvDomain **res_d_x,
                         BzlaBvDomain **res_d_y,
                         BzlaBvDomain **res_d_z,
                         bool no_overflows);

/** Propagate domains 'd_x', 'd_y' and 'd_z' of z = x < y (unsigned lt). */
bool bzla_bvprop_ult(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_z,
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x', 'd_y' and 'd_z' of z = x / y (unsigned division).
 */
bool bzla_bvprop_udiv(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_y,
                      BzlaBvDomain *d_z,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_y,
                      BzlaBvDomain **res_d_z);

/**
 * Propagate domains 'd_x', 'd_y' and 'd_z' of z = x % y (unsigned remainder).
 */
bool bzla_bvprop_urem(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_y,
                      BzlaBvDomain *d_z,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_y,
                      BzlaBvDomain **res_d_z);

/*----------------------------------------------------------------------------*/
/* generator */
/*----------------------------------------------------------------------------*/

/** A generator to enumerate all possible values of a given domain. */
struct BzlaBvDomainGenerator
{
  BzlaMemMgr *mm;       /* the associated memory manager */
  BzlaRNG *rng;         /* the associated RNG (may be 0) */
  uint32_t n_gen;       /* number of generated values (for non-ranged init) */
  uint32_t n_max;       /* the max number of values (for non-ranged init) */
  BzlaBitVector *bits;  /* unconstrained bits, most LSB is farthest right. */
  BzlaBitVector *next;  /* next value */
  BzlaBitVector *cur;   /* current value */
  BzlaBvDomain *domain; /* the domain to enumerate values for */
  BzlaBitVector *min;   /* the min value (in case of ranged init) */
  BzlaBitVector *max;   /* the max value (in case of ranged init) */
};

typedef struct BzlaBvDomainGenerator BzlaBvDomainGenerator;

/**
 * Initialize domain generator.
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 */
void bzla_bvprop_gen_init(BzlaMemMgr *mm,
                          BzlaRNG *rng,
                          BzlaBvDomainGenerator *gen,
                          const BzlaBvDomain *d);

/**
 * Initialize generator for values within given range (inclusive).
 * mm : the associated memory manager
 * rng: the associated random number generator, may be 0
 * gen: the generator to be initialized
 * d  : the domain to enumerate values for
 * min: the minimum value to start enumeration with
 * max: the maximum value to enumerate until
 */
void bzla_bvprop_gen_init_range(BzlaMemMgr *mm,
                                BzlaRNG *rng,
                                BzlaBvDomainGenerator *gen,
                                const BzlaBvDomain *d,
                                BzlaBitVector *min,
                                BzlaBitVector *max);

/**
 * Return true if not all possible values have been generated yet.
 * Note: For bzla_bvprop_gen_random(), this is always returns true if there
 *       are any values to enumerate (i.e., the initial call to
 *       bzla_bvprop_gen_has_next() is true).
 */
bool bzla_bvprop_gen_has_next(const BzlaBvDomainGenerator *gen);

/** Generate next element in the sequence. */
BzlaBitVector *bzla_bvprop_gen_next(BzlaBvDomainGenerator *gen);

/** Generate random element in the sequence. */
BzlaBitVector *bzla_bvprop_gen_random(BzlaBvDomainGenerator *gen);

/** Delete generator and release all associated memory. */
void bzla_bvprop_gen_delete(const BzlaBvDomainGenerator *gen);

/*----------------------------------------------------------------------------*/

#endif
