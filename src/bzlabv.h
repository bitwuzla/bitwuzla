/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLABV_H_INCLUDED
#define BZLABV_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "bzlatypes.h"
#include "utils/bzlamem.h"
#include "utils/bzlarng.h"
#include "utils/bzlastack.h"

typedef struct BzlaBitVector BzlaBitVector;

BZLA_DECLARE_STACK(BzlaBitVectorPtr, BzlaBitVector *);

/** Create a new bit-vector of given bit-width, initialized to zero. */
BzlaBitVector *bzla_bv_new(BzlaMemMgr *mm, uint32_t bw);

/** Create a new random bit-vector of given bit-width. */
BzlaBitVector *bzla_bv_new_random(BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw);

/** Create a new random bit-vector within the given (unsigned) value range. */
BzlaBitVector *bzla_bv_new_random_range(BzlaMemMgr *mm,
                                        BzlaRNG *rng,
                                        uint32_t bw,
                                        const BzlaBitVector *from,
                                        const BzlaBitVector *to);

/** Create a new random bit-vector within the given (signed) value range. */
BzlaBitVector *bzla_bv_new_random_signed_range(BzlaMemMgr *mm,
                                               BzlaRNG *rng,
                                               uint32_t bw,
                                               const BzlaBitVector *from,
                                               const BzlaBitVector *to);

/**
 * Create a new bit-vector of given bit-width and randomly set bits within given
 * index range. Bits outside of given index range are initialized with zero.
 */
BzlaBitVector *bzla_bv_new_random_bit_range(
    BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw, uint32_t up, uint32_t lo);

/**
 * Create bit-vector from given binary string.
 * The bit-width of the resulting bit-vector is the length of the given string.
 */
BzlaBitVector *bzla_bv_char_to_bv(BzlaMemMgr *mm, const char *assignment);

/** Create bit-vector of given bit-width from given unsigned integer value. */
BzlaBitVector *bzla_bv_uint64_to_bv(BzlaMemMgr *mm,
                                    uint64_t value,
                                    uint32_t bw);

/** Create bit-vector of given bit-width from given integer value. */
BzlaBitVector *bzla_bv_int64_to_bv(BzlaMemMgr *mm, int64_t value, uint32_t bw);

/**
 * Create bit-vector from given binary string.
 * The bit-width of the resulting bit-vector is the length of the given string.
 */
BzlaBitVector *bzla_bv_const(BzlaMemMgr *mm, const char *str, uint32_t bw);

/** Create bit-vector of given bit-width from given decimal string. */
BzlaBitVector *bzla_bv_constd(BzlaMemMgr *mm, const char *str, uint32_t bw);

/** Create bit-vector of given bit-width from given hexadecimal string. */
BzlaBitVector *bzla_bv_consth(BzlaMemMgr *mm, const char *str, uint32_t bw);

/** Create a (deep) copy of the given bit-vector. */
BzlaBitVector *bzla_bv_copy(BzlaMemMgr *mm, const BzlaBitVector *bv);

/*------------------------------------------------------------------------*/

/** Return the size in bytes of the given bit-vector. */
size_t bzla_bv_size(const BzlaBitVector *bv);

/** Free memory allocated for the given bit-vector. */
void bzla_bv_free(BzlaMemMgr *mm, BzlaBitVector *bv);

/**
 * Compare bit-vectors 'a' and 'b' (unsigned).
 * Return 0 if 'a' and 'b' are equal, 1 if a > b, and -1 if a < b.
 */
int32_t bzla_bv_compare(const BzlaBitVector *a, const BzlaBitVector *b);

/**
 * Compare bit-vectors 'a' and 'b' (signed).
 * Return 0 if 'a' and 'b' are equal, 1 if a >s b, and -1 if a <s b.
 */
int32_t bzla_bv_signed_compare(const BzlaBitVector *a, const BzlaBitVector *b);

/** Return a hash value for the given bit-vector. */
uint32_t bzla_bv_hash(const BzlaBitVector *bv);

/** Print given bit-vector to stdout, terminated with a new line. */
void bzla_bv_print(const BzlaBitVector *bv);
/** Print given bit-vector to stdout, without terminating new line. */
void bzla_bv_print_without_new_line(const BzlaBitVector *bv);

/**
 * Convert given bit-vector to a binary string.
 * Note: Result string must be freed with bzla_mem_freestr().
 */
char *bzla_bv_to_char(BzlaMemMgr *mm, const BzlaBitVector *bv);
/**
 * Convert given bit-vector to a hexadecimal string.
 * Note: Result string must be freed with bzla_mem_freestr().
 */
char *bzla_bv_to_hex_char(BzlaMemMgr *mm, const BzlaBitVector *bv);
/**
 * Convert given bit-vector to a decimal string.
 * Note: Result string must be freed with bzla_mem_freestr().
 */
char *bzla_bv_to_dec_char(BzlaMemMgr *mm, const BzlaBitVector *bv);

/** Convert given bit-vector to an unsigned 64 bit integer. */
uint64_t bzla_bv_to_uint64(const BzlaBitVector *bv);

/*------------------------------------------------------------------------*/

/** Get the bit-width of given bit-vector. */
uint32_t bzla_bv_get_width(const BzlaBitVector *bv);

/**
 * Get the length of the bits array of the given bit-vector.
 * This function returns 0 if compiled with GMP.
 */
uint32_t bzla_bv_get_len(const BzlaBitVector *bv);

/** Get value of bit at given index (index 0 is LSB, width - 1 is MSB). */
uint32_t bzla_bv_get_bit(const BzlaBitVector *bv, uint32_t pos);
/** Get value of bit at given index (index 0 is LSB, width - 1 is MSB). */
void bzla_bv_set_bit(BzlaBitVector *bv, uint32_t pos, uint32_t value);

/** Flip bit at given index. */
void bzla_bv_flip_bit(BzlaBitVector *bv, uint32_t pos);

/** Return true if given bit-vector represents true ('1'). */
bool bzla_bv_is_true(const BzlaBitVector *bv);
/** Return true if given bit-vector represents false ('0'). */
bool bzla_bv_is_false(const BzlaBitVector *bv);

/** Return true if given bit-vector represents 0 (all bits set to 0). */
bool bzla_bv_is_zero(const BzlaBitVector *bv);
/** Return true if given bit-vector represents ~0 (all bits set to 1). */
bool bzla_bv_is_ones(const BzlaBitVector *bv);
/** Return true if given bit-vector represents 1. */
bool bzla_bv_is_one(const BzlaBitVector *bv);
/** Return true if given bit-vector represents the min. signed value (10...0).
 */
bool bzla_bv_is_min_signed(const BzlaBitVector *bv);
/** Return true if given bit-vector represents the max. signed value (01...1).
 */
bool bzla_bv_is_max_signed(const BzlaBitVector *bv);

/** Return p for bv = 2^p, and -1 if bv is not a power of 2 */
int64_t bzla_bv_power_of_two(const BzlaBitVector *bv);
/**
 * Return 'bv' as integer if its value can be converted into a positive
 * integer of bw 32, and -1 otherwise
 */
int32_t bzla_bv_small_positive_int(const BzlaBitVector *bv);

/** Return the of count trailing zeros (starting from LSB). */
uint32_t bzla_bv_get_num_trailing_zeros(const BzlaBitVector *bv);
/** Return the of count leading zeros (starting from MSB). */
uint32_t bzla_bv_get_num_leading_zeros(const BzlaBitVector *bv);
/** Return the of count leading ones (starting from MSB). */
uint32_t bzla_bv_get_num_leading_ones(const BzlaBitVector *bv);

/*------------------------------------------------------------------------*/

#define bzla_bv_zero(MM, BW) bzla_bv_new(MM, BW)

/** Create a bit-vector of given bit-width that represents 1. */
BzlaBitVector *bzla_bv_one(BzlaMemMgr *mm, uint32_t bw);
/** Create a bit-vector of given bit-width that represents ~0. */
BzlaBitVector *bzla_bv_ones(BzlaMemMgr *mm, uint32_t bw);

/**
 * Create a bit-vector of given bit-width that represents the minimum signed
 * value 10...0.
 */
BzlaBitVector *bzla_bv_min_signed(BzlaMemMgr *mm, uint32_t bw);
/**
 * Create a bit-vector of given bit-width that represents the maximum signed
 * value 01...1.
 */
BzlaBitVector *bzla_bv_max_signed(BzlaMemMgr *mm, uint32_t bw);

/** Create the negation (two's complement0 of the given bit-vector. */
BzlaBitVector *bzla_bv_neg(BzlaMemMgr *mm, const BzlaBitVector *bv);
/** Create the bit-wise negation of the given bit-vector. */
BzlaBitVector *bzla_bv_not(BzlaMemMgr *mm, const BzlaBitVector *bv);
/** Create the increment (+1) of the given bit-vector. */
BzlaBitVector *bzla_bv_inc(BzlaMemMgr *mm, const BzlaBitVector *bv);
/** Create the decrement (-1) of the given bit-vector. */
BzlaBitVector *bzla_bv_dec(BzlaMemMgr *mm, const BzlaBitVector *bv);

/** Create a bit-vector representing the redor of given bit-vector. */
BzlaBitVector *bzla_bv_redor(BzlaMemMgr *mm, const BzlaBitVector *bv);
/** Create a bit-vector representing the redand of given bit-vector. */
BzlaBitVector *bzla_bv_redand(BzlaMemMgr *mm, const BzlaBitVector *bv);

/** Create the addition of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_add(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the subtraction of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_sub(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the bit-wise and of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_and(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the boolean implication of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_implies(BzlaMemMgr *mm,
                               const BzlaBitVector *a,
                               const BzlaBitVector *b);

/** Create the bit-wise nand of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_nand(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the bit-wise nor of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_nor(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the bit-wise or of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_or(BzlaMemMgr *mm,
                          const BzlaBitVector *a,
                          const BzlaBitVector *b);

/** Create the bit-wise xnor of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_xnor(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the bit-wise xor of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_xor(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the equality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_eq(BzlaMemMgr *mm,
                          const BzlaBitVector *a,
                          const BzlaBitVector *b);

/** Create the disequality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_ne(BzlaMemMgr *mm,
                          const BzlaBitVector *a,
                          const BzlaBitVector *b);

/** Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_ult(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/**
 * Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BzlaBitVector *bzla_bv_ulte(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_ugt(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/**
 * Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BzlaBitVector *bzla_bv_ugte(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_slt(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/**
 * Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BzlaBitVector *bzla_bv_slte(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the signed less than inequality of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_sgt(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/**
 * Create the signed less than or equal inequality of bit-vectors 'a' and 'b'.
 */
BzlaBitVector *bzla_bv_sgte(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the logical shift left of bit-vectors 'a' by 'shift'. */
BzlaBitVector *bzla_bv_sll_uint64(BzlaMemMgr *mm,
                                  const BzlaBitVector *a,
                                  uint64_t shift);

/** Create the logical shift left of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_sll(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the logical shift right of bit-vectors 'a' by 'shift'. */
BzlaBitVector *bzla_bv_srl_uint64(BzlaMemMgr *mm,
                                  const BzlaBitVector *a,
                                  uint64_t shift);

/** Create the logical shift right of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_srl(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the arithmetic shift right of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_sra(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the multiplication of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_mul(BzlaMemMgr *mm,
                           const BzlaBitVector *a,
                           const BzlaBitVector *b);

/** Create the unsigned division of of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_udiv(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the unsigned remainder of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_urem(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the signed division of of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_sdiv(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the signed remainder of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_srem(BzlaMemMgr *mm,
                            const BzlaBitVector *a,
                            const BzlaBitVector *b);

/** Create the if-then-else conditional c ? a : b. */
BzlaBitVector *bzla_bv_ite(BzlaMemMgr *mm,
                           const BzlaBitVector *c,
                           const BzlaBitVector *t,
                           const BzlaBitVector *e);

/** Create the concatenation of bit-vectors 'a' and 'b'. */
BzlaBitVector *bzla_bv_concat(BzlaMemMgr *mm,
                              const BzlaBitVector *a,
                              const BzlaBitVector *b);

/** Create the slice from bit index upper to lower of given the bit-vector. */
BzlaBitVector *bzla_bv_slice(BzlaMemMgr *mm,
                             const BzlaBitVector *bv,
                             uint32_t upper,
                             uint32_t lower);

/** Create the unsigned/zero extension by 'len' bits of the given bit-vector. */
BzlaBitVector *bzla_bv_uext(BzlaMemMgr *mm,
                            const BzlaBitVector *bv0,
                            uint32_t len);

/** Create the signed extension by 'len' bits of the given bit-vector. */
BzlaBitVector *bzla_bv_sext(BzlaMemMgr *mm,
                            const BzlaBitVector *bv0,
                            uint32_t len);

/*------------------------------------------------------------------------*/

/**
 * Create the unsigned division and remainder of bit-vectors 'a' and 'b'.
 * The result of the division is stored in 'q', and the result of the remainder
 * operation is stored in 'r'.
 */
void bzla_bv_udiv_urem(BzlaMemMgr *mm,
                       const BzlaBitVector *a,
                       const BzlaBitVector *b,
                       BzlaBitVector **q,
                       BzlaBitVector **r);

/*------------------------------------------------------------------------*/

/** Create a copy of given bit-vector with the bit at given index flipped. */
BzlaBitVector *bzla_bv_flipped_bit(BzlaMemMgr *mm,
                                   const BzlaBitVector *bv,
                                   uint32_t pos);

/**
 * Create a copy of given bit-vector with the bits at given index range
 * (from upper index 'up' to lower index 'lo') flipped.
 */
BzlaBitVector *bzla_bv_flipped_bit_range(BzlaMemMgr *mm,
                                         const BzlaBitVector *bv,
                                         uint32_t up,
                                         uint32_t lo);

/*------------------------------------------------------------------------*/

/** Return true if the unsigned addition 'bv0 + bv1' produces an overflow. */
bool bzla_bv_is_uaddo(BzlaMemMgr *mm,
                      const BzlaBitVector *a,
                      const BzlaBitVector *b);

/** Return true if unsigned multiplication 'bv0 * bv1' produces an overflow. */
bool bzla_bv_is_umulo(BzlaMemMgr *mm,
                      const BzlaBitVector *bv0,
                      const BzlaBitVector *bv1);

/*------------------------------------------------------------------------*/

#if 0
BzlaBitVector * bzla_bv_gcd_ext (Bzla * bzla,
				 const BzlaBitVector * bv1,
				 const BzlaBitVector * bv2,
				 BzlaBitVector ** fx,
				 BzlaBitVector ** fy);
#endif

/**
 * Calculate modular inverse for given bit-vector by means of the Extended
 * Euclidian Algorithm.
 *
 * Note that c must be odd (the greatest common divisor gcd (c, 2^bw) must be
 * and is in this case always 1).
 */
BzlaBitVector *bzla_bv_mod_inverse(BzlaMemMgr *mm, const BzlaBitVector *bv);

/*------------------------------------------------------------------------*/

enum BzlaSpecialConstBitVector
{
  BZLA_SPECIAL_CONST_BV_ZERO,
  BZLA_SPECIAL_CONST_BV_ONE,
  BZLA_SPECIAL_CONST_BV_ONES,
  BZLA_SPECIAL_CONST_BV_ONE_ONES,
  BZLA_SPECIAL_CONST_BV_MIN_SIGNED,
  BZLA_SPECIAL_CONST_BV_MAX_SIGNED,
  BZLA_SPECIAL_CONST_BV_NONE
};

typedef enum BzlaSpecialConstBitVector BzlaSpecialConstBitVector;

BzlaSpecialConstBitVector bzla_bv_is_special_const(const BzlaBitVector *bv);

/*------------------------------------------------------------------------*/

struct BzlaBitVectorTuple
{
  uint32_t arity;
  BzlaBitVector **bv;
};

typedef struct BzlaBitVectorTuple BzlaBitVectorTuple;

BzlaBitVectorTuple *bzla_bv_new_tuple(BzlaMemMgr *mm, uint32_t arity);
void bzla_bv_free_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t);

BzlaBitVectorTuple *bzla_bv_copy_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t);

size_t bzla_bv_size_tuple(BzlaBitVectorTuple *t);

void bzla_bv_add_to_tuple(BzlaMemMgr *mm,
                          BzlaBitVectorTuple *t,
                          const BzlaBitVector *bv,
                          uint32_t pos);

int32_t bzla_bv_compare_tuple(const BzlaBitVectorTuple *t0,
                              const BzlaBitVectorTuple *t1);

uint32_t bzla_bv_hash_tuple(const BzlaBitVectorTuple *t);

/*------------------------------------------------------------------------*/

#endif
