/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlabv.h"
#include "bzlarm.h"
#include "bzlasort.h"
#include "utils/bzlanodemap.h"

#ifndef BZLAFP_H_INCLUDED
#define BZLAFP_H_INCLUDED

/* -------------------------------------------------------------------------- */
/* Floating-Point literals.                                                   */
/* -------------------------------------------------------------------------- */

/**
 * Wraps a FloatingPointSize object (required by SymFPU) and a SymFPU
 * UnpackedFloat object (the underlying floating-point representation).
 */
typedef struct BzlaFloatingPoint BzlaFloatingPoint;
typedef struct BzlaNodePtrStack BzlaNodePtrStack;

/**
 * Create a new floating-point wrapper object.
 *
 * This does not yet initialize the underlying SymFPU UnpackedFloat
 * representation -- must be set after creation with bzla_fp_set_fp.
 *
 * Note: Memory for the returned BzlaFloatingPoint object itself is managed
 *       by the memory manager of the given Bzla instance. Memory for the
 *       underlying FloatingPointSize and UnpackedFloat is not managed by the
 *       memory manager, but (de)allocated with free and delete.
 */
BzlaFloatingPoint *bzla_fp_new(Bzla *bzla, BzlaSortId sort);

/** Free the memory of the given BzlaFloatingPoint and it's wrapped objects.  */
void bzla_fp_free(Bzla *bzla, BzlaFloatingPoint *fp);

/** Copy the given BzlaFloatingPoint objects and its wrapped objects. */
BzlaFloatingPoint *bzla_fp_copy(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Return the exponent width of a given floating-point. */
uint32_t bzla_fp_get_exp_width(const BzlaFloatingPoint *fp);

/** Return the significand width of a given floating-point. */
uint32_t bzla_fp_get_sig_width(const BzlaFloatingPoint *fp);

/**
 * Return the bit-width of the bit-vector representation of the given
 * floating-point.
 */
uint32_t bzla_fp_get_bv_width(const BzlaFloatingPoint *fp);

/** Get the bit-vector representing a given floating-point.  */
BzlaBitVector *bzla_fp_as_bv(Bzla *bzla, BzlaFloatingPoint *fp);

void bzla_fp_ieee_bv_as_bvs(Bzla *bzla,
                            const BzlaBitVector *bv,
                            BzlaSortId fp_sort,
                            BzlaBitVector **sign,
                            BzlaBitVector **exp,
                            BzlaBitVector **sig);

/**
 * Get the triple of bit-vectors representing a given floating-point.
 * sign: The output argument for the bit-vector representation of the sign bit.
 * exp : The output argument for the bit-vector representation of the exponent.
 * sig : The output argument for the bit-vector representation of the
 *       significand.
 */
void bzla_fp_as_bvs(Bzla *bzla,
                    BzlaFloatingPoint *fp,
                    BzlaBitVector **sign,
                    BzlaBitVector **exp,
                    BzlaBitVector **sig);

/** Get the floating-point of a floating-point constant node. */
BzlaFloatingPoint *bzla_fp_get_fp(BzlaNode *node);

/** Get the size of a floating-point node (for debugging cloning). */
size_t bzla_fp_get_bytes(BzlaNode *node);

/** Compute the hash of the given floating-point. */
uint32_t bzla_fp_hash(const BzlaFloatingPoint *fp);

/**
 * Compare two floating-point values.
 * Returns 0 if they are equal, and -1 if they are disequal.
 */
int32_t bzla_fp_compare(const BzlaFloatingPoint *a, const BzlaFloatingPoint *b);

/* -------------------------------------------------------------------------- */

/** Returns true if given floating-point represents a zero value. */
bool bzla_fp_is_zero(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a normal value. */
bool bzla_fp_is_normal(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a subnormal value. */
bool bzla_fp_is_subnormal(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a nan value. */
bool bzla_fp_is_nan(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a infinite value. */
bool bzla_fp_is_inf(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a negative value. */
bool bzla_fp_is_neg(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if given floating-point represents a positive value. */
bool bzla_fp_is_pos(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Returns true if floating-point constant fp0 is equal to fp1. */
bool bzla_fp_eq(Bzla *bzla,
                const BzlaFloatingPoint *fp0,
                const BzlaFloatingPoint *fp1);

/** Returns true if floating-point constant fp0 is less than fp1. */
bool bzla_fp_lt(Bzla *bzla,
                const BzlaFloatingPoint *fp0,
                const BzlaFloatingPoint *fp1);

/** Returns true if floating-point constant fp0 is less than or equal fp1. */
bool bzla_fp_lte(Bzla *bzla,
                 const BzlaFloatingPoint *fp0,
                 const BzlaFloatingPoint *fp1);
/**
 * Create a floating-point constant representing zero.
 * sign: false for +zero and true for -zero.
 */
BzlaFloatingPoint *bzla_fp_zero(Bzla *bzla, BzlaSortId sort, bool sign);

/**
 * Create a floating-point constant representing infinity.
 * sign: false for +inf and true for -inf.
 */
BzlaFloatingPoint *bzla_fp_inf(Bzla *bzla, BzlaSortId sort, bool sign);

/**
 * Create a floating-point constant representing nan.
 */
BzlaFloatingPoint *bzla_fp_nan(Bzla *bzla, BzlaSortId sort);

/**
 * Create a floating-point constant from its bit-vector representation given as
 * sign bit, exponent bits, and significand bits.
 */
BzlaFloatingPoint *bzla_fp_fp(Bzla *bzla,
                              BzlaBitVector *bv_sign,
                              BzlaBitVector *bv_exp,
                              BzlaBitVector *bv_sig);

/**
 * Create a floating-point constant from its unpacked bit-vector representation
 * given as sign bit, exponent bits, and significand bits.
 *
 * This unpacked representation accounts for additional bits required for the
 * exponent to allow subnormals to be normalized.
 *
 * This should NOT be used to create a literal from its IEEE bit-vector
 * representation -- for this, the above constructor is to be used.
 */
BzlaFloatingPoint *bzla_fp_fp_from_unpacked(Bzla *bzla,
                                            BzlaBitVector *bv_sign,
                                            BzlaBitVector *bv_exp,
                                            BzlaBitVector *bv_sig);

/**
 * Create a floating-point constant from a given bit-vector constant.
 */
BzlaFloatingPoint *bzla_fp_from_bv(Bzla *bzla,
                                   BzlaSortId sort,
                                   const BzlaBitVector *bv_const);

/**
 * Create a floating-point constant representing the absolute value
 * of the given floating-point constant.
 */
BzlaFloatingPoint *bzla_fp_abs(Bzla *bzla, const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant representing the negation of the
 * given floating-point constant.
 */
BzlaFloatingPoint *bzla_fp_neg(Bzla *bzla, const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant representing the square root of the
 * given floating-point constant w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_sqrt(Bzla *bzla,
                                const BzlaRoundingMode rm,
                                const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant representing the round to integral of
 * the given floating-point constant w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_rti(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant representing the remainder operation
 * of the given floating-point constants.
 */
BzlaFloatingPoint *bzla_fp_rem(Bzla *bzla,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant representing the addition of the
 * given floating-point constants w.r.t. given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_add(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant representing the multiplication of the
 * given floating-point constants w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_mul(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant representing the division of the
 * given floating-point constants w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_div(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant representing the fused multiplication
 * and addition operation of the given floating-point constants w.r.t. to the
 * given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_fma(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1,
                               const BzlaFloatingPoint *fp2);

/**
 * Create a floating-point constant of given sort converted from the given
 * floating-point constant w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_convert(Bzla *bzla,
                                   BzlaSortId sort,
                                   const BzlaRoundingMode rm,
                                   const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant of given sort converted from the given
 * bit-vector constant (interpreted as signed) w.r.t. to the given rounding
 * mode.
 */
BzlaFloatingPoint *bzla_fp_convert_from_sbv(Bzla *bzla,
                                            BzlaSortId sort,
                                            const BzlaRoundingMode rm,
                                            const BzlaBitVector *bv);

/**
 * Create a floating-point constant of given sort converted from the given
 * bit-vector constant (interpreted as unsigned) w.r.t. to the given rounding
 * mode.
 */
BzlaFloatingPoint *bzla_fp_convert_from_ubv(Bzla *bzla,
                                            BzlaSortId sort,
                                            const BzlaRoundingMode rm,
                                            const BzlaBitVector *bv);

/**
 * Create a floating-point constant of given sort converted from the given real
 * constant represented as a decimal string w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_convert_from_real(Bzla *bzla,
                                             BzlaSortId sort,
                                             const BzlaRoundingMode rm,
                                             const char *real);
/**
 * Create a floating-point constant of given sort converted from the given
 * rational constant represented as a numerator and denominator decimal
 * string w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_convert_from_rational(Bzla *bzla,
                                                 BzlaSortId sort,
                                                 const BzlaRoundingMode rm,
                                                 const char *num,
                                                 const char *den);

/* -------------------------------------------------------------------------- */
/* Word-Blaster.                                                              */
/* -------------------------------------------------------------------------- */

/**
 * Create word-blaster.
 * Note: Memory is not managed by the memory manager of the given Bzla instance.
 */
void *bzla_fp_word_blaster_new(Bzla *bzla);

/**
 * Clone given word-blaster.
 * Note: Memory is not managed by the memory manager of the given Bzla instance.
 */
void *bzla_fp_word_blaster_clone(Bzla *bzla, Bzla *clone, BzlaNodeMap *exp_map);

/**
 * Delete word-blaster of given Bzla instance.
 * Note: Memory is not managed by the memory manager of the given Bzla instance.
 */
void bzla_fp_word_blaster_delete(Bzla *bzla);

/** Assert additional constraints added during word-blasting. */
void bzla_fp_word_blaster_add_additional_assertions(Bzla *bzla);

/** Word-blast given floating-point/rounding mode expression. */
BzlaNode *bzla_fp_word_blast(Bzla *bzla, BzlaNode *node);

/** Return all uninterpreted functions introduced while word-blasting. */
void bzla_fp_word_blaster_get_introduced_ufs(Bzla *bzla, BzlaNodePtrStack *ufs);
#endif
