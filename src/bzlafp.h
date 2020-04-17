/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlabv.h"
#include "bzlasort.h"
#include "bzlatypes.h"
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

/**
 * Get the triple of bit-vectors representing a given floating-point.
 * sign: The output argument for the bit-vector representation of the sign bit.
 * exp : The output argument for the bit-vector representation of the exponent.
 * sig : The output argument for the bit-vector representation of the
 *       significand.
 */
void bzla_fp_as_bv(Bzla *bzla,
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

/**
 * Create a floating-point constant node representing zero.
 * sign: false for +zero and true for -zero.
 */
BzlaFloatingPoint *bzla_fp_zero(Bzla *bzla, BzlaSortId sort, bool sign);

/**
 * Create a floating-point constant node representing infinity.
 * sign: false for +inf and true for -inf.
 */
BzlaFloatingPoint *bzla_fp_inf(Bzla *bzla, BzlaSortId sort, bool sign);

/**
 * Create a floating-point constant node representing nan.
 */
BzlaFloatingPoint *bzla_fp_nan(Bzla *bzla, BzlaSortId sort);

/**
 * Create a floating-point constant node from a given bit-vector constant.
 */
BzlaFloatingPoint *bzla_fp_from_bv(Bzla *bzla,
                                   BzlaSortId sort,
                                   BzlaBitVector *bv_const);

/**
 * Create a floating-point constant node representing the absolute value
 * of the given floating-point constant.
 */
BzlaFloatingPoint *bzla_fp_abs(Bzla *bzla, const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant node representing the negation of the
 * given floating-point constant.
 */
BzlaFloatingPoint *bzla_fp_neg(Bzla *bzla, const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant node representing the square root of the
 * given floating-point constant w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_sqrt(Bzla *bzla,
                                const BzlaRoundingMode rm,
                                const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant node representing the round to integral of
 * the given floating-point constant w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_rti(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp);

/**
 * Create a floating-point constant node representing the remainder operation
 * of the given floating-point constants.
 */
BzlaFloatingPoint *bzla_fp_rem(Bzla *bzla,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant node representing the addition of the
 * given floating-point constants w.r.t. given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_add(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant node representing the multiplication of the
 * given floating-point constants w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_mul(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

/**
 * Create a floating-point constant node representing the division of the
 * given floating-point constants w.r.t. to the given rounding mode.
 */
BzlaFloatingPoint *bzla_fp_div(Bzla *bzla,
                               const BzlaRoundingMode rm,
                               const BzlaFloatingPoint *fp0,
                               const BzlaFloatingPoint *fp1);

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

/** Word-blast given Boolean expression. */
BzlaNode *bzla_fp_word_blast(Bzla *bzla, BzlaNode *node);

#endif
