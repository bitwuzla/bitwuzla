/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

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

/**
 * Create a floating-point constant node representing zero.
 * sign: false for +zero and true for -zero.
 */
BzlaFloatingPoint *bzla_fp_make_zero(Bzla *bzla, BzlaSortId sort, bool sign);

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
 * Delete given word-blaster.
 * Note: Memory is not managed by the memory manager of the given Bzla instance.
 */
void bzla_fp_word_blaster_delete(void *wblaster);

/** Word-blast given Boolean expression. */
BzlaNode *bzla_fp_word_blast(Bzla *bzla, BzlaNode *node);

#endif
