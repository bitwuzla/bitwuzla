/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAINVUTILS_H_INCLUDED
#define BZLAINVUTILS_H_INCLUDED

#include "bzlabv.h"
#include "bzlabvprop.h"

typedef struct BzlaPropInfo BzlaPropInfo;

/* -------------------------------------------------------------------------- */
/* Check invertibility without considering constant bits in x.                */
/* -------------------------------------------------------------------------- */

/** Check invertibility of x + s = t or s + x = t when solved for x. */
bool bzla_is_inv_add(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_and(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x o s = t or s o x = t when solved for x. */
bool bzla_is_inv_concat(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_eq(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x * s = t or s * x = t when solved for x. */
bool bzla_is_inv_mul(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x << s = t or s << x = t when solved for x. */
bool bzla_is_inv_sll(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x >> s = t or s >> x = t when solved for x. */
bool bzla_is_inv_srl(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x >>a s = t or s >>a x = t when solved for x. */
bool bzla_is_inv_sra(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x / s = t or s / x = t when solved for x. */
bool bzla_is_inv_udiv(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of unsigned x < s = t or s < x = t when solved for x. */
bool bzla_is_inv_ult(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of signed x < s = t or s < x = t when solved for x. */
bool bzla_is_inv_slt(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x % s = t or s % x = t when solved for x. */
bool bzla_is_inv_urem(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x ? s0 : s1 = t or c ? x : s = t or c ? s : x = t
 * when solved for x.
 */
bool bzla_is_inv_cond(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x[upper:lower] = t when solved for x. */
bool bzla_is_inv_slice(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of sign_extend(x, n) = t when solved for x. */
bool bzla_is_inv_sext(Bzla *bzla, BzlaPropInfo *pi);

/** Check invertibility of x ^ s = t when solved for x. */
bool bzla_is_inv_xor(Bzla *bzla, BzlaPropInfo *pi);

/* -------------------------------------------------------------------------- */
/* Check invertibility while considering constant bits in x.                  */
/* -------------------------------------------------------------------------- */

/**
 * Check invertibility of x + s = t or s + x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_add_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_and_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x o s = t or s o x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_concat_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_eq_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x * s = t or s * x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_mul_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x << s = t or s << x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_sll_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x >> s = t or s >> x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_srl_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x >>a s = t or s >>a x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_sra_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x / s = t or s / x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_udiv_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of unsigned x < s = t or s < x = t when solved for x
 * with respect to const bits in x.
 */
bool bzla_is_inv_ult_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of signed x < s = t or s < x = t when solved for x
 * with respect to const bits in x.
 */
bool bzla_is_inv_slt_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x % s = t or s % x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_urem_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x ? s0 : s1 = t or c ? x : s = t or c ? s : x = t
 * when solved for x with respect to const bits in x.
 */
bool bzla_is_inv_cond_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x[upper:lower] = t when solved for x with respect to
 * const bits in x.
 */
bool bzla_is_inv_slice_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of sign_extend(x, n) = t when solved for x with respect
 * to const bits in x. */
bool bzla_is_inv_sext_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check invertibility of x ^ s = t when solved for x with respect to const
 * bits in x. */
bool bzla_is_inv_xor_const(Bzla *bzla, BzlaPropInfo *pi);

#endif
