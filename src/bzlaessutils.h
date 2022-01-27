/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAESSUTILS_H_INCLUDED
#define BZLAESSUTILS_H_INCLUDED

#include "bzlabv.h"

typedef struct BzlaPropInfo BzlaPropInfo;

/* -------------------------------------------------------------------------- */

/** Check if x is essential w.r.t. to t for x + s = t or s + x = t. */
bool bzla_is_ess_add(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x & s = t or s & x = t. */
bool bzla_is_ess_and(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x ^ s = t or s ^ x = t. */
bool bzla_is_ess_xor(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x o s = t or s o x = t. */
bool bzla_is_ess_concat(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for (x = s) = t or (s = x) = t. */
bool bzla_is_ess_eq(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x * s = t or s * x = t. */
bool bzla_is_ess_mul(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x[u:l} = t. */
bool bzla_is_ess_slice(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x << s = t or s << x = t. */
bool bzla_is_ess_sll(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x >> s = t or s >> x = t. */
bool bzla_is_ess_srl(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x >>a s = t or s >>a x = t. */
bool bzla_is_ess_sra(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x / s = t or s / x = t. */
bool bzla_is_ess_udiv(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x < s = t or s < x = t. */
bool bzla_is_ess_ult(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x <s s = t or s <s x = t. */
bool bzla_is_ess_slt(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/** Check if x is essential w.r.t. to t for x % s = t or s % x = t. */
bool bzla_is_ess_urem(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t for x ? s0 : s1 = t or s0 ? x : s1 = t
 *  or s0 ? s1 : x = t.
 */
bool bzla_is_ess_cond(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/* -------------------------------------------------------------------------- */

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x + s = t
 * or s + x = t.
 */
bool bzla_is_ess_add_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x & s = t
 * or s & x = t.
 */
bool bzla_is_ess_and_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x ^ s = t
 * or s ^ x = t.
 */
bool bzla_is_ess_xor_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x o s = t
 * or s o x = t.
 */
bool bzla_is_ess_concat_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for (x = s) = t
 * or (s = x) = t.
 */
bool bzla_is_ess_eq_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x * s = t
 * or s * x = t.
 */
bool bzla_is_ess_mul_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x[u:l} = t.
 */
bool bzla_is_ess_slice_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x << s = t
 * or s << x = t.
 */
bool bzla_is_ess_sll_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x >> s = t
 * or s >> x = t.
 */
bool bzla_is_ess_srl_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x >>a s = t
 * or s >>a x = t.
 */
bool bzla_is_ess_sra_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x / s = t
 * or s / x = t.
 */
bool bzla_is_ess_udiv_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x < s = t
 * or s < x = t.
 */
bool bzla_is_ess_ult_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x <s s = t
 * or s <s x = t.
 */
bool bzla_is_ess_slt_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for x % s = t
 * or s % x = t.
 */
bool bzla_is_ess_urem_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);

/**
 * Check if x is essential w.r.t. to t and constant bits in s for
 * x ? s0 : s1 = t or s0 ? x : s1 = t or s0 ? s1 : x = t.
 */
bool bzla_is_ess_cond_const(Bzla *bzla, BzlaPropInfo *pi, uint32_t pos_x);
#endif
