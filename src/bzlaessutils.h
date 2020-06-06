/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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
#endif
