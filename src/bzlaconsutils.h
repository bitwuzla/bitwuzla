/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLACONSUTILS_H_INCLUDED
#define BZLACONSUTILS_H_INCLUDED

#include "bzlabv.h"

typedef struct BzlaPropInfo BzlaPropInfo;

/**
 * Check consistency of x + s = t or s + x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_add_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_and_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x ^ s = t or s ^ x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_xor_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of (x = s) = t or (s = x) = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_eq_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of (x < s) = t or (s < x) = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_ult_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of (x <s s) = t or (s <s x) = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_slt_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x << s = t or s << x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_sll_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x >> s = t or s >> x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_srl_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x >>a s = t or s >>a x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_sra_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x * s = t or s * x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_mul_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x / s = t or s / x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_udiv_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x % s = t or s % x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_urem_const(Bzla *bzla, BzlaPropInfo *pi);

/**
 * Check consistency of x o s = t or s o x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_cons_concat_const(Bzla *bzla, BzlaPropInfo *pi);

#endif
