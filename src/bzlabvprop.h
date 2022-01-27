/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLABVPROP_H_INCLUDED
#define BZLABVPROP_H_INCLUDED

#include "bzlabv.h"
#include "bzlabvdomain.h"

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
bool bzla_bvprop_cond(BzlaMemMgr *mm,
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

#endif
