/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAINVUTILS_H_INCLUDED
#define BZLAINVUTILS_H_INCLUDED

#include "bzlabv.h"
#include "bzlabvprop.h"

/* -------------------------------------------------------------------------- */
/* Check invertibility without considering constant bits in x.                */
/* -------------------------------------------------------------------------- */

/** Check invertibility of x + s = t or s + x = t when solved for x. */
bool bzla_is_inv_add(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_and(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x o s = t or s o x = t when solved for x. */
bool bzla_is_inv_concat(BzlaMemMgr *mm,
                        const BzlaBvDomain *x,
                        const BzlaBitVector *t,
                        const BzlaBitVector *s,
                        uint32_t pos_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_eq(BzlaMemMgr *mm,
                    const BzlaBvDomain *x,
                    const BzlaBitVector *t,
                    const BzlaBitVector *s,
                    uint32_t pos_x);

/** Check invertibility of x * s = t or s * x = t when solved for x. */
bool bzla_is_inv_mul(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x << s = t or s << x = t when solved for x. */
bool bzla_is_inv_sll(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x >>a s = t or s >>a x = t when solved for x. */
bool bzla_is_inv_sra(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x >> s = t or s >> x = t when solved for x. */
bool bzla_is_inv_srl(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x / s = t or s / x = t when solved for x. */
bool bzla_is_inv_udiv(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x);

/** Check invertibility of x < s = t or s < x = t when solved for x. */
bool bzla_is_inv_ult(BzlaMemMgr *mm,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x % s = t or s % x = t when solved for x. */
bool bzla_is_inv_urem(BzlaMemMgr *mm,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x);

/** Check invertibility of x[:] = t when solved for x. */
bool bzla_is_inv_slice(BzlaMemMgr *mm,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       const BzlaBitVector *s,
                       uint32_t pos_x);

/* -------------------------------------------------------------------------- */
/* Check invertibility while considering constant bits in x.                  */
/* -------------------------------------------------------------------------- */

/**
 * Check invertibility of x + s = t or s + x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_add_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_and_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x o s = t or s o x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_concat_const(BzlaMemMgr *mm,
                              const BzlaBvDomain *x,
                              const BzlaBitVector *t,
                              const BzlaBitVector *s,
                              uint32_t pos_x);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_eq_const(BzlaMemMgr *mm,
                          const BzlaBvDomain *x,
                          const BzlaBitVector *t,
                          const BzlaBitVector *s,
                          uint32_t pos_x);

/**
 * Check invertibility of x * s = t or s * x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_mul_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x << s = t or s << x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_sll_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x >>a s = t or s >>a x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_sra_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x >> s = t or s >> x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_srl_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x / s = t or s / x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_udiv_const(BzlaMemMgr *mm,
                            const BzlaBvDomain *x,
                            const BzlaBitVector *t,
                            const BzlaBitVector *s,
                            uint32_t pos_x);

/**
 * Check invertibility of x < s = t or s < x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_ult_const(BzlaMemMgr *mm,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x);

/**
 * Check invertibility of x % s = t or s % x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_urem_const(BzlaMemMgr *mm,
                            const BzlaBvDomain *x,
                            const BzlaBitVector *t,
                            const BzlaBitVector *s,
                            uint32_t pos_x);

/**
 * Check invertibility of x[:] = t when solved for x with respect to const
 * bits in x.
 */
bool bzla_is_inv_slice_const(BzlaMemMgr *mm,
                             const BzlaBvDomain *x,
                             const BzlaBitVector *t,
                             const BzlaBitVector *s,
                             uint32_t pos_x);
#endif
