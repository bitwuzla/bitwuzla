/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2019-2020 Aina Niemetz.
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
bool bzla_is_inv_add(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_and(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x o s = t or s o x = t when solved for x. */
bool bzla_is_inv_concat(Bzla *bzla,
                        const BzlaBvDomain *x,
                        const BzlaBitVector *t,
                        const BzlaBitVector *s,
                        uint32_t pos_x,
                        BzlaBvDomain **d_res_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_eq(Bzla *bzla,
                    const BzlaBvDomain *x,
                    const BzlaBitVector *t,
                    const BzlaBitVector *s,
                    uint32_t pos_x,
                    BzlaBvDomain **d_res_x);

/** Check invertibility of x * s = t or s * x = t when solved for x. */
bool bzla_is_inv_mul(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x << s = t or s << x = t when solved for x. */
bool bzla_is_inv_sll(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x >> s = t or s >> x = t when solved for x. */
bool bzla_is_inv_srl(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x / s = t or s / x = t when solved for x. */
bool bzla_is_inv_udiv(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x);

/** Check invertibility of x < s = t or s < x = t when solved for x. */
bool bzla_is_inv_ult(Bzla *bzla,
                     const BzlaBvDomain *x,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x,
                     BzlaBvDomain **d_res_x);

/** Check invertibility of x % s = t or s % x = t when solved for x. */
bool bzla_is_inv_urem(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x ? s0 : s1 = t or c ? x : s = t or c ? s : x = t
 * when solved for x.
 */
bool bzla_is_inv_cond(Bzla *bzla,
                      const BzlaBvDomain *x,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s0,
                      const BzlaBitVector *s1,
                      uint32_t pos_x,
                      BzlaBvDomain **d_res_x);

/** Check invertibility of x[upper:lower] = t when solved for x. */
bool bzla_is_inv_slice(Bzla *bzla,
                       const BzlaBvDomain *x,
                       const BzlaBitVector *t,
                       uint32_t upper,
                       uint32_t lower);

/* -------------------------------------------------------------------------- */
/* Check invertibility while considering constant bits in x.                  */
/* -------------------------------------------------------------------------- */

/**
 * Check invertibility of x + s = t or s + x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_add_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_and_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x o s = t or s o x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_concat_const(Bzla *bzla,
                              const BzlaBvDomain *x,
                              const BzlaBitVector *t,
                              const BzlaBitVector *s,
                              uint32_t pos_x,
                              BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x & s = t or s & x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_eq_const(Bzla *bzla,
                          const BzlaBvDomain *x,
                          const BzlaBitVector *t,
                          const BzlaBitVector *s,
                          uint32_t pos_x,
                          BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x * s = t or s * x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_mul_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x << s = t or s << x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_sll_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x >> s = t or s >> x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_srl_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x / s = t or s / x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_udiv_const(Bzla *bzla,
                            const BzlaBvDomain *x,
                            const BzlaBitVector *t,
                            const BzlaBitVector *s,
                            uint32_t pos_x,
                            BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x < s = t or s < x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_ult_const(Bzla *bzla,
                           const BzlaBvDomain *x,
                           const BzlaBitVector *t,
                           const BzlaBitVector *s,
                           uint32_t pos_x,
                           BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x % s = t or s % x = t when solved for x with
 * respect to const bits in x.
 */
bool bzla_is_inv_urem_const(Bzla *bzla,
                            const BzlaBvDomain *x,
                            const BzlaBitVector *t,
                            const BzlaBitVector *s,
                            uint32_t pos_x,
                            BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x ? s0 : s1 = t or c ? x : s = t or c ? s : x = t
 * when solved for x with respect to const bits in x.
 */
bool bzla_is_inv_cond_const(Bzla *bzla,
                            const BzlaBvDomain *x,
                            const BzlaBitVector *t,
                            const BzlaBitVector *s0,
                            const BzlaBitVector *s1,
                            uint32_t pos_x,
                            BzlaBvDomain **d_res_x);

/**
 * Check invertibility of x[upper:lower] = t when solved for x with respect to
 * const bits in x.
 */
bool bzla_is_inv_slice_const(Bzla *bzla,
                             const BzlaBvDomain *x,
                             const BzlaBitVector *t,
                             uint32_t upper,
                             uint32_t lower);
#endif
