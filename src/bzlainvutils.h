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

/* -------------------------------------------------------------------------- */

/** Check invertibility of x + s = t or s + x = t when solved for x. */
bool bzla_is_inv_add(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_and(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x o s = t or s o x = t when solved for x. */
bool bzla_is_inv_concat(BzlaMemMgr *mm,
                        const BzlaBitVector *t,
                        const BzlaBitVector *s,
                        uint32_t pos_x);

/** Check invertibility of x & s = t or s & x = t when solved for x. */
bool bzla_is_inv_eq(BzlaMemMgr *mm,
                    const BzlaBitVector *t,
                    const BzlaBitVector *s,
                    uint32_t pos_x);

/** Check invertibility of x * s = t or s * x = t when solved for x. */
bool bzla_is_inv_mul(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x | s = t or s | x = t when solved for x. */
bool bzla_is_inv_or(BzlaMemMgr *mm,
                    const BzlaBitVector *t,
                    const BzlaBitVector *s,
                    uint32_t pos_x);

/** Check invertibility of x << s = t or s << x = t when solved for x. */
bool bzla_is_inv_sll(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x >>a s = t or s >>a x = t when solved for x. */
bool bzla_is_inv_sra(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x >> s = t or s >> x = t when solved for x. */
bool bzla_is_inv_srl(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x / s = t or s / x = t when solved for x. */
bool bzla_is_inv_udiv(BzlaMemMgr *mm,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x);

/** Check invertibility of x < s = t or s < x = t when solved for x. */
bool bzla_is_inv_ult(BzlaMemMgr *mm,
                     const BzlaBitVector *t,
                     const BzlaBitVector *s,
                     uint32_t pos_x);

/** Check invertibility of x % s = t or s % x = t when solved for x. */
bool bzla_is_inv_urem(BzlaMemMgr *mm,
                      const BzlaBitVector *t,
                      const BzlaBitVector *s,
                      uint32_t pos_x);

#endif
