/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAINVUTILS_H_INCLUDED
#define BZLAINVUTILS_H_INCLUDED

#include "bzlabv.h"

/*------------------------------------------------------------------------*/

bool bzla_is_inv_and(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t);

bool bzla_is_inv_concat(BzlaMemMgr *mm,
                        const BzlaBitVector *s,
                        const BzlaBitVector *t,
                        uint32_t pos_x);

bool bzla_is_inv_mul(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t);

bool bzla_is_inv_or(BzlaMemMgr *mm,
                    const BzlaBitVector *s,
                    const BzlaBitVector *t);

bool bzla_is_inv_sll(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t,
                     uint32_t pos_x);

bool bzla_is_inv_sra(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t,
                     uint32_t pos_x);

bool bzla_is_inv_srl(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t,
                     uint32_t pos_x);

bool bzla_is_inv_udiv(BzlaMemMgr *mm,
                      const BzlaBitVector *s,
                      const BzlaBitVector *t,
                      uint32_t pos_x);

bool bzla_is_inv_ult(BzlaMemMgr *mm,
                     const BzlaBitVector *s,
                     const BzlaBitVector *t,
                     uint32_t pos_x);

bool bzla_is_inv_urem(BzlaMemMgr *mm,
                      const BzlaBitVector *s,
                      const BzlaBitVector *t,
                      uint32_t pos_x);

#endif
