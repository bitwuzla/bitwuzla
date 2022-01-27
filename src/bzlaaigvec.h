/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAAIGVEC_H_INCLUDED
#define BZLAAIGVEC_H_INCLUDED

#include "bzlaaig.h"
#include "bzlabv.h"
#include "bzlaopt.h"
#include "bzlatypes.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

struct BzlaAIGVec
{
  uint32_t width;  /* width of the AIG vector (cf. bit-width) */
  BzlaAIG *aigs[]; /* vector of AIGs (MSB is at index 0) */
};

typedef struct BzlaAIGVec BzlaAIGVec;

typedef struct BzlaAIGVecMgr BzlaAIGVecMgr;

struct BzlaAIGVecMgr
{
  Bzla *bzla;
  BzlaAIGMgr *amgr;
  uint_least64_t max_num_aigvecs;
  uint_least64_t cur_num_aigvecs;
};

/*------------------------------------------------------------------------*/

BzlaAIGVecMgr *bzla_aigvec_mgr_new(Bzla *bzla);
BzlaAIGVecMgr *bzla_aigvec_mgr_clone(Bzla *bzla, BzlaAIGVecMgr *avmgr);
void bzla_aigvec_mgr_delete(BzlaAIGVecMgr *avmgr);

BzlaAIGMgr *bzla_aigvec_get_aig_mgr(const BzlaAIGVecMgr *avmgr);

/*------------------------------------------------------------------------*/

/**
 * Create an AIG vector representing the constant specified by bits.
 * width(result) = width(bits)
 */
BzlaAIGVec *bzla_aigvec_const(BzlaAIGVecMgr *avmgr, const BzlaBitVector *bits);

/**
 * Create an AIG vector representing 0 of given width.
 * width > 0
 * width(result) = width
 */
BzlaAIGVec *bzla_aigvec_zero(BzlaAIGVecMgr *avmgr, uint32_t width);

/**
 * Create an AIG vector representing a variable.
 * width > 0
 * width(result) = width
 */
BzlaAIGVec *bzla_aigvec_var(BzlaAIGVecMgr *avmgr, uint32_t width);

/** Invert all AIGs of the given AIG vector */
void bzla_aigvec_invert(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av);

/**
 * Create an AIG vector representing ones's complement of av.
 * width(result) = width(av)
 */
BzlaAIGVec *bzla_aigvec_not(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av);

/**
 * Create an AIG vector representing a slice of av.
 * upper < width(av)
 * lower >= 0
 * upper >= lower
 * width(result) = upper - lower + 1
 */
BzlaAIGVec *bzla_aigvec_slice(BzlaAIGVecMgr *avmgr,
                              BzlaAIGVec *av,
                              uint32_t upper,
                              uint32_t lower);
/**
 * Create an AIG vector representing av1 AND av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BzlaAIGVec *bzla_aigvec_and(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 less than av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = 1
 */
BzlaAIGVec *bzla_aigvec_ult(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 less than av2 (signed).
 * width(av1) = width(av2)
 * width(result) = 1
 */
BzlaAIGVec *bzla_aigvec_slt(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 equal av2.
 * width(av1) = width(av2)
 * width(result) = 1
 */
BzlaAIGVec *bzla_aigvec_eq(BzlaAIGVecMgr *avmgr,
                           BzlaAIGVec *av1,
                           BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 + av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BzlaAIGVec *bzla_aigvec_add(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 shift left logical by av2.
 * is_power_of_2(width(av1))
 * width(av2) = log2(width(av1))
 * width(result) = width(av1)
 */
BzlaAIGVec *bzla_aigvec_sll(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 shift right logical by av2.
 * is_power_of_2(width(av1))
 * width(av2) = log2(width(av1))
 * width(result) = width(av1)
 */
BzlaAIGVec *bzla_aigvec_srl(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 * av2.
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BzlaAIGVec *bzla_aigvec_mul(BzlaAIGVecMgr *avmgr,
                            BzlaAIGVec *av1,
                            BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 / av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BzlaAIGVec *bzla_aigvec_udiv(BzlaAIGVecMgr *avmgr,
                             BzlaAIGVec *av1,
                             BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av1 % av2 (unsigned).
 * width(av1) = width(av2)
 * width(result) = width(av1) = width(av2)
 */
BzlaAIGVec *bzla_aigvec_urem(BzlaAIGVecMgr *avmgr,
                             BzlaAIGVec *av1,
                             BzlaAIGVec *av2);
/**
 * Create an AIG vector representing the concatenation av1.av2.
 * width(result) = width(av1) + width(av2)
 */
BzlaAIGVec *bzla_aigvec_concat(BzlaAIGVecMgr *avmgr,
                               BzlaAIGVec *av1,
                               BzlaAIGVec *av2);
/**
 * Create an AIG vector representing av_cond ? av_if : av_else.
 * width(av_cond) = 1
 * width(av_if) = width(av_else)
 * width(result) = width(av_if) = width(av_else)
 */
BzlaAIGVec *bzla_aigvec_cond(BzlaAIGVecMgr *avmgr,
                             BzlaAIGVec *av_cond,
                             BzlaAIGVec *av_if,
                             BzlaAIGVec *av_else);
/**
 * Creates an AIG vector representing a copy of av.
 * width(result) = width(av)
 */
BzlaAIGVec *bzla_aigvec_copy(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av);

/**
 * Clone the given AIG vector.
 * All aigs referenced must already be cloned.
 */
BzlaAIGVec *bzla_aigvec_clone(BzlaAIGVec *av, BzlaAIGVecMgr *avmgr);

/*i* Translate every AIG of the given AIG vector into SAT in both phases.  */
void bzla_aigvec_to_sat_tseitin(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av);

/** Release all AIGs of the given AIG vector and delete it. */
void bzla_aigvec_release_delete(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av);
#endif
