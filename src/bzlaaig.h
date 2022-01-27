/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAAIG_H_INCLUDED
#define BZLAAIG_H_INCLUDED

#include <stdint.h>
#include <stdio.h>

#include "bzlaopt.h"
#include "bzlasat.h"
#include "bzlatypes.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

struct BzlaAIG
{
  int32_t id;
  int32_t cnf_id;
  uint32_t refs;
  int32_t next; /* next AIG id for unique table */
  uint8_t mark : 2;
  uint8_t is_var : 1; /* is it an AIG variable or an AND? */
  uint32_t local;
  int32_t children[]; /* only allocated for AIG AND */
};

typedef struct BzlaAIG BzlaAIG;

BZLA_DECLARE_STACK(BzlaAIGPtr, BzlaAIG *);

struct BzlaAIGUniqueTable
{
  uint32_t size;
  uint32_t num_elements;
  int32_t *chains;
};

typedef struct BzlaAIGUniqueTable BzlaAIGUniqueTable;

struct BzlaAIGMgr
{
  Bzla *bzla;
  BzlaAIGUniqueTable table;
  BzlaSATMgr *smgr;
  BzlaAIGPtrStack id2aig; /* id to AIG node */
  BzlaIntStack cnfid2aig; /* cnf id to AIG id */

  uint_least64_t cur_num_aigs;     /* current number of ANDs */
  uint_least64_t cur_num_aig_vars; /* current number of AIG variables */

  /* statistics */
  uint_least64_t max_num_aigs;
  uint_least64_t max_num_aig_vars;
  uint_least64_t num_cnf_vars;
  uint_least64_t num_cnf_clauses;
  uint_least64_t num_cnf_literals;
};

typedef struct BzlaAIGMgr BzlaAIGMgr;

/*------------------------------------------------------------------------*/

#define BZLA_AIG_FALSE ((BzlaAIG *) (uintptr_t) 0)

#define BZLA_AIG_TRUE ((BzlaAIG *) (uintptr_t) 1)

#define BZLA_INVERT_AIG(aig) ((BzlaAIG *) ((uintptr_t) 1 ^ (uintptr_t)(aig)))

#define BZLA_IS_INVERTED_AIG(aig) ((uintptr_t) 1 & (uintptr_t)(aig))

#define BZLA_REAL_ADDR_AIG(aig) \
  ((BzlaAIG *) ((~(uintptr_t) 1) & (uintptr_t)(aig)))

#define BZLA_IS_REGULAR_AIG(aig) (!((uintptr_t) 1 & (uintptr_t)(aig)))

/*------------------------------------------------------------------------*/

static inline bool
bzla_aig_is_const(const BzlaAIG *aig)
{
  return aig == BZLA_AIG_TRUE || aig == BZLA_AIG_FALSE;
}

static inline bool
bzla_aig_is_false(const BzlaAIG *aig)
{
  return aig == BZLA_AIG_FALSE;
}

static inline bool
bzla_aig_is_true(const BzlaAIG *aig)
{
  return aig == BZLA_AIG_TRUE;
}

static inline bool
bzla_aig_is_var(const BzlaAIG *aig)
{
  if (bzla_aig_is_const(aig)) return false;
  return aig->is_var;
}

static inline bool
bzla_aig_is_and(const BzlaAIG *aig)
{
  if (bzla_aig_is_const(aig)) return false;
  return !aig->is_var;
}

static inline int32_t
bzla_aig_get_id(const BzlaAIG *aig)
{
  assert(aig);
  assert(!bzla_aig_is_const(aig));
  return BZLA_IS_INVERTED_AIG(aig) ? -BZLA_REAL_ADDR_AIG(aig)->id : aig->id;
}

static inline BzlaAIG *
bzla_aig_get_by_id(BzlaAIGMgr *amgr, int32_t id)
{
  assert(amgr);

  return id < 0 ? BZLA_INVERT_AIG(BZLA_PEEK_STACK(amgr->id2aig, -id))
                : BZLA_PEEK_STACK(amgr->id2aig, id);
}

static inline int32_t
bzla_aig_get_cnf_id(const BzlaAIG *aig)
{
  if (bzla_aig_is_true(aig)) return 1;
  if (bzla_aig_is_false(aig)) return -1;
  return BZLA_IS_INVERTED_AIG(aig) ? -BZLA_REAL_ADDR_AIG(aig)->cnf_id
                                   : aig->cnf_id;
}

static inline BzlaAIG *
bzla_aig_get_left_child(BzlaAIGMgr *amgr, const BzlaAIG *aig)
{
  assert(amgr);
  assert(aig);
  assert(!bzla_aig_is_const(aig));
  return bzla_aig_get_by_id(amgr, BZLA_REAL_ADDR_AIG(aig)->children[0]);
}

static inline BzlaAIG *
bzla_aig_get_right_child(BzlaAIGMgr *amgr, const BzlaAIG *aig)
{
  assert(amgr);
  assert(aig);
  assert(!bzla_aig_is_const(aig));
  return bzla_aig_get_by_id(amgr, BZLA_REAL_ADDR_AIG(aig)->children[1]);
}

/*------------------------------------------------------------------------*/
BzlaAIGMgr *bzla_aig_mgr_new(Bzla *bzla);
BzlaAIGMgr *bzla_aig_mgr_clone(Bzla *bzla, BzlaAIGMgr *amgr);
void bzla_aig_mgr_delete(BzlaAIGMgr *amgr);

BzlaSATMgr *bzla_aig_get_sat_mgr(const BzlaAIGMgr *amgr);

/* Variable representing 1 bit. */
BzlaAIG *bzla_aig_var(BzlaAIGMgr *amgr);

/* Inverter. */
BzlaAIG *bzla_aig_not(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* Logical AND. */
BzlaAIG *bzla_aig_and(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right);

/* Logical OR. */
BzlaAIG *bzla_aig_or(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right);

/* Logical EQUIVALENCE. */
BzlaAIG *bzla_aig_eq(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right);

/* If then Else. */
BzlaAIG *bzla_aig_cond(BzlaAIGMgr *amgr,
                       BzlaAIG *aig_cond,
                       BzlaAIG *aig_if,
                       BzlaAIG *aig_else);

/* Copies AIG (increments reference counter). */
BzlaAIG *bzla_aig_copy(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* Releases AIG (decrements reference counter).
 * If reference counter reaches 0,
 * then also the children are released
 * and AIG is deleted from memory.
 */
void bzla_aig_release(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* Translates AIG into SAT instance. */
void bzla_aig_to_sat(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* As 'bzla_aig_to_sat' but also add the argument as new SAT constraint.
 * Actually this will result in less constraints being generated.
 */
void bzla_aig_add_toplevel_to_sat(BzlaAIGMgr *, BzlaAIG *);

/* Translates AIG into SAT instance in both phases.
 * The function guarantees that after finishing every reachable AIG
 * has a CNF id.
 */
void bzla_aig_to_sat_tseitin(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* Gets current assignment of AIG aig (in the SAT case).
 */
int32_t bzla_aig_get_assignment(BzlaAIGMgr *amgr, BzlaAIG *aig);

/* Orders AIGs (actually assume left child of an AND node is smaller
 * than right child
 */
int32_t bzla_aig_compare(const BzlaAIG *aig0, const BzlaAIG *aig1);

/* hash AIG by id */
uint32_t bzla_aig_hash_by_id(const BzlaAIG *aig);

/* compare AIG by id */
int32_t bzla_aig_compare_by_id(const BzlaAIG *aig0, const BzlaAIG *aig1);
int32_t bzla_compare_aig_by_id_qsort_asc(const void *aig0, const void *aig1);
#endif
