/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaaig.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include "bzlacore.h"
#include "bzlasat.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_INIT_AIG_UNIQUE_TABLE(mm, table) \
  do                                          \
  {                                           \
    assert(mm);                               \
    (table).size         = 1;                 \
    (table).num_elements = 0;                 \
    BZLA_CNEW(mm, (table).chains);            \
  } while (0)

#define BZLA_RELEASE_AIG_UNIQUE_TABLE(mm, table)    \
  do                                                \
  {                                                 \
    assert(mm);                                     \
    BZLA_DELETEN(mm, (table).chains, (table).size); \
  } while (0)

#define BZLA_AIG_UNIQUE_TABLE_LIMIT 30

#define BZLA_AIG_UNIQUE_TABLE_PRIME 2000000137u

#define BZLA_FIND_AND_AIG_CONTRADICTION_LIMIT 8

/*------------------------------------------------------------------------*/

//#define BZLA_EXTRACT_TOP_LEVEL_MULTI_OR

//#define BZLA_AIG_TO_CNF_TOP_ELIM

#define BZLA_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED

#define BZLA_AIG_TO_CNF_EXTRACT_ITE

#define BZLA_AIG_TO_CNF_EXTRACT_XOR

// #define BZLA_AIG_TO_CNF_NARY_AND

/*------------------------------------------------------------------------*/

static void
setup_aig_and_add_to_id_table(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  int32_t id;

  id = BZLA_COUNT_STACK(amgr->id2aig);
  BZLA_ABORT(id == INT32_MAX, "AIG id overflow");
  aig->refs = 1;
  aig->id   = id;
  BZLA_PUSH_STACK(amgr->id2aig, aig);
  assert(aig->id >= 0);
  assert(BZLA_COUNT_STACK(amgr->id2aig) == (size_t) aig->id + 1);
  assert(BZLA_PEEK_STACK(amgr->id2aig, aig->id) == aig);
}

static BzlaAIG *
new_and_aig(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  assert(amgr);
  assert(!bzla_aig_is_const(left));
  assert(!bzla_aig_is_const(right));

  BzlaAIG *aig;
  size_t size;

  size = sizeof(BzlaAIG) + 2 * sizeof(int32_t);
  aig  = bzla_mem_malloc(amgr->bzla->mm, size);
  memset(aig, 0, size);
  setup_aig_and_add_to_id_table(amgr, aig);
  aig->children[0] = bzla_aig_get_id(left);
  aig->children[1] = bzla_aig_get_id(right);
  amgr->cur_num_aigs++;
  if (amgr->max_num_aigs < amgr->cur_num_aigs)
    amgr->max_num_aigs = amgr->cur_num_aigs;
  return aig;
}

static void
release_cnf_id_aig_mgr(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(!BZLA_IS_INVERTED_AIG(aig));
  assert(aig->cnf_id > 0);
  assert((size_t) aig->cnf_id < BZLA_SIZE_STACK(amgr->cnfid2aig));
  assert(amgr->cnfid2aig.start[aig->cnf_id] == aig->id);
  if (amgr->smgr->have_restore) return;
  amgr->cnfid2aig.start[aig->cnf_id] = 0;
  bzla_sat_mgr_release_cnf_id(amgr->smgr, aig->cnf_id);
  aig->cnf_id = 0;
}

static void
delete_aig_node(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(!BZLA_IS_INVERTED_AIG(aig));
  assert(amgr);
  if (bzla_aig_is_const(aig)) return;
  if (aig->cnf_id) release_cnf_id_aig_mgr(amgr, aig);
  amgr->id2aig.start[aig->id] = 0;
  if (aig->is_var)
  {
    amgr->cur_num_aig_vars--;
    BZLA_DELETE(amgr->bzla->mm, aig);
  }
  else
  {
    amgr->cur_num_aigs--;
    bzla_mem_free(amgr->bzla->mm, aig, sizeof(BzlaAIG) + 2 * sizeof(int32_t));
  }
}

static uint32_t
hash_aig(int32_t id0, int32_t id1, uint32_t table_size)
{
  uint32_t hash;
  assert(table_size > 0);
  assert(bzla_util_is_power_of_2(table_size));
  hash = 547789289u * (uint32_t) abs(id0);
  hash += 786695309u * (uint32_t) abs(id1);
  hash *= BZLA_AIG_UNIQUE_TABLE_PRIME;
  hash &= table_size - 1;
  return hash;
}

static uint32_t
compute_aig_hash(BzlaAIG *aig, uint32_t table_size)
{
  uint32_t hash;
  assert(!BZLA_IS_INVERTED_AIG(aig));
  assert(bzla_aig_is_and(aig));
  hash = hash_aig(aig->children[0], aig->children[1], table_size);
  return hash;
}

static void
delete_aig_nodes_unique_table_entry(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  uint32_t hash;
  BzlaAIG *cur, *prev;
  assert(amgr);
  assert(!BZLA_IS_INVERTED_AIG(aig));
  assert(bzla_aig_is_and(aig));
  prev = 0;
  hash = compute_aig_hash(aig, amgr->table.size);
  cur  = bzla_aig_get_by_id(amgr, amgr->table.chains[hash]);
  while (cur != aig)
  {
    assert(!BZLA_IS_INVERTED_AIG(cur));
    prev = cur;
    cur  = bzla_aig_get_by_id(amgr, cur->next);
  }
  assert(cur);
  if (!prev)
    amgr->table.chains[hash] = cur->next;
  else
    prev->next = cur->next;
  amgr->table.num_elements--;
}

static void
inc_aig_ref_counter(BzlaAIG *aig)
{
  if (!bzla_aig_is_const(aig))
  {
    BZLA_ABORT(BZLA_REAL_ADDR_AIG(aig)->refs == UINT32_MAX,
               "reference counter overflow");
    BZLA_REAL_ADDR_AIG(aig)->refs++;
  }
}

static BzlaAIG *
inc_aig_ref_counter_and_return(BzlaAIG *aig)
{
  inc_aig_ref_counter(aig);
  return aig;
}

static int32_t *
find_and_aig(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  assert(amgr);
  assert(!bzla_aig_is_const(left));
  assert(!bzla_aig_is_const(right));

  BzlaAIG *cur;
  uint32_t hash;
  int32_t *result;

  if (bzla_opt_get(amgr->bzla, BZLA_OPT_RW_SORT_AIG) > 0
      && BZLA_REAL_ADDR_AIG(right)->id < BZLA_REAL_ADDR_AIG(left)->id)
  {
    BZLA_SWAP(BzlaAIG *, left, right);
  }

  hash   = hash_aig(BZLA_REAL_ADDR_AIG(left)->id,
                  BZLA_REAL_ADDR_AIG(right)->id,
                  amgr->table.size);
  result = amgr->table.chains + hash;
  cur    = bzla_aig_get_by_id(amgr, *result);
  while (cur)
  {
    assert(!BZLA_IS_INVERTED_AIG(cur));
    assert(bzla_aig_is_and(cur));
    if (bzla_aig_get_left_child(amgr, cur) == left
        && bzla_aig_get_right_child(amgr, cur) == right)
      break;
#ifndef NDEBUG
    if (bzla_opt_get(amgr->bzla, BZLA_OPT_RW_SORT_AIG) > 0)
      assert(bzla_aig_get_left_child(amgr, cur) != right
             || bzla_aig_get_right_child(amgr, cur) != left);
#endif
    result = &cur->next;
    cur    = cur->next == 0 ? 0 : bzla_aig_get_by_id(amgr, cur->next);
  }
  return result;
}

static BzlaAIG *
find_and_aig_node(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  int32_t *lookup;
  BzlaAIG *res;
  lookup = find_and_aig(amgr, left, right);
  assert(lookup);
  res = *lookup ? bzla_aig_get_by_id(amgr, *lookup) : 0;
  return res;
}

static void
enlarge_aig_nodes_unique_table(BzlaAIGMgr *amgr)
{
  BzlaMemMgr *mm;
  int32_t *new_chains;
  uint32_t i, size, new_size;
  uint32_t hash;
  BzlaAIG *temp = 0;
  BzlaAIG *cur  = 0;
  assert(amgr);
  size     = amgr->table.size;
  new_size = size << 1;
  assert(new_size / size == 2);
  mm = amgr->bzla->mm;
  BZLA_CNEWN(mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = bzla_aig_get_by_id(amgr, amgr->table.chains[i]);
    while (cur)
    {
      assert(!BZLA_IS_INVERTED_AIG(cur));
      assert(bzla_aig_is_and(cur));
      temp             = bzla_aig_get_by_id(amgr, cur->next);
      hash             = compute_aig_hash(cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur->id;
      cur              = temp;
    }
  }
  BZLA_RELEASE_AIG_UNIQUE_TABLE(mm, amgr->table);
  amgr->table.size   = new_size;
  amgr->table.chains = new_chains;
}

BzlaAIG *
bzla_aig_copy(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(amgr);
  (void) amgr;
  if (bzla_aig_is_const(aig)) return aig;
  return inc_aig_ref_counter_and_return(aig);
}

void
bzla_aig_release(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  BzlaAIG *cur, *l, *r;
  BzlaAIGPtrStack stack;
  BzlaMemMgr *mm;

  assert(amgr);
  mm = amgr->bzla->mm;

  if (!bzla_aig_is_const(aig))
  {
    cur = BZLA_REAL_ADDR_AIG(aig);
    assert(cur->refs > 0u);
    if (cur->refs > 1u)
    {
      cur->refs--;
    }
    else
    {
      assert(cur->refs == 1u);
      BZLA_INIT_STACK(mm, stack);
      goto BZLA_RELEASE_AIG_WITHOUT_POP;

      while (!BZLA_EMPTY_STACK(stack))
      {
        cur = BZLA_POP_STACK(stack);
        cur = BZLA_REAL_ADDR_AIG(cur);

        if (cur->refs > 1u)
        {
          cur->refs--;
        }
        else
        {
        BZLA_RELEASE_AIG_WITHOUT_POP:
          assert(cur->refs == 1u);
          if (!bzla_aig_is_var(cur))
          {
            assert(bzla_aig_is_and(cur));
            l = bzla_aig_get_left_child(amgr, cur);
            r = bzla_aig_get_right_child(amgr, cur);
            BZLA_PUSH_STACK(stack, r);
            BZLA_PUSH_STACK(stack, l);
            delete_aig_nodes_unique_table_entry(amgr, cur);
          }

          delete_aig_node(amgr, cur);
        }
      }
      BZLA_RELEASE_STACK(stack);
    }
  }
}

BzlaAIG *
bzla_aig_var(BzlaAIGMgr *amgr)
{
  BzlaAIG *aig;
  assert(amgr);
  BZLA_CNEW(amgr->bzla->mm, aig);
  setup_aig_and_add_to_id_table(amgr, aig);
  aig->is_var = 1;
  amgr->cur_num_aig_vars++;
  if (amgr->max_num_aig_vars < amgr->cur_num_aig_vars)
    amgr->max_num_aig_vars = amgr->cur_num_aig_vars;
  return aig;
}

BzlaAIG *
bzla_aig_not(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(amgr);
  (void) amgr;
  inc_aig_ref_counter(aig);
  return BZLA_INVERT_AIG(aig);
}

static bool
find_and_contradiction_aig(
    BzlaAIGMgr *amgr, BzlaAIG *aig, BzlaAIG *a0, BzlaAIG *a1, uint32_t *calls)
{
  assert(amgr);
  assert(aig);
  assert(a0);
  assert(a1);
  assert(calls);
  (void) amgr;

  if (*calls >= BZLA_FIND_AND_AIG_CONTRADICTION_LIMIT) return false;

  if (!BZLA_IS_INVERTED_AIG(aig) && bzla_aig_is_and(aig))
  {
    if (bzla_aig_get_left_child(amgr, aig) == BZLA_INVERT_AIG(a0)
        || bzla_aig_get_left_child(amgr, aig) == BZLA_INVERT_AIG(a1)
        || bzla_aig_get_right_child(amgr, aig) == BZLA_INVERT_AIG(a0)
        || bzla_aig_get_right_child(amgr, aig) == BZLA_INVERT_AIG(a1))
      return true;
    *calls += 1;
    return find_and_contradiction_aig(
               amgr, bzla_aig_get_left_child(amgr, aig), a0, a1, calls)
           || find_and_contradiction_aig(
               amgr, bzla_aig_get_right_child(amgr, aig), a0, a1, calls);
  }
  return false;
}

static BzlaAIG *
simp_aig_by_sat(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  int32_t lit, val, repr, sign;
  BzlaAIG *res;

  /* fixed handling for const aigs not supported by minisat
   * (returns 0) FIXME why? */
  if (bzla_aig_is_const(aig)) return aig;

  lit = bzla_aig_get_cnf_id(aig);
  if (!lit) return aig;
  val = bzla_sat_fixed(amgr->smgr, lit);
  if (val) return (val < 0) ? BZLA_AIG_FALSE : BZLA_AIG_TRUE;
  repr = bzla_sat_repr(amgr->smgr, lit);
  if ((sign = (repr < 0))) repr = -repr;
  assert(repr >= 0);
  assert((size_t) repr < BZLA_SIZE_STACK(amgr->cnfid2aig));
  res = bzla_aig_get_by_id(amgr, amgr->cnfid2aig.start[repr]);
  if (!res) return aig;
  if (sign) res = BZLA_INVERT_AIG(res);
  return res;
}

BzlaAIG *
bzla_aig_and(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  BzlaAIG *res, *real_left, *real_right;
  int32_t *lookup;
  uint32_t calls;

  assert(amgr);

  if (amgr->smgr->initialized)
  {
    left  = simp_aig_by_sat(amgr, left);
    right = simp_aig_by_sat(amgr, right);
  }

  calls = 0;

BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN:
  if (left == BZLA_AIG_FALSE || right == BZLA_AIG_FALSE) return BZLA_AIG_FALSE;

  if (left == BZLA_AIG_TRUE) return inc_aig_ref_counter_and_return(right);

  if (right == BZLA_AIG_TRUE || (left == right))
    return inc_aig_ref_counter_and_return(left);
  if (left == BZLA_INVERT_AIG(right)) return BZLA_AIG_FALSE;

  real_left  = BZLA_REAL_ADDR_AIG(left);
  real_right = BZLA_REAL_ADDR_AIG(right);

  /* 2 level minimization rules for AIGs */
  /* first rule of contradiction */
  if (bzla_aig_is_and(real_left) && !BZLA_IS_INVERTED_AIG(left))
  {
    if (bzla_aig_get_left_child(amgr, real_left) == BZLA_INVERT_AIG(right)
        || bzla_aig_get_right_child(amgr, real_left) == BZLA_INVERT_AIG(right))
      return BZLA_AIG_FALSE;
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_right) == BZLA_INVERT_AIG(left)
        || bzla_aig_get_right_child(amgr, real_right) == BZLA_INVERT_AIG(left))
      return BZLA_AIG_FALSE;
  }
  /* second rule of contradiction */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && !BZLA_IS_INVERTED_AIG(left) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_left)
            == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_left_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)))
      return BZLA_AIG_FALSE;
  }
  /* first rule of subsumption */
  if (bzla_aig_is_and(real_left) && BZLA_IS_INVERTED_AIG(left))
  {
    if (bzla_aig_get_left_child(amgr, real_left) == BZLA_INVERT_AIG(right)
        || bzla_aig_get_right_child(amgr, real_left) == BZLA_INVERT_AIG(right))
      return inc_aig_ref_counter_and_return(right);
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_right) == BZLA_INVERT_AIG(left)
        || bzla_aig_get_right_child(amgr, real_right) == BZLA_INVERT_AIG(left))
      return inc_aig_ref_counter_and_return(left);
  }
  /* second rule of subsumption */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && BZLA_IS_INVERTED_AIG(left) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_left)
            == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_left_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)))
      return inc_aig_ref_counter_and_return(right);
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && !BZLA_IS_INVERTED_AIG(left) && BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_left)
            == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_left_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
        || bzla_aig_get_right_child(amgr, real_left)
               == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)))
      return inc_aig_ref_counter_and_return(left);
  }
  /* rule of resolution */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && BZLA_IS_INVERTED_AIG(left) && BZLA_IS_INVERTED_AIG(right))
  {
    if ((bzla_aig_get_left_child(amgr, real_left)
             == bzla_aig_get_left_child(amgr, real_right)
         && bzla_aig_get_right_child(amgr, real_left)
                == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)))
        || (bzla_aig_get_left_child(amgr, real_left)
                == bzla_aig_get_right_child(amgr, real_right)
            && bzla_aig_get_right_child(amgr, real_left)
                   == BZLA_INVERT_AIG(
                       bzla_aig_get_left_child(amgr, real_right))))
      return inc_aig_ref_counter_and_return(
          BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_left)));
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && BZLA_IS_INVERTED_AIG(left) && BZLA_IS_INVERTED_AIG(right))
  {
    if ((bzla_aig_get_right_child(amgr, real_right)
             == bzla_aig_get_right_child(amgr, real_left)
         && bzla_aig_get_left_child(amgr, real_right)
                == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_left)))
        || (bzla_aig_get_right_child(amgr, real_right)
                == bzla_aig_get_left_child(amgr, real_left)
            && bzla_aig_get_left_child(amgr, real_right)
                   == BZLA_INVERT_AIG(
                       bzla_aig_get_right_child(amgr, real_left))))
      return inc_aig_ref_counter_and_return(
          BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)));
  }
  /* asymmetric rule of idempotency */
  if (bzla_aig_is_and(real_left) && !BZLA_IS_INVERTED_AIG(left))
  {
    if (bzla_aig_get_left_child(amgr, real_left) == right
        || bzla_aig_get_right_child(amgr, real_left) == right)
      return inc_aig_ref_counter_and_return(left);
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_right) == left
        || bzla_aig_get_right_child(amgr, real_right) == left)
      return inc_aig_ref_counter_and_return(right);
  }
  /* symmetric rule of idempotency */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && !BZLA_IS_INVERTED_AIG(left) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_left)
            == bzla_aig_get_left_child(amgr, real_right)
        || bzla_aig_get_right_child(amgr, real_left)
               == bzla_aig_get_left_child(amgr, real_right))
    {
      right = bzla_aig_get_right_child(amgr, real_right);
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && bzla_aig_is_and(real_left)
      && !BZLA_IS_INVERTED_AIG(left) && !BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_left)
            == bzla_aig_get_right_child(amgr, real_right)
        || bzla_aig_get_right_child(amgr, real_left)
               == bzla_aig_get_right_child(amgr, real_right))
    {
      right = bzla_aig_get_left_child(amgr, real_right);
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* asymmetric rule of substitution */
  if (bzla_aig_is_and(real_left) && BZLA_IS_INVERTED_AIG(left))
  {
    if (bzla_aig_get_right_child(amgr, real_left) == right)
    {
      left = BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_left));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (bzla_aig_get_left_child(amgr, real_left) == right)
    {
      left = BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_left));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && BZLA_IS_INVERTED_AIG(right))
  {
    if (bzla_aig_get_left_child(amgr, real_right) == left)
    {
      right = BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if (bzla_aig_get_right_child(amgr, real_right) == left)
    {
      right = BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* symmetric rule of substitution */
  if (bzla_aig_is_and(real_left) && BZLA_IS_INVERTED_AIG(left)
      && bzla_aig_is_and(real_right) && !BZLA_IS_INVERTED_AIG(right))
  {
    if ((bzla_aig_get_right_child(amgr, real_left)
         == bzla_aig_get_left_child(amgr, real_right))
        || (bzla_aig_get_right_child(amgr, real_left)
            == bzla_aig_get_right_child(amgr, real_right)))
    {
      left = BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_left));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((bzla_aig_get_left_child(amgr, real_left)
         == bzla_aig_get_left_child(amgr, real_right))
        || (bzla_aig_get_left_child(amgr, real_left)
            == bzla_aig_get_right_child(amgr, real_right)))
    {
      left = BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_left));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }
  /* use commutativity */
  if (bzla_aig_is_and(real_right) && BZLA_IS_INVERTED_AIG(right)
      && bzla_aig_is_and(real_left) && !BZLA_IS_INVERTED_AIG(left))
  {
    if ((bzla_aig_get_left_child(amgr, real_right)
         == bzla_aig_get_right_child(amgr, real_left))
        || (bzla_aig_get_left_child(amgr, real_right)
            == bzla_aig_get_left_child(amgr, real_left)))
    {
      right = BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
    if ((bzla_aig_get_right_child(amgr, real_right)
         == bzla_aig_get_right_child(amgr, real_left))
        || (bzla_aig_get_right_child(amgr, real_right)
            == bzla_aig_get_left_child(amgr, real_left)))
    {
      right = BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right));
      goto BZLA_AIG_TWO_LEVEL_OPT_TRY_AGAIN;
    }
  }

  if (find_and_contradiction_aig(amgr, left, left, right, &calls)
      || find_and_contradiction_aig(amgr, right, left, right, &calls))
    return BZLA_AIG_FALSE;

  // Implicit XOR normalization .... (TODO keep it?)

  if (BZLA_IS_INVERTED_AIG(left) && bzla_aig_is_and(real_left)
      && BZLA_IS_INVERTED_AIG(right) && bzla_aig_is_and(real_right)
      && bzla_aig_get_left_child(amgr, real_left)
             == BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_right))
      && bzla_aig_get_right_child(amgr, real_left)
             == BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_right)))
  {
    BzlaAIG *l = find_and_aig_node(
        amgr,
        bzla_aig_get_left_child(amgr, real_left),
        BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_left)));
    if (l)
    {
      BzlaAIG *r = find_and_aig_node(
          amgr,
          BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_left)),
          bzla_aig_get_right_child(amgr, real_left));
      if (r)
      {
        res = find_and_aig_node(amgr, BZLA_INVERT_AIG(l), BZLA_INVERT_AIG(r));
        if (res)
        {
          inc_aig_ref_counter(res);
          return BZLA_INVERT_AIG(res);
        }
      }
    }
  }

  // TODO Implicit ITE normalization ....

  lookup = find_and_aig(amgr, left, right);
  assert(lookup);
  res = *lookup ? bzla_aig_get_by_id(amgr, *lookup) : 0;
  if (!res)
  {
    if (amgr->table.num_elements == amgr->table.size
        && bzla_util_log_2(amgr->table.size) < BZLA_AIG_UNIQUE_TABLE_LIMIT)
    {
      enlarge_aig_nodes_unique_table(amgr);
      lookup = find_and_aig(amgr, left, right);
    }
    if (bzla_opt_get(amgr->bzla, BZLA_OPT_RW_SORT_AIG) > 0
        && real_right->id < real_left->id)
    {
      BZLA_SWAP(BzlaAIG *, left, right);
    }
    res     = new_and_aig(amgr, left, right);
    *lookup = res->id;
    inc_aig_ref_counter(left);
    inc_aig_ref_counter(right);
    assert(amgr->table.num_elements < INT32_MAX);
    amgr->table.num_elements++;
  }
  else
  {
    inc_aig_ref_counter(res);
  }
  return res;
}

BzlaAIG *
bzla_aig_or(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  assert(amgr);
  return BZLA_INVERT_AIG(
      bzla_aig_and(amgr, BZLA_INVERT_AIG(left), BZLA_INVERT_AIG(right)));
}

BzlaAIG *
bzla_aig_eq(BzlaAIGMgr *amgr, BzlaAIG *left, BzlaAIG *right)
{
  BzlaAIG *eq, *eq_left, *eq_right;
  assert(amgr);

  eq_left  = BZLA_INVERT_AIG(bzla_aig_and(amgr, left, BZLA_INVERT_AIG(right)));
  eq_right = BZLA_INVERT_AIG(bzla_aig_and(amgr, BZLA_INVERT_AIG(left), right));
  eq       = bzla_aig_and(amgr, eq_left, eq_right);
  bzla_aig_release(amgr, eq_left);
  bzla_aig_release(amgr, eq_right);
  return eq;
}

BzlaAIG *
bzla_aig_cond(BzlaAIGMgr *amgr, BzlaAIG *a_cond, BzlaAIG *a_if, BzlaAIG *a_else)
{
  BzlaAIG *cond, *and1, *and2;
  assert(amgr);
  and1 = bzla_aig_and(amgr, a_if, a_cond);
  and2 = bzla_aig_and(amgr, a_else, BZLA_INVERT_AIG(a_cond));
  cond = bzla_aig_or(amgr, and1, and2);
  bzla_aig_release(amgr, and1);
  bzla_aig_release(amgr, and2);
  return cond;
}

BzlaAIGMgr *
bzla_aig_mgr_new(Bzla *bzla)
{
  assert(bzla);

  BzlaAIGMgr *amgr;

  BZLA_CNEW(bzla->mm, amgr);
  amgr->bzla = bzla;
  BZLA_INIT_AIG_UNIQUE_TABLE(bzla->mm, amgr->table);
  amgr->smgr = bzla_sat_mgr_new(bzla);
  BZLA_INIT_STACK(bzla->mm, amgr->id2aig);
  BZLA_PUSH_STACK(amgr->id2aig, BZLA_AIG_FALSE);
  BZLA_PUSH_STACK(amgr->id2aig, BZLA_AIG_TRUE);
  assert((size_t) BZLA_AIG_FALSE == 0);
  assert((size_t) BZLA_AIG_TRUE == 1);
  BZLA_INIT_STACK(bzla->mm, amgr->cnfid2aig);
  return amgr;
}

static BzlaAIG *
clone_aig(BzlaMemMgr *mm, BzlaAIG *aig)
{
  assert(mm);

  size_t size;
  BzlaAIG *res, *real_aig;

  if (bzla_aig_is_const(aig)) return aig;

  real_aig = BZLA_REAL_ADDR_AIG(aig);
  size     = sizeof(BzlaAIG);
  if (!real_aig->is_var) size += 2 * sizeof(int32_t);
  res = bzla_mem_malloc(mm, size);
  memcpy(res, real_aig, size);

  res = BZLA_IS_INVERTED_AIG(aig) ? BZLA_INVERT_AIG(res) : res;
  return res;
}

static void
clone_aigs(BzlaAIGMgr *amgr, BzlaAIGMgr *clone)
{
  assert(amgr);
  assert(clone);

  uint32_t i;
  size_t size;
  BzlaMemMgr *mm;
  BzlaAIG *aig;

  mm = clone->bzla->mm;

  /* clone id2aig table */
  BZLA_INIT_STACK(mm, clone->id2aig);
  size = BZLA_SIZE_STACK(amgr->id2aig);
  if (size)
  {
    BZLA_CNEWN(mm, clone->id2aig.start, size);
    clone->id2aig.end = clone->id2aig.start + size;
    clone->id2aig.top = clone->id2aig.start + BZLA_COUNT_STACK(amgr->id2aig);
  }
  for (i = 0; i < BZLA_COUNT_STACK(amgr->id2aig); i++)
  {
    aig = clone_aig(mm, BZLA_PEEK_STACK(amgr->id2aig, i));
    BZLA_POKE_STACK(clone->id2aig, i, aig);
  }

  /* clone unique table */
  BZLA_CNEWN(mm, clone->table.chains, amgr->table.size);
  clone->table.size         = amgr->table.size;
  clone->table.num_elements = amgr->table.num_elements;
  memcpy(clone->table.chains,
         amgr->table.chains,
         amgr->table.size * sizeof(int32_t));

  /* clone cnfid2aig table */
  BZLA_INIT_STACK(mm, clone->cnfid2aig);
  size = BZLA_SIZE_STACK(amgr->cnfid2aig);
  if (size)
  {
    BZLA_CNEWN(mm, clone->cnfid2aig.start, size);
    clone->cnfid2aig.end = clone->cnfid2aig.start + size;
    clone->cnfid2aig.top = clone->cnfid2aig.start;
    memcpy(
        clone->cnfid2aig.start, amgr->cnfid2aig.start, size * sizeof(int32_t));
  }
  assert(BZLA_SIZE_STACK(clone->cnfid2aig) == BZLA_SIZE_STACK(amgr->cnfid2aig));
  assert(BZLA_COUNT_STACK(clone->cnfid2aig)
         == BZLA_COUNT_STACK(amgr->cnfid2aig));
}

BzlaAIGMgr *
bzla_aig_mgr_clone(Bzla *bzla, BzlaAIGMgr *amgr)
{
  assert(bzla);
  assert(amgr);

  BzlaAIGMgr *res;

  BZLA_CNEW(bzla->mm, res);
  res->bzla = bzla;

  res->smgr = bzla_sat_mgr_clone(bzla, amgr->smgr);
  /* Note: we do not yet clone aigs here (we need the clone of the aig
   *       manager for that). */
  res->max_num_aigs     = amgr->max_num_aigs;
  res->max_num_aig_vars = amgr->max_num_aig_vars;
  res->cur_num_aigs     = amgr->cur_num_aigs;
  res->cur_num_aig_vars = amgr->cur_num_aig_vars;
  res->num_cnf_vars     = amgr->num_cnf_vars;
  res->num_cnf_clauses  = amgr->num_cnf_clauses;
  res->num_cnf_literals = amgr->num_cnf_literals;
  clone_aigs(amgr, res);
  return res;
}

void
bzla_aig_mgr_delete(BzlaAIGMgr *amgr)
{
  BzlaMemMgr *mm;
  assert(amgr);
  assert(getenv("BZLALEAK") || getenv("BZLALEAKAIG")
         || amgr->table.num_elements == 0);
  mm = amgr->bzla->mm;
  BZLA_RELEASE_AIG_UNIQUE_TABLE(mm, amgr->table);
  bzla_sat_mgr_delete(amgr->smgr);
  BZLA_RELEASE_STACK(amgr->id2aig);
  BZLA_RELEASE_STACK(amgr->cnfid2aig);
  BZLA_DELETE(mm, amgr);
}

static bool
is_xor_aig(BzlaAIGMgr *amgr, BzlaAIG *aig, BzlaAIGPtrStack *leafs)
{
#ifdef BZLA_AIG_TO_CNF_EXTRACT_XOR
  BzlaAIG *l, *r, *ll, *lr, *rl, *rr;

  assert(bzla_aig_is_and(aig));
  assert(!BZLA_IS_INVERTED_AIG(aig));

  l = bzla_aig_get_left_child(amgr, aig);
  if (!BZLA_IS_INVERTED_AIG(l)) return false;
  l = BZLA_REAL_ADDR_AIG(l);
#ifdef BZLA_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (l->refs > 1) return false;
#endif

  r = bzla_aig_get_right_child(amgr, aig);
  if (!BZLA_IS_INVERTED_AIG(r)) return false;
  r = BZLA_REAL_ADDR_AIG(r);
#ifdef BZLA_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (r->refs > 1) return false;
#endif

  ll = bzla_aig_get_left_child(amgr, l);
  lr = bzla_aig_get_right_child(amgr, l);

  rl = bzla_aig_get_left_child(amgr, r);
  rr = bzla_aig_get_right_child(amgr, r);

  if (ll == BZLA_INVERT_AIG(rl) && lr == BZLA_INVERT_AIG(rr))
  {
    BZLA_PUSH_STACK(*leafs, rr);
    BZLA_PUSH_STACK(*leafs, ll);
    return true;
  }

  assert(!bzla_opt_get(amgr->bzla, BZLA_OPT_RW_SORT_AIG)
         || ll != BZLA_INVERT_AIG(rr) || lr != BZLA_INVERT_AIG(rl));

  return false;
#else
  (void) amgr;
  (void) aig;
  (void) leafs;
  return false;
#endif
}

static bool
is_ite_aig(BzlaAIGMgr *amgr, BzlaAIG *aig, BzlaAIGPtrStack *leafs)
{
#ifdef BZLA_AIG_TO_CNF_EXTRACT_ITE
  BzlaAIG *l, *r, *ll, *lr, *rl, *rr;

  assert(bzla_aig_is_and(aig));
  assert(!BZLA_IS_INVERTED_AIG(aig));

  l = bzla_aig_get_left_child(amgr, aig);
  if (!BZLA_IS_INVERTED_AIG(l)) return false;
  l = BZLA_REAL_ADDR_AIG(l);
#ifdef BZLA_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (l->refs > 1) return false;
#endif

  r = bzla_aig_get_right_child(amgr, aig);
  if (!BZLA_IS_INVERTED_AIG(r)) return false;
  r = BZLA_REAL_ADDR_AIG(r);
#ifdef BZLA_AIG_TO_CNF_EXTRACT_ONLY_NON_SHARED
  if (r->refs > 1) return false;
#endif

  ll = bzla_aig_get_left_child(amgr, l);
  lr = bzla_aig_get_right_child(amgr, l);

  rl = bzla_aig_get_left_child(amgr, r);
  rr = bzla_aig_get_right_child(amgr, r);

  // aig == (!ll | !lr)(!rl | !rr)

  if (BZLA_INVERT_AIG(lr) == rl)
  {
    // aig == (!rl -> !ll)(rl -> !rr) = rl ? !rr : !ll
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(ll));  // else
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(rr));  // then
    BZLA_PUSH_STACK(*leafs, rl);                   // cond
    return true;
  }
  if (BZLA_INVERT_AIG(ll) == rl)
  {
    // aig == (!rl -> !lr)(rl -> !rr)
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(lr));  // else
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(rr));  // then
    BZLA_PUSH_STACK(*leafs, rl);                   // cond
    return true;
  }
  if (BZLA_INVERT_AIG(lr) == rr)
  {
    // aig == (!rr -> !ll)(rr -> !rl)
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(ll));  // else
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(rl));  // then
    BZLA_PUSH_STACK(*leafs, rr);                   // cond
    return true;
  }
  if (BZLA_INVERT_AIG(ll) == rr)
  {
    // aig == (!rr -> !lr)(rr -> !rl)
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(lr));  // else
    BZLA_PUSH_STACK(*leafs, BZLA_INVERT_AIG(rl));  // then
    BZLA_PUSH_STACK(*leafs, rr);                   // cond
    return true;
  }

  return false;
#else
  (void) amgr;
  (void) aig;
  (void) leafs;
  return false;
#endif
}

static void
set_next_id_aig_mgr(BzlaAIGMgr *amgr, BzlaAIG *root)
{
  assert(!BZLA_IS_INVERTED_AIG(root));
  assert(!root->cnf_id);
  root->cnf_id = bzla_sat_mgr_next_cnf_id(amgr->smgr);
  assert(root->cnf_id > 0);
  BZLA_FIT_STACK(amgr->cnfid2aig, (size_t) root->cnf_id);
  amgr->cnfid2aig.start[root->cnf_id] = root->id;
  assert(amgr->cnfid2aig.start[root->cnf_id] == root->id);
  amgr->num_cnf_vars++;
}

#ifdef BZLA_EXTRACT_TOP_LEVEL_MULTI_OR
static bool
is_or_aig(BzlaAIGMgr *amgr, BzlaAIG *root, BzlaAIGPtrStack *leafs)
{
  assert(amgr);
  assert(root);
  assert(leafs);
  assert(BZLA_EMPTY_STACK(*leafs));

  BzlaAIG *real_cur, *cur, **p;
  BzlaAIGPtrStack tree;
  BzlaMemMgr *mm;

  if (!BZLA_IS_INVERTED_AIG(root) || !bzla_aig_is_and(BZLA_REAL_ADDR_AIG(root)))
    return false;

  mm   = amgr->bzla->mm;
  root = BZLA_REAL_ADDR_AIG(root);

  BZLA_INIT_STACK(mm, tree);
  BZLA_PUSH_STACK(tree, bzla_aig_get_right_child(amgr, root));
  BZLA_PUSH_STACK(tree, bzla_aig_get_left_child(amgr, root));

  while (!BZLA_EMPTY_STACK(tree))
  {
    cur      = BZLA_POP_STACK(tree);
    real_cur = BZLA_REAL_ADDR_AIG(cur);

    if (bzla_aig_is_const(real_cur))
    {
      assert(cur == BZLA_AIG_FALSE);
      continue;
    }

    if (real_cur->mark) continue;

    if (!BZLA_IS_INVERTED_AIG(cur) && bzla_aig_is_and(real_cur))
    {
      BZLA_PUSH_STACK(tree, bzla_aig_get_right_child(amgr, real_cur));
      BZLA_PUSH_STACK(tree, bzla_aig_get_left_child(amgr, real_cur));
    }
    else
    {
      BZLA_PUSH_STACK(*leafs, cur);
      real_cur->mark = 1;
    }
  }

  for (p = (*leafs).start; p < (*leafs).top; p++)
  {
    cur = *p;
    assert(BZLA_REAL_ADDR_AIG(cur)->mark);
    BZLA_REAL_ADDR_AIG(cur)->mark = 0;
  }

  BZLA_RELEASE_STACK(tree);
  return true;
}
#endif

void
bzla_aig_to_sat_tseitin(BzlaAIGMgr *amgr, BzlaAIG *start)
{
  BzlaAIGPtrStack stack, tree, leafs, marked;
  int32_t x, y, a, b, c;
  bool isxor, isite;
  BzlaAIG *root, *cur;
  BzlaSATMgr *smgr;
  BzlaMemMgr *mm;
  uint32_t local;
  BzlaAIG **p;

  if (bzla_aig_is_const(start)) return;

  assert(amgr);

  smgr = amgr->smgr;
  mm   = amgr->bzla->mm;

  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, tree);
  BZLA_INIT_STACK(mm, leafs);
  BZLA_INIT_STACK(mm, marked);

  start = BZLA_REAL_ADDR_AIG(start);
  BZLA_PUSH_STACK(stack, start);

  while (!BZLA_EMPTY_STACK(stack))
  {
    root = BZLA_REAL_ADDR_AIG(BZLA_POP_STACK(stack));

    if (root->mark == 2)
    {
      assert(root->cnf_id);
      assert(root->local < root->refs);
      root->local++;
      continue;
    }

    if (root->cnf_id) continue;

    if (bzla_aig_is_var(root))
    {
      set_next_id_aig_mgr(amgr, root);
      continue;
    }

    assert(root->mark < 2);
    assert(bzla_aig_is_and(root));
    assert(BZLA_EMPTY_STACK(tree));
    assert(BZLA_EMPTY_STACK(leafs));

    if ((isxor = is_xor_aig(amgr, root, &leafs)))
      isite = 0;
    else
      isite = is_ite_aig(amgr, root, &leafs);

    if (!isxor && !isite)
    {
#ifdef BZLA_AIG_TO_CNF_NARY_AND
      BZLA_PUSH_STACK(tree, bzla_aig_get_right_child(amgr, root));
      BZLA_PUSH_STACK(tree, bzla_aig_get_left_child(amgr, root));

      while (!BZLA_EMPTY_STACK(tree))
      {
        cur = BZLA_POP_STACK(tree);

        if (BZLA_IS_INVERTED_AIG(cur) || bzla_aig_is_var(cur) || cur->refs > 1u
            || cur->cnf_id)
        {
          BZLA_PUSH_STACK(leafs, cur);
        }
        else
        {
          BZLA_PUSH_STACK(tree, bzla_aig_get_right_child(amgr, cur));
          BZLA_PUSH_STACK(tree, bzla_aig_get_left_child(amgr, cur));
        }
      }
#else
      BZLA_PUSH_STACK(leafs, bzla_aig_get_left_child(amgr, root));
      BZLA_PUSH_STACK(leafs, bzla_aig_get_right_child(amgr, root));
#endif
    }

    if (root->mark == 0)
    {
      root->mark = 1;
      assert(root->refs >= 1);
      assert(!root->local);
      root->local = 1;
      BZLA_PUSH_STACK(marked, root);
      BZLA_PUSH_STACK(stack, root);
      for (p = leafs.start; p < leafs.top; p++) BZLA_PUSH_STACK(stack, *p);
    }
    else
    {
      assert(root->mark == 1);
      root->mark = 2;

      set_next_id_aig_mgr(amgr, root);
      x = root->cnf_id;
      assert(x);

      if (isxor)
      {
        assert(BZLA_COUNT_STACK(leafs) == 2);
        a = bzla_aig_get_cnf_id(leafs.start[0]);
        b = bzla_aig_get_cnf_id(leafs.start[1]);

        bzla_sat_add(smgr, -x);
        bzla_sat_add(smgr, a);
        bzla_sat_add(smgr, -b);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, -x);
        bzla_sat_add(smgr, -a);
        bzla_sat_add(smgr, b);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, x);
        bzla_sat_add(smgr, -a);
        bzla_sat_add(smgr, -b);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, x);
        bzla_sat_add(smgr, a);
        bzla_sat_add(smgr, b);
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses += 4;
        amgr->num_cnf_literals += 12;
      }
      else if (isite)
      {
        assert(BZLA_COUNT_STACK(leafs) == 3);
        a = bzla_aig_get_cnf_id(leafs.start[0]);  // else
        b = bzla_aig_get_cnf_id(leafs.start[1]);  // then
        c = bzla_aig_get_cnf_id(leafs.start[2]);  // cond

        bzla_sat_add(smgr, -x);
        bzla_sat_add(smgr, -c);
        bzla_sat_add(smgr, b);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, -x);
        bzla_sat_add(smgr, c);
        bzla_sat_add(smgr, a);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, x);
        bzla_sat_add(smgr, -c);
        bzla_sat_add(smgr, -b);
        bzla_sat_add(smgr, 0);

        bzla_sat_add(smgr, x);
        bzla_sat_add(smgr, c);
        bzla_sat_add(smgr, -a);
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses += 4;
        amgr->num_cnf_literals += 12;
      }
      else
      {
        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = bzla_aig_get_cnf_id(cur);
          assert(y);
          bzla_sat_add(smgr, -y);
          amgr->num_cnf_literals++;
        }
        bzla_sat_add(smgr, x);
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals++;

        for (p = leafs.start; p < leafs.top; p++)
        {
          cur = *p;
          y   = bzla_aig_get_cnf_id(cur);
          bzla_sat_add(smgr, -x);
          bzla_sat_add(smgr, y);
          bzla_sat_add(smgr, 0);
          amgr->num_cnf_clauses++;
          amgr->num_cnf_literals += 2;
        }
      }
    }
    BZLA_RESET_STACK(leafs);
  }
  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(leafs);
  BZLA_RELEASE_STACK(tree);

  while (!BZLA_EMPTY_STACK(marked))
  {
    cur = BZLA_POP_STACK(marked);
    assert(!BZLA_IS_INVERTED_AIG(cur));
    assert(cur->mark > 0);
    cur->mark = 0;
    assert(cur->cnf_id);
    assert(bzla_aig_is_and(cur));
    local = cur->local;
    assert(local > 0);
    cur->local = 0;
    if (cur == start) continue;
    assert(cur->refs >= local);
    if (cur->refs > local) continue;
    release_cnf_id_aig_mgr(amgr, cur);
  }
  BZLA_RELEASE_STACK(marked);
}

static void
aig_to_sat_tseitin(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(amgr);
  assert(!bzla_aig_is_const(aig));
  BZLA_MSG(amgr->bzla->msg,
           3,
           "transforming AIG into CNF using Tseitin transformation");
  bzla_aig_to_sat_tseitin(amgr, aig);
}

void
bzla_aig_to_sat(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(amgr);
  if (!bzla_sat_is_initialized(amgr->smgr)) return;
  if (!bzla_aig_is_const(aig)) aig_to_sat_tseitin(amgr, aig);
}

void
bzla_aig_add_toplevel_to_sat(BzlaAIGMgr *amgr, BzlaAIG *root)
{
  assert(amgr);
  assert(root);

  if (!bzla_sat_is_initialized(amgr->smgr)) return;

#ifdef BZLA_AIG_TO_CNF_TOP_ELIM
  BzlaMemMgr *mm;
  BzlaSATMgr *smgr;
  BzlaAIG *aig, *left;
  BzlaAIGPtrStack stack;
#ifdef BZLA_EXTRACT_TOP_LEVEL_MULTI_OR
  BzlaAIGPtrStack leafs;
  BzlaAIG **p;
#else
  BzlaAIG *real_aig, *right;
#endif

  mm   = amgr->bzla->mm;
  smgr = amgr->smgr;

  if (!bzla_sat_is_initialized(smgr)) return;

  if (root == BZLA_AIG_TRUE) return;

  if (root == BZLA_AIG_FALSE)
  {
    bzla_sat_add(smgr, 0); /* add empty clause */
    amgr->num_cnf_clauses++;
    return;
  }

  BZLA_INIT_STACK(mm, stack);
  aig = root;
  goto BZLA_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP;

  while (!BZLA_EMPTY_STACK(stack))
  {
    aig = BZLA_POP_STACK(stack);
  BZLA_ADD_TOPLEVEL_AIG_TO_SAT_WITHOUT_POP:
    if (!BZLA_IS_INVERTED_AIG(aig) && bzla_aig_is_and(aig))
    {
      BZLA_PUSH_STACK(stack, bzla_aig_get_right_child(amgr, aig));
      BZLA_PUSH_STACK(stack, bzla_aig_get_left_child(amgr, aig));
    }
    else
    {
#ifdef BZLA_EXTRACT_TOP_LEVEL_MULTI_OR
      BZLA_INIT_STACK(mm, leafs);
      if (is_or_aig(amgr, aig, &leafs))
      {
        assert(BZLA_COUNT_STACK(leafs) > 1);
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          if (bzla_aig_is_const(left))  // TODO reachable?
            continue;
          bzla_aig_to_sat(amgr, left);
        }
        for (p = leafs.start; p < leafs.top; p++)
        {
          left = *p;
          assert(bzla_aig_get_cnf_id(left));
          bzla_sat_add(smgr, bzla_aig_get_cnf_id(BZLA_INVERT_AIG(left)));
          amgr->num_cnf_literals++;
        }
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses++;
      }
      else
      {
        bzla_aig_to_sat(amgr, aig);
        bzla_sat_add(smgr, bzla_aig_get_cnf_id(aig));
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_literals++;
        amgr->num_cnf_clauses++;
      }
      BZLA_RELEASE_STACK(leafs);
#else
      real_aig = BZLA_REAL_ADDR_AIG(aig);
      if (BZLA_IS_INVERTED_AIG(aig) && bzla_aig_is_and(real_aig))
      {
        left  = BZLA_INVERT_AIG(bzla_aig_get_left_child(amgr, real_aig));
        right = BZLA_INVERT_AIG(bzla_aig_get_right_child(amgr, real_aig));
        bzla_aig_to_sat(amgr, left);
        bzla_aig_to_sat(amgr, right);
        bzla_sat_add(smgr, bzla_aig_get_cnf_id(left));
        bzla_sat_add(smgr, bzla_aig_get_cnf_id(right));
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals += 2;
      }
      else
      {
        bzla_aig_to_sat(amgr, aig);
        bzla_sat_add(smgr, bzla_aig_get_cnf_id(aig));
        bzla_sat_add(smgr, 0);
        amgr->num_cnf_clauses++;
        amgr->num_cnf_literals++;
      }
#endif
    }
  }
  BZLA_RELEASE_STACK(stack);
#else
  if (root == BZLA_AIG_TRUE) return;

  if (root == BZLA_AIG_FALSE)
  {
    bzla_sat_add(amgr->smgr, 0);
    return;
  }
  bzla_aig_to_sat(amgr, root);
  bzla_sat_add(amgr->smgr, bzla_aig_get_cnf_id(root));
  bzla_sat_add(amgr->smgr, 0);
#endif
}

BzlaSATMgr *
bzla_aig_get_sat_mgr(const BzlaAIGMgr *amgr)
{
  return amgr ? amgr->smgr : 0;
}

int32_t
bzla_aig_get_assignment(BzlaAIGMgr *amgr, BzlaAIG *aig)
{
  assert(amgr);
  if (aig == BZLA_AIG_TRUE) return 1;
  if (aig == BZLA_AIG_FALSE) return -1;

  /* Note: If an AIG is not yet encoded to SAT or if the SAT solver returns
   * undefined for a variable, we implicitly initialize it with false (-1). */
  int32_t val = -1;
  if (BZLA_REAL_ADDR_AIG(aig)->cnf_id > 0)
  {
    val = bzla_sat_deref(amgr->smgr, BZLA_REAL_ADDR_AIG(aig)->cnf_id);
    if (val == 0)
    {
      val = -1;
    }
  }
  return BZLA_IS_INVERTED_AIG(aig) ? -val : val;
}

int32_t
bzla_aig_compare(const BzlaAIG *aig0, const BzlaAIG *aig1)
{
  if (aig0 == aig1) return 0;
  if (BZLA_INVERT_AIG(aig0) == aig1) return BZLA_IS_INVERTED_AIG(aig0) ? -1 : 1;
  if (BZLA_IS_INVERTED_AIG(aig0)) aig0 = BZLA_INVERT_AIG(aig0);
  if (aig0 == BZLA_AIG_FALSE) return -1;
  assert(aig0 != BZLA_AIG_TRUE);
  if (BZLA_IS_INVERTED_AIG(aig1)) aig1 = BZLA_INVERT_AIG(aig1);
  if (aig1 == BZLA_AIG_FALSE) return 1;
  assert(aig1 != BZLA_AIG_TRUE);
  return aig0->id - aig1->id;
}

/* hash AIG by id */
uint32_t
bzla_aig_hash_by_id(const BzlaAIG *aig)
{
  assert(aig);
  return (uint32_t) bzla_aig_get_id(aig) * 7334147u;
}

/* compare AIG by id */
int32_t
bzla_aig_compare_by_id(const BzlaAIG *aig0, const BzlaAIG *aig1)
{
  assert(aig0);
  assert(aig1);

  int32_t id0, id1;

  id0 = bzla_aig_get_id(aig0);
  id1 = bzla_aig_get_id(aig1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

int32_t
bzla_compare_aig_by_id_qsort_asc(const void *aig0, const void *aig1)
{
  assert(aig0);
  assert(!bzla_aig_is_const(aig0));
  assert(aig1);
  assert(!bzla_aig_is_const(aig1));

  int32_t id0, id1;

  id0 = BZLA_REAL_ADDR_AIG(*(BzlaAIG **) aig0)->id;
  id1 = BZLA_REAL_ADDR_AIG(*(BzlaAIG **) aig1)->id;
  return id0 - id1;
}
