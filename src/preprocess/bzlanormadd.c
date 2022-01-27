/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

// WIP: compact adder chains (an)
// WIP: shift negated terms on equalities over adders
//      - remove terms on both sides...
// TODO: factorize equal parts of assoc. operators (make rewrite rule global
// pass)
// TODO: normalizations of adders
//         x + 1 = -(~x)
//         x - 1 = ~(-x)
//         -(x + 1) = ~x

#include "preprocess/bzlanormadd.h"

#include <stdbool.h>

#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlasubst.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static void
add_leaf_coeff(Bzla *bzla,
               BzlaPtrHashTable *leafs,
               BzlaNode *n,
               BzlaNode *coeff)
{
  assert(leafs);
  assert(n);
  assert(coeff);
  assert(bzla_node_is_bv_const(coeff));

#ifndef NDEBUG
  /* All constants are added into one constant at the beginning of leafs */
  BzlaNode *one = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(n));
  assert(!bzla_node_is_bv_const(n) || n == one);
  bzla_node_release(bzla, one);
#endif

  BzlaPtrHashBucket *b;

  if (!(b = bzla_hashptr_table_get(leafs, n)))
  {
    b              = bzla_hashptr_table_add(leafs, bzla_node_copy(bzla, n));
    b->data.as_ptr = bzla_node_copy(bzla, coeff);
  }
  else
  {
    BzlaNode *old_coeff = b->data.as_ptr;
    b->data.as_ptr      = bzla_exp_bv_add(bzla, old_coeff, coeff);
    bzla_node_release(bzla, old_coeff);
  }
}

static void
inc_leaf_coeff(Bzla *bzla, BzlaPtrHashTable *leafs, BzlaNode *n)
{
  BzlaNode *one = bzla_exp_bv_int(bzla, 1, bzla_node_get_sort_id(n));
  /* Constants are added as coeff of one */
  if (bzla_node_is_bv_const(n))
  {
    add_leaf_coeff(bzla, leafs, one, n);
  }
  else
  {
    add_leaf_coeff(bzla, leafs, n, one);
  }
  bzla_node_release(bzla, one);
}

static BzlaNode *
mul_get_coeff(BzlaNode *n, BzlaNode **res)
{
  if (bzla_node_is_inverted(n)) return 0;
  if (!bzla_node_is_bv_mul(n)) return 0;
  if (bzla_node_is_bv_const(n->e[0]))
  {
    assert(!bzla_node_is_bv_const(n->e[1]));
    *res = n->e[1];
    return n->e[0];
  }
  if (bzla_node_is_bv_const(n->e[1]))
  {
    assert(!bzla_node_is_bv_const(n->e[0]));
    *res = n->e[0];
    return n->e[1];
  }
  return 0;
}

static void
collect_add_leafs(Bzla *bzla, BzlaNode *n, BzlaPtrHashTable *leafs)
{
  assert(n);
  assert(leafs);

  uint32_t i;
  int32_t id;
  BzlaIntHashTable *cache;
  BzlaNodePtrStack visit;
  BzlaNode *cur, *coeff, *real_cur, *res;

  // printf("*** collect\n");
  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_PUSH_STACK(visit, n);
  do
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    id       = bzla_node_get_id(cur);
    res      = 0;

    if (bzla_node_is_bv_add(real_cur) && !bzla_hashint_table_contains(cache, id)
        && real_cur->parents == 1)
    {
      bzla_hashint_table_add(cache, id);

      /* ~(x + y) = ~x + ~y + 1 */
      if (bzla_node_is_inverted(cur))
      {
        BZLA_PUSH_STACK(visit, bzla_node_invert(real_cur->e[0]));
        BZLA_PUSH_STACK(visit, bzla_node_invert(real_cur->e[1]));

        BzlaNode *one = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(cur));
        inc_leaf_coeff(bzla, leafs, one);
        // printf ("leaf (i): %s\n", bzla_util_node2string (one));
        bzla_node_release(bzla, one);
        continue;
      }

      /* only traverse along adders with one parent */
      if (real_cur->parents > 1)
      {
        // printf ("leaf (p): %s\n", bzla_util_node2string (cur));
        inc_leaf_coeff(bzla, leafs, cur);
        continue;
      }

      for (i = 0; i < real_cur->arity; i++)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if ((coeff = mul_get_coeff(cur, &res)))
    {
      assert(res);
      // printf ("mul coeff: %s\n", bzla_util_node2string(cur));
      // printf ("coeff: %s\n", bzla_util_node2string(coeff));
      // printf ("leaf: %s\n", bzla_util_node2string (res));
      add_leaf_coeff(bzla, leafs, res, coeff);
    }
    else
    {
      // printf ("leaf: %s\n", bzla_util_node2string (cur));
      inc_leaf_coeff(bzla, leafs, cur);
    }
  } while (!BZLA_EMPTY_STACK(visit));
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
}

static void
prep_leafs(Bzla *bzla, BzlaPtrHashTable *t, BzlaNodePtrStack *leafs)
{
  assert(t->count > 0);

  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  BzlaNode *cur, *coeff, *leaf;
  BzlaSortId sort_id;

  sort_id        = bzla_node_get_sort_id(t->first->key);
  BzlaNode *zero = bzla_exp_bv_zero(bzla, sort_id);

  // printf("*** prep\n");
  bzla_iter_hashptr_init(&it, t);
  while (bzla_iter_hashptr_has_next(&it))
  {
    assert(!bzla_node_is_bv_const(it.cur) || t->first->key == it.cur);
    b     = it.bucket;
    coeff = b->data.as_ptr;
    cur   = bzla_iter_hashptr_next(&it);
    assert(coeff);

    // printf ("leaf: %s (%s)\n", bzla_util_node2string (cur),
    // bzla_util_node2string(coeff));

    /* skip all nodes with coefficient zero */
    if (coeff == zero)
    {
      goto CLEANUP;
    }

#ifndef NDEBUG
    /* all leafs have been normalized to a positive coefficient */
    if (cur != t->first->key)
    {
      BzlaNode *gtz = bzla_exp_bv_sgt(bzla, coeff, zero);
      assert(gtz == bzla->true_exp);
      bzla_node_release(bzla, gtz);
    }
#endif

    /* multiply with coefficient */
    leaf = bzla_exp_bv_mul(bzla, cur, coeff);
    BZLA_PUSH_STACK(*leafs, leaf);
    // printf ("push %s\n", bzla_util_node2string(leaf));

  CLEANUP:
    bzla_node_release(bzla, coeff);
    b->data.as_ptr = 0;
    bzla_hashptr_table_remove(t, cur, 0, 0);
    bzla_node_release(bzla, cur);
  }

  BZLA_PUSH_STACK_IF(
      BZLA_EMPTY_STACK(*leafs), *leafs, bzla_node_copy(bzla, zero));
  bzla_node_release(bzla, zero);
}

static void
normalize_coeffs(Bzla *bzla,
                 BzlaSortId sort_id,
                 BzlaPtrHashTable *lhs,
                 BzlaPtrHashTable *rhs)
{
  BzlaPtrHashBucket *blhs, *brhs;
  BzlaPtrHashTableIterator it;
  BzlaNode *cur, *real_cur, *lt, *c1, *c2, *neg_coeff;

  BzlaNode *zero = bzla_exp_bv_zero(bzla, sort_id);

  assert(bzla_node_is_bv_const(lhs->first->key));

  // printf ("*** normalize coeffs\n");
  bzla_iter_hashptr_init(&it, lhs);
  // printf ("const leaf: %s (%s)\n", bzla_util_node2string(it.cur),
  // bzla_util_node2string(it.bucket->data.as_ptr));
  while (bzla_iter_hashptr_has_next(&it))
  {
    blhs     = it.bucket;
    cur      = bzla_iter_hashptr_next(&it);
    real_cur = bzla_node_real_addr(cur);

    if (bzla_node_is_bv_const(cur) || blhs->data.as_ptr == zero) continue;

      // printf ("leaf: %s (%s)\n", bzla_util_node2string(cur),
      // bzla_util_node2string(blhs->data.as_ptr));

#if 1
    /* c1 * ~x + c2 * x  -->  (c2 - c1) * x - c1 */
    if (bzla_node_is_inverted(cur)
        && (brhs = bzla_hashptr_table_get(lhs, real_cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      /* Apply only if there is an x */
      if (c2 != zero)
      {
        // printf ("c1: %s\n", bzla_util_node2string(c1));
        // printf ("c2: %s\n", bzla_util_node2string(c2));
        neg_coeff = bzla_exp_bv_neg(bzla, c1);
        add_leaf_coeff(bzla, lhs, real_cur, neg_coeff);
        // printf ("diff: %s\n",
        // bzla_util_node2string(bzla_hashptr_table_get(lhs,
        // real_cur)->data.as_ptr));
        inc_leaf_coeff(bzla, lhs, neg_coeff);
        bzla_node_release(bzla, neg_coeff);

        bzla_node_release(bzla, blhs->data.as_ptr);
        blhs->data.as_ptr = bzla_node_copy(bzla, zero);
        // printf ("n1\n");
        continue;
      }
    }
#endif

#if 1
    /* c1 * x = c2 * x  -->  0 = (c2 - c1) * x  if c1 <= c2 */
    if ((brhs = bzla_hashptr_table_get(rhs, cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      lt = bzla_exp_bv_slte(bzla, c1, c2);
      if (lt == bzla->true_exp)
      {
        neg_coeff = bzla_exp_bv_neg(bzla, c1);
        add_leaf_coeff(bzla, rhs, cur, neg_coeff);
        bzla_node_release(bzla, neg_coeff);

        bzla_node_release(bzla, blhs->data.as_ptr);
        blhs->data.as_ptr = bzla_node_copy(bzla, zero);
        // printf ("n2\n");
      }
      bzla_node_release(bzla, lt);
      continue;
    }
#endif

#if 0
    /* t1 + -c * x = t2  --> t1 = t2 + c * x  */
    lt = bzla_exp_bv_slt (bzla, blhs->data.as_ptr, zero);
    bool is_lt = lt == bzla->true_exp;
    bzla_node_release (bzla, lt);
    if (is_lt)
    {
      neg_coeff = bzla_exp_bv_neg (bzla, blhs->data.as_ptr);
      add_leaf_coeff (bzla, rhs, cur, neg_coeff);
      bzla_node_release (bzla, neg_coeff);

      bzla_node_release (bzla, blhs->data.as_ptr);
      blhs->data.as_ptr = bzla_node_copy (bzla, zero);
      //printf ("n3\n");
      continue;
    }
#endif

#if 1
    /* t1  + c * ~a + c = t2  --> t1 = t2 + c * a */
    if (bzla_node_is_inverted(cur))
    {
      c1 = blhs->data.as_ptr;
      c2 = lhs->first->data.as_ptr;

      lt         = bzla_exp_bv_sgte(bzla, c2, c1);
      bool is_lt = lt == bzla->true_exp;
      bzla_node_release(bzla, lt);
      if (is_lt)
      {
        neg_coeff = bzla_exp_bv_neg(bzla, c1);
        inc_leaf_coeff(bzla, lhs, neg_coeff);
        bzla_node_release(bzla, neg_coeff);

        add_leaf_coeff(bzla, rhs, real_cur, c1);

        bzla_node_release(bzla, blhs->data.as_ptr);
        blhs->data.as_ptr = bzla_node_copy(bzla, zero);
        // printf ("n3\n");
        continue;
      }
    }
#endif

#if 1
    /* Normalize c * ~x  -->  -c * x - c and try to substract from rhs. */
    if (bzla_node_is_inverted(cur)
        && (brhs = bzla_hashptr_table_get(rhs, real_cur)))
    {
      c1 = blhs->data.as_ptr;
      c2 = brhs->data.as_ptr;

      neg_coeff = bzla_exp_bv_neg(bzla, c1);

      /* Move cur rhs other side, add negative coefficient rhs 'lhs' */
      lt = bzla_exp_bv_slte(bzla, neg_coeff, c2);
      if (lt == bzla->true_exp)
      {
        add_leaf_coeff(bzla, rhs, real_cur, c1);
        inc_leaf_coeff(bzla, lhs, neg_coeff);

        bzla_node_release(bzla, blhs->data.as_ptr);
        blhs->data.as_ptr = bzla_node_copy(bzla, zero);
        // printf ("n4\n");
      }
      bzla_node_release(bzla, lt);
      bzla_node_release(bzla, neg_coeff);
    }
#endif
  }
  bzla_node_release(bzla, zero);
}

static BzlaNode *
normalize_eq_adds(Bzla *bzla, BzlaNode *eq)
{
  assert(bzla_node_is_regular(eq));
  assert(bzla_node_is_bv_eq(eq));

  BzlaPtrHashTable *lhs_leafs, *rhs_leafs;
  BzlaNodePtrStack lhs, rhs;
  BzlaSortId sort_id;

  sort_id = bzla_node_get_sort_id(eq->e[0]);

  BZLA_INIT_STACK(bzla->mm, lhs);
  BZLA_INIT_STACK(bzla->mm, rhs);

  lhs_leafs      = bzla_hashptr_table_new(bzla->mm,
                                     (BzlaHashPtr) bzla_node_hash_by_id,
                                     (BzlaCmpPtr) bzla_node_compare_by_id);
  rhs_leafs      = bzla_hashptr_table_new(bzla->mm,
                                     (BzlaHashPtr) bzla_node_hash_by_id,
                                     (BzlaCmpPtr) bzla_node_compare_by_id);
  BzlaNode *one  = bzla_exp_bv_one(bzla, sort_id);
  BzlaNode *zero = bzla_exp_bv_zero(bzla, sort_id);

  /* constants are stored at the first position of the hash tables */
  add_leaf_coeff(bzla, lhs_leafs, one, zero);
  add_leaf_coeff(bzla, rhs_leafs, one, zero);
  bzla_node_release(bzla, one);
  bzla_node_release(bzla, zero);

  collect_add_leafs(bzla, eq->e[0], lhs_leafs);
  collect_add_leafs(bzla, eq->e[1], rhs_leafs);

  normalize_coeffs(bzla, sort_id, lhs_leafs, rhs_leafs);
  normalize_coeffs(bzla, sort_id, rhs_leafs, lhs_leafs);

  prep_leafs(bzla, lhs_leafs, &lhs);
  prep_leafs(bzla, rhs_leafs, &rhs);

#if 0
  BzlaNode *lhs_c, *rhs_c;
  lhs_c = BZLA_TOP_STACK(lhs);
  rhs_c = BZLA_TOP_STACK(rhs);

  // TODO: subtract lhs_c from rhs_c
  if (lhs_c != zero && rhs_c != zero
      && bzla_node_is_bv_const(lhs_c) && bzla_node_is_bv_const(rhs_c))
  {
    BzlaNode *c = bzla_exp_bv_sub(bzla, lhs_c, rhs_c);
    BZLA_POP_STACK(lhs);
    BZLA_POP_STACK(rhs);

    bzla_node_release(bzla, lhs_c);
    bzla_node_release(bzla, rhs_c);
    BZLA_PUSH_STACK(lhs, c);
  }
#endif

  BzlaNode *add_lhs = bzla_exp_bv_add_n(bzla, lhs.start, BZLA_COUNT_STACK(lhs));
  BzlaNode *add_rhs = bzla_exp_bv_add_n(bzla, rhs.start, BZLA_COUNT_STACK(rhs));
  BzlaNode *result  = bzla_exp_eq(bzla, add_lhs, add_rhs);
  bzla_node_release(bzla, add_rhs);
  bzla_node_release(bzla, add_lhs);

  while (!BZLA_EMPTY_STACK(lhs)) bzla_node_release(bzla, BZLA_POP_STACK(lhs));
  BZLA_RELEASE_STACK(lhs);
  while (!BZLA_EMPTY_STACK(rhs)) bzla_node_release(bzla, BZLA_POP_STACK(rhs));
  BZLA_RELEASE_STACK(rhs);
  bzla_hashptr_table_delete(lhs_leafs);
  bzla_hashptr_table_delete(rhs_leafs);
  return result;
}

void
bzla_normalize_adds(Bzla *bzla)
{
  uint32_t i;
  int32_t id;
  BzlaPtrHashTableIterator it;
  BzlaIntHashTable *cache;
  BzlaNodePtrStack visit;
  BzlaNode *cur, *subst;

  double start = bzla_util_time_stamp();
  bzla_init_substitutions(bzla);

  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(visit, cur);
  }

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    id  = bzla_node_get_id(cur);

    if (bzla_hashint_table_contains(cache, id)) continue;
    bzla_hashint_table_add(cache, id);

    if (bzla_node_is_bv_eq(cur)
        && (bzla_node_is_bv_add(cur->e[0]) || bzla_node_is_bv_add(cur->e[1])))
    {
      subst = normalize_eq_adds(bzla, cur);
      bzla_insert_substitution(bzla, cur, subst, false);
      bzla_node_release(bzla, subst);
    }

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);

  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);

  double delta = bzla_util_time_stamp() - start;
  BZLA_MSG(bzla->msg, 1, "normalized adds in %.3f seconds", delta);
}
