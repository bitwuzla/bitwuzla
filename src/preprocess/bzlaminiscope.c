/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaminiscope.h"

#include "bzlaexp.h"
#include "bzlanode.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

static void
miniscope(Bzla *bzla,
          BzlaNode *quant,
          BzlaIntHashTable *pushed_to,
          BzlaPtrHashTable *rev_pushed_to)
{
  BzlaIntHashTable *cone, *cache;
  BzlaNodeIterator it;
  BzlaNodePtrStack visit, *pushed;
  BzlaNode *cur, *real_cur, *e0, *e1, *cur_parent, *scope, *scope_parent;
  int32_t cur_pol;
  bool e0_cone, e1_cone;
  BzlaPtrHashBucket *b;

  cone  = bzla_hashint_table_new(bzla->mm);
  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);

  /* mark cone of var in order to determine parts of the formula that are
   * not dependent on var */
  BZLA_PUSH_STACK(visit, quant->e[0]);
  bzla_hashint_table_add(cone, quant->id);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cone, cur->id)) continue;

    bzla_hashint_table_add(cone, cur->id);
    bzla_iter_parent_init(&it, cur);
    while (bzla_iter_parent_has_next(&it))
      BZLA_PUSH_STACK(visit, bzla_iter_parent_next(&it));
  }

  cur_pol      = 1;
  cur          = quant->e[1];
  cur_parent   = 0;
  scope_parent = 0;
  scope        = 0;
  while (true)
  {
    real_cur = bzla_node_real_addr(cur);

    if (bzla_hashint_table_contains(cache, real_cur->id)
        || !bzla_sort_is_bool(bzla, real_cur->sort_id))
      continue;

    bzla_hashint_table_add(cache, real_cur->id);

    if (bzla_node_is_bv_and(cur))
    {
      e0      = bzla_node_real_addr(real_cur->e[0]);
      e1      = bzla_node_real_addr(real_cur->e[1]);
      e0_cone = bzla_hashint_table_contains(cone, e0->id);
      e1_cone = bzla_hashint_table_contains(cone, e1->id);
      if (e0_cone && !e1_cone)
      {
        if (bzla_node_is_inverted(cur)) cur_pol *= -1;
        cur          = real_cur->e[0];
        cur_parent   = bzla_node_set_tag(real_cur, 0);
        scope        = cur;
        scope_parent = cur_parent;
        continue;
      }
      else if (!e0_cone && e1_cone)
      {
        if (bzla_node_is_inverted(cur)) cur_pol *= -1;
        cur          = real_cur->e[1];
        cur_parent   = bzla_node_set_tag(real_cur, 1);
        scope        = cur;
        scope_parent = cur_parent;
        continue;
      }
    }
    else if ((bzla_node_is_quantifier(real_cur)
              && bzla_hashint_map_get(pushed_to, real_cur->id))
             || real_cur->kind == quant->kind)
    {
      if (bzla_node_is_inverted(cur)) cur_pol *= -1;
      cur        = real_cur->e[1];
      cur_parent = bzla_node_set_tag(real_cur, 1);
      continue;
    }
    break;
  }

  if (scope)
  {
    assert(scope != bzla_node_binder_get_body(quant));
    assert(cur != bzla_node_binder_get_body(quant));
    /* 'cur_parent' is tagged with the child number, where the new scope
     * of 'quant' begins */
    assert(bzla_node_is_bv_and(scope_parent));

    bzla_hashint_map_add(pushed_to, quant->id)->as_ptr = scope;
    b = bzla_hashptr_table_get(rev_pushed_to, scope_parent);
    if (b)
      pushed = b->data.as_ptr;
    else
    {
      b = bzla_hashptr_table_add(rev_pushed_to, scope_parent);
      BZLA_CNEW(bzla->mm, pushed);
      BZLA_INIT_STACK(bzla->mm, *pushed);
      b->data.as_ptr = pushed;
    }
    quant = (cur_pol == -1) ? bzla_node_invert(quant) : quant;
    BZLA_PUSH_STACK(*pushed, quant);
  }

  bzla_hashint_table_delete(cone);
  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(visit);
}

/* create quantifiers with new scopes */
static BzlaNode *
rebuild_mk_quantifiers(Bzla *bzla,
                       BzlaNodePtrStack *quants,
                       BzlaNode *body,
                       BzlaIntHashTable *map,
                       BzlaIntHashTable *pushed_quants)
{
  uint32_t i;
  BzlaNode *top_q, *q, *result, *tmp;
  BzlaHashTableData *d;

  top_q  = BZLA_PEEK_STACK(*quants, 0);
  result = bzla_node_copy(bzla, body);

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (bzla_node_is_inverted(top_q)) result = bzla_node_invert(result);

  for (i = 0; i < BZLA_COUNT_STACK(*quants); i++)
  {
    q = BZLA_PEEK_STACK(*quants, i);
    assert(bzla_node_is_quantifier(q));

    /* all quantifiers must have the same polarity */
    assert(bzla_node_is_inverted(top_q) == bzla_node_is_inverted(q));
    d = bzla_hashint_map_get(map, bzla_node_real_addr(q)->e[0]->id);
    assert(d);
    assert(d->as_ptr);
    if (bzla_node_is_forall(q))
      tmp = bzla_exp_forall(bzla, d->as_ptr, result);
    else
      tmp = bzla_exp_exists(bzla, d->as_ptr, result);
    bzla_node_release(bzla, result);
    result = tmp;
    bzla_hashint_table_add(pushed_quants, bzla_node_real_addr(q)->id);
  }

  /* we do not have NNF, polarities of quantifiers must not be changed
   * pol=-1, Qx . t[x] -> -(Qx . -t[x])
   * pol=-1, Qx .-t[x] -> -(Qx . t[x])
   */
  if (bzla_node_is_inverted(top_q)) result = bzla_node_invert(result);

  return result;
}

static BzlaNode *
rebuild(Bzla *bzla, BzlaNode *root, BzlaPtrHashTable *pushed)
{
  int32_t i;
  uint32_t j;
  BzlaNode *cur, *real_cur, *result, **e, *tmp;
  BzlaNodePtrStack visit, args, *quants;
  BzlaMemMgr *mm;
  BzlaHashTableData *d;
  BzlaIntHashTable *map, *pushed_quants;
  BzlaPtrHashBucket *b;

  if (pushed->count == 0) return bzla_node_copy(bzla, root);

  mm = bzla->mm;

  map           = bzla_hashint_map_new(mm);
  pushed_quants = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(map, real_cur->id);
    if (!d)
    {
      bzla_hashint_map_add(map, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (d->as_ptr == 0)
    {
      assert(BZLA_COUNT_STACK(args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      for (j = 0; j < 2; j++)
      {
        if ((b = bzla_hashptr_table_get(pushed,
                                        bzla_node_set_tag(real_cur, j))))
        {
          assert(bzla_node_is_bv_and(real_cur));
          quants = b->data.as_ptr;
          assert(!BZLA_EMPTY_STACK(*quants));
          tmp = rebuild_mk_quantifiers(bzla, quants, e[j], map, pushed_quants);
          bzla_node_release(bzla, e[j]);
          e[j] = tmp;
          BZLA_RELEASE_STACK(*quants);
          BZLA_DELETE(mm, quants);
        }
      }

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
        {
          result = bzla_node_create_param(
              bzla, real_cur->sort_id, bzla_node_get_symbol(bzla, real_cur));
        }
        else
        {
          result = bzla_node_copy(bzla, real_cur);
        }
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      /* scope of quantifier changed */
      else if (bzla_node_is_quantifier(real_cur)
               && bzla_hashint_table_contains(pushed_quants, real_cur->id))
      {
        result = bzla_node_copy(bzla, e[1]);
      }
      else
      {
        result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);
    PUSH_RESULT:
      BZLA_PUSH_STACK(args, bzla_node_cond_invert(cur, result));
    }
    else
    {
      result = bzla_node_copy(bzla, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(args) == 1);
  result = BZLA_POP_STACK(args);

  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(args);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    bzla_node_release(bzla, map->data[j].as_ptr);
  }
  bzla_hashint_map_delete(map);
  bzla_hashint_table_delete(pushed_quants);
  return result;
}

BzlaNode *
bzla_miniscope_node(Bzla *bzla, BzlaNode *root)
{
  uint32_t i;
  BzlaNode *cur, *result;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache, *pushed_to;
  BzlaPtrHashTable *rev_pushed_to;
  BzlaHashTableData *d;

  if (bzla->quantifiers->count == 0) return bzla_node_copy(bzla, root);

  mm            = bzla->mm;
  cache         = bzla_hashint_map_new(mm);
  pushed_to     = bzla_hashint_map_new(mm);
  rev_pushed_to = bzla_hashptr_table_new(mm, 0, 0);

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    d = bzla_hashint_map_get(cache, cur->id);
    if (!d)
    {
      bzla_hashint_map_add(cache, cur->id);
      BZLA_PUSH_STACK(visit, cur);
      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (bzla_node_is_quantifier(cur))
      {
        miniscope(bzla, cur, pushed_to, rev_pushed_to);
      }
    }
  }

  result = rebuild(bzla, root, rev_pushed_to);

  bzla_hashint_map_delete(cache);
  bzla_hashint_map_delete(pushed_to);
  bzla_hashptr_table_delete(rev_pushed_to);
  BZLA_RELEASE_STACK(visit);
  assert(!bzla_node_real_addr(result)->parameterized);
  return result;
}
