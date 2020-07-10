/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016-2017 Mathias Preiner.
 *  Copyright (C) 2017-2018 Aina Niemetz.
 *  Copyright (C) 2017 Armin Biere.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include "preprocess/bzlanormquant.h"

#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

static BzlaNode *
create_skolem_ite(Bzla *bzla, BzlaNode *ite, BzlaIntHashTable *map)
{
  assert(bzla_node_is_regular(ite));
  assert(bzla_node_is_bv_cond(ite));

  char buf[128];
  uint32_t i;
  BzlaNodePtrStack params, visit;
  BzlaSortIdStack tsorts;
  BzlaNode *param, *uf, *result, *cur;
  BzlaSortId domain, funsort;
  BzlaMemMgr *mm;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;

  mm   = bzla->mm;
  mark = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, params);
  BZLA_INIT_STACK(mm, tsorts);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, ite);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(mark, cur->id) || !cur->parameterized)
      continue;

    if (bzla_node_is_param(cur))
    {
      d = bzla_hashint_map_get(map, cur->id);
      assert(d);
      assert(d->as_ptr);
      param = d->as_ptr;
      BZLA_PUSH_STACK(params, param);
      BZLA_PUSH_STACK(tsorts, param->sort_id);
    }
    /* param of 'cur' is bound */
    else if (bzla_node_is_quantifier(cur))
      bzla_hashint_table_add(mark, cur->e[0]->id);

    bzla_hashint_table_add(mark, cur->id);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  sprintf(buf, "ite_%d", ite->id);
  if (BZLA_EMPTY_STACK(params))
    result = bzla_exp_var(bzla, ite->sort_id, buf);
  else
  {
    domain  = bzla_sort_tuple(bzla, tsorts.start, BZLA_COUNT_STACK(tsorts));
    funsort = bzla_sort_fun(bzla, domain, ite->sort_id);
    uf      = bzla_exp_uf(bzla, funsort, buf);
    result = bzla_exp_apply_n(bzla, uf, params.start, BZLA_COUNT_STACK(params));
    bzla_sort_release(bzla, domain);
    bzla_sort_release(bzla, funsort);
    bzla_node_release(bzla, uf);
  }

  bzla_hashint_table_delete(mark);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(params);
  BZLA_RELEASE_STACK(tsorts);
  BZLA_MSG(bzla->msg, 1, "create fresh skolem constant %s", buf);
  return result;
}

static BzlaNode *
mk_param_with_symbol(Bzla *bzla, BzlaNode *node)
{
  BzlaMemMgr *mm;
  BzlaNode *result;
  size_t len  = 0;
  int32_t idx = 0;
  char *sym, *buf = 0;

  mm  = bzla->mm;
  sym = bzla_node_get_symbol(bzla, node);
  if (sym)
  {
    len = strlen(sym);
    while (true)
    {
      len += 2 + bzla_util_num_digits(idx);
      BZLA_NEWN(mm, buf, len);
      sprintf(buf, "%s!%d", sym, idx);
      if (bzla_hashptr_table_get(bzla->symbols, buf))
      {
        BZLA_DELETEN(mm, buf, len);
        idx += 1;
      }
      else
        break;
    }
  }
  result = bzla_exp_param(bzla, node->sort_id, buf);
  if (buf) BZLA_DELETEN(mm, buf, len);
  return result;
}

static BzlaNode *
elim_quantified_ite(Bzla *bzla, BzlaNode *roots[], uint32_t num_roots)
{
  int32_t i;
  uint32_t j;
  BzlaNode *cur, *real_cur, *tmp, *result, **e;
  BzlaNode *ite, *ite_if, *ite_else;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit, args, conds;
  BzlaIntHashTable *map;
  BzlaHashTableData *d;

  mm  = bzla->mm;
  map = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, conds);

  for (j = 0; j < num_roots; j++) BZLA_PUSH_STACK(visit, roots[j]);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    d        = bzla_hashint_map_get(map, real_cur->id);

    if (!d)
    {
      /* mark new scope of 'real_cur' */
      if (bzla_node_is_quantifier(real_cur)) BZLA_PUSH_STACK(conds, real_cur);

      bzla_hashint_map_add(map, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert(BZLA_COUNT_STACK(args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
          result = mk_param_with_symbol(bzla, real_cur);
        else
          result = bzla_node_copy(bzla, real_cur);
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      else if (bzla_node_is_bv_cond(real_cur)
               && bzla_node_real_addr(real_cur->e[0])->quantifier_below)
      {
        result = create_skolem_ite(bzla, real_cur, map);

        tmp    = bzla_exp_eq(bzla, result, e[1]);
        ite_if = bzla_exp_implies(bzla, e[0], tmp);
        bzla_node_release(bzla, tmp);

        tmp      = bzla_exp_eq(bzla, result, e[2]);
        ite_else = bzla_exp_implies(bzla, bzla_node_invert(e[0]), tmp);
        bzla_node_release(bzla, tmp);

        ite = bzla_exp_bv_and(bzla, ite_if, ite_else);
        bzla_node_release(bzla, ite_if);
        bzla_node_release(bzla, ite_else);

        BZLA_PUSH_STACK(conds, ite);
      }
      else
      {
        if (bzla_node_is_quantifier(real_cur))
        {
          assert(!BZLA_EMPTY_STACK(conds));
          /* add ite contraints in scope of 'real_cur' to body of
           * quantifier */
          do
          {
            ite = BZLA_POP_STACK(conds);
            if (ite == real_cur) break;
            tmp = bzla_exp_bv_and(bzla, ite, e[1]);
            bzla_node_release(bzla, ite);
            bzla_node_release(bzla, e[1]);
            e[1] = tmp;
          } while (!BZLA_EMPTY_STACK(conds));
        }
        result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);
    PUSH_RESULT:
      result = bzla_node_cond_invert(cur, result);
      BZLA_PUSH_STACK(args, result);
    }
    else
    {
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(args) == num_roots);

  /* add remaining constraints to top level */
  while (!BZLA_EMPTY_STACK(conds))
  {
    tmp = BZLA_POP_STACK(conds);
    assert(!bzla_node_is_quantifier(tmp));
    BZLA_PUSH_STACK(args, tmp);
  }

  result = BZLA_POP_STACK(args);
  while (!BZLA_EMPTY_STACK(args))
  {
    cur = BZLA_POP_STACK(args);
    tmp = bzla_exp_bv_and(bzla, result, cur);
    bzla_node_release(bzla, result);
    bzla_node_release(bzla, cur);
    result = tmp;
  }
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(conds);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    bzla_node_release(bzla, map->data[j].as_ptr);
  }
  bzla_hashint_map_delete(map);
  return result;
}

static int32_t
get_polarity(BzlaNode *n)
{
  return bzla_node_is_inverted(n) ? -1 : 1;
}

static BzlaNode *
fix_quantifier_polarities(Bzla *bzla, BzlaNode *root)
{
  int32_t i, id, cur_pol;
  uint32_t j;
  BzlaNode *cur, *real_cur, *result, **e;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit, args, cleanup;
  BzlaIntHashTable *map;
  BzlaIntStack polarity, reset;
  BzlaHashTableData *d, data;
  BzlaNodeKind kind;

  mm  = bzla->mm;
  map = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, polarity);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, reset);
  BZLA_INIT_STACK(mm, cleanup);

  BZLA_PUSH_STACK(visit, root);
  BZLA_PUSH_STACK(polarity, get_polarity(root));
  while (!BZLA_EMPTY_STACK(visit))
  {
    assert(BZLA_COUNT_STACK(visit) == BZLA_COUNT_STACK(polarity));
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    cur_pol  = BZLA_POP_STACK(polarity);

    /* bv variables have been converted to outermost existential vars in
     * normalize_quantifiers */
    assert(!bzla_node_is_bv_var(real_cur));

    /* polarities are only pushed along the boolean skeleton */
    if (!bzla_node_is_bv_and(real_cur) && !bzla_node_is_quantifier(real_cur)
        && !(bzla_node_is_bv_eq(real_cur) && real_cur->quantifier_below
             && bzla_node_bv_get_width(bzla, real_cur) == 1))
      cur_pol = 1;

    id = real_cur->id * cur_pol;
    d  = bzla_hashint_map_get(map, id);

    if (!d)
    {
      bzla_hashint_map_add(map, id);

      if (bzla_node_is_quantifier(real_cur) && bzla_node_is_inverted(cur)
          && cur_pol == -1)
      {
        BZLA_PUSH_STACK(visit, real_cur);
        BZLA_PUSH_STACK(polarity, cur_pol);
        /* push negation down */
        BZLA_PUSH_STACK(visit, bzla_node_invert(real_cur->e[1]));
        BZLA_PUSH_STACK(polarity,
                        get_polarity(bzla_node_invert(real_cur->e[1])));
        BZLA_PUSH_STACK(visit, real_cur->e[0]);
        BZLA_PUSH_STACK(polarity, 1);
      }
      /* represent boolean equality as with and/not */
      else if (bzla_node_is_bv_eq(real_cur) && real_cur->quantifier_below
               && bzla_node_bv_get_width(bzla, real_cur->e[0]) == 1)
      {
        /* Explicitely disable rewriting here, since we *never* want the
         * created 'iff' to be rewritten to an actual boolean equality.
         * The created node is only used for traversing and getting the
         * polarities right.  With the current set of rewriting rules the
         * generated 'iff' is not rewritten to an equality, however, if
         * additional rules are introduced later we want to make sure that
         * this does not break normalization. */
        unsigned rwl = bzla_opt_get(bzla, BZLA_OPT_REWRITE_LEVEL);
        bzla_opt_set(bzla, BZLA_OPT_REWRITE_LEVEL, 0);
        BzlaNode *i1  = bzla_exp_implies(bzla, real_cur->e[0], real_cur->e[1]);
        BzlaNode *i2  = bzla_exp_implies(bzla, real_cur->e[1], real_cur->e[0]);
        BzlaNode *iff = bzla_exp_bv_and(bzla, i1, i2);
        bzla_node_release(bzla, i1);
        bzla_node_release(bzla, i2);
        iff = bzla_node_cond_invert(cur, iff);
        BZLA_PUSH_STACK(visit, iff);
        BZLA_PUSH_STACK(polarity, cur_pol);
        BZLA_PUSH_STACK(cleanup, iff);
        bzla_opt_set(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);
      }
      else
      {
        BZLA_PUSH_STACK(visit, cur);
        BZLA_PUSH_STACK(polarity, cur_pol);
        for (i = real_cur->arity - 1; i >= 0; i--)
        {
          BZLA_PUSH_STACK(visit, real_cur->e[i]);
          BZLA_PUSH_STACK(polarity, cur_pol * get_polarity(real_cur->e[i]));
        }
      }

      /* push marker for scope of 'real_cur', every parameterized exp
       * under 'real_cur' is in the scope of 'real_cur' */
      if (bzla_node_is_quantifier(real_cur)) BZLA_PUSH_STACK(reset, 0);
    }
    else if (!d->as_ptr)
    {
      assert(BZLA_COUNT_STACK(args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
          result = mk_param_with_symbol(bzla, real_cur);
        else
          result = bzla_node_copy(bzla, real_cur);
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      else
      {
        /* flip quantification */
        if (bzla_node_is_quantifier(real_cur) && cur_pol == -1)
        {
          kind = real_cur->kind == BZLA_FORALL_NODE ? BZLA_EXISTS_NODE
                                                    : BZLA_FORALL_NODE;
        }
        else
          kind = real_cur->kind;

        result = bzla_exp_create(bzla, kind, e, real_cur->arity);
      }

      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);

      if (real_cur->parameterized && real_cur->arity > 0)
        BZLA_PUSH_STACK(reset, id);

      /* scope of 'real_cur' is closed remove all parameterized nodes from
       * cache that are in the scope of 'real_cur'. */
      if (bzla_node_is_quantifier(real_cur))
      {
        while (!BZLA_EMPTY_STACK(reset))
        {
          id = BZLA_POP_STACK(reset);
          /* scope of 'real_cur' closed */
          if (id == 0) break;
          bzla_hashint_map_remove(map, id, &data);
          bzla_node_release(bzla, data.as_ptr);
        }
        /* remove cached param from current quantifier */
        bzla_hashint_map_remove(map, real_cur->e[0]->id, &data);
        bzla_node_release(bzla, data.as_ptr);
      }
    PUSH_RESULT:
      result = bzla_node_cond_invert(cur, result);
      BZLA_PUSH_STACK(args, result);
    }
    else
    {
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_EMPTY_STACK(polarity));
  assert(BZLA_COUNT_STACK(args) == 1);

  result = BZLA_POP_STACK(args);

  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(polarity);
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(reset);

  while (!BZLA_EMPTY_STACK(cleanup))
    bzla_node_release(bzla, BZLA_POP_STACK(cleanup));
  BZLA_RELEASE_STACK(cleanup);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    bzla_node_release(bzla, map->data[j].as_ptr);
  }
  bzla_hashint_map_delete(map);
  return result;
}

static BzlaNode *
collect_existential_vars(Bzla *bzla, BzlaNode *root)
{
  int32_t i, id;
  uint32_t j;
  BzlaNode *cur, *real_cur, *tmp, *result, **e;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit, args, vars;
  BzlaIntHashTable *map;
  BzlaHashTableData *d;

  mm  = bzla->mm;
  map = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, vars);

  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    if (bzla_node_is_quantifier(real_cur))
      id = bzla_node_get_id(cur);
    else
      id = real_cur->id;
    d = bzla_hashint_map_get(map, id);

    if (!d)
    {
      bzla_hashint_map_add(map, id);
      BZLA_PUSH_STACK(visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert(BZLA_COUNT_STACK(args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
          result = mk_param_with_symbol(bzla, real_cur);
        else if (bzla_node_is_bv_var(real_cur))
        {
          result = mk_param_with_symbol(bzla, real_cur);
          BZLA_PUSH_STACK(vars, result);
        }
        else
          result = bzla_node_copy(bzla, real_cur);
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      else
        result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);
    PUSH_RESULT:
      result = bzla_node_cond_invert(cur, result);
      BZLA_PUSH_STACK(args, result);
    }
    else
    {
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(args) == 1);
  result = BZLA_POP_STACK(args);

  /* create outermost existential scope for bv variables */
  while (!BZLA_EMPTY_STACK(vars))
  {
    tmp = bzla_exp_exists(bzla, BZLA_POP_STACK(vars), result);
    bzla_node_release(bzla, result);
    result = tmp;
  }
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(vars);

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    bzla_node_release(bzla, map->data[j].as_ptr);
  }
  bzla_hashint_map_delete(map);

  return result;
}

#ifndef NDEBUG

static bool
check_quantifiers_in_bool_skeleton(Bzla *bzla, BzlaNode *root)
{
  bool res;
  uint32_t i;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;
  BzlaNode *cur;
  BzlaIntHashTable *cache, *all, *found;

  mm    = bzla->mm;
  cache = bzla_hashint_table_new(mm);
  all   = bzla_hashint_table_new(mm);
  found = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;
    bzla_hashint_table_add(cache, cur->id);

    if (bzla_node_is_quantifier(cur)) bzla_hashint_table_add(all, cur->id);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  bzla_hashint_table_delete(cache);
  cache = bzla_hashint_table_new(mm);

  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)
        || bzla_node_bv_get_width(bzla, cur) != 1)
      continue;
    bzla_hashint_table_add(cache, cur->id);

    if (bzla_node_is_quantifier(cur)) bzla_hashint_table_add(found, cur->id);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  res = found->count == all->count;
  bzla_hashint_table_delete(cache);
  bzla_hashint_table_delete(found);
  bzla_hashint_table_delete(all);
  BZLA_RELEASE_STACK(visit);
  return res;
}

#endif

static BzlaNode *
normalize_quantifiers(Bzla *bzla, BzlaNode *roots[], uint32_t num_roots)
{
  assert(bzla);
  assert(roots);

  BzlaNode *root, *root_fixed, *tmp;

  tmp = elim_quantified_ite(bzla, roots, num_roots);
  assert(check_quantifiers_in_bool_skeleton(bzla, tmp));

  root = collect_existential_vars(bzla, tmp);
  bzla_node_release(bzla, tmp);

  /* since we don't have a NNF we have to check the polarities of the
   * quantifiers and flip them if necessary */
  root_fixed = fix_quantifier_polarities(bzla, root);
  bzla_node_release(bzla, root);

  return root_fixed;
}

BzlaNode *
bzla_normalize_quantifiers_node(Bzla *bzla, BzlaNode *root)
{
  assert(bzla);
  assert(root);
  return normalize_quantifiers(bzla, &root, 1);
}

BzlaNode *
bzla_normalize_quantifiers(Bzla *bzla)
{
  assert(bzla->synthesized_constraints->count == 0);
  assert(bzla->embedded_constraints->count == 0);
  assert(bzla->varsubst_constraints->count == 0);

  BzlaNode *result, *root;
  BzlaMemMgr *mm;
  BzlaNodePtrStack roots;
  BzlaPtrHashTableIterator it;

  mm = bzla->mm;

  if (bzla->unsynthesized_constraints->count == 0)
  {
    return bzla_exp_true(bzla);
  }

  BZLA_INIT_STACK(mm, roots);
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    root = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(roots, root);
    bzla_node_real_addr(root)->constraint = 0;
    bzla_hashptr_table_remove(bzla->unsynthesized_constraints, root, 0, 0);
  }

  result = normalize_quantifiers(bzla, roots.start, BZLA_COUNT_STACK(roots));

  while (!BZLA_EMPTY_STACK(roots))
  {
    bzla_node_release(bzla, BZLA_POP_STACK(roots));
  }
  BZLA_RELEASE_STACK(roots);
  return result;
}

#if 0
BzlaNode *
bzla_invert_quantifiers (Bzla * bzla, BzlaNode * root,
			 BzlaIntHashTable * node_map)
{
  size_t j;
  int32_t i;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *result, **e;
  BzlaNodePtrStack stack, args;
  BzlaIntHashTable *map;
  BzlaHashTableData *d;

  mm = bzla->mm;
  map = bzla_hashint_map_new (mm);
  BZLA_INIT_STACK (mm, stack);
  BZLA_INIT_STACK (mm, args);
  BZLA_PUSH_STACK (stack, root);
  while (!BZLA_EMPTY_STACK (stack))
    {
      cur = BZLA_POP_STACK (stack);
      real_cur = bzla_node_real_addr (cur);
      d = bzla_hashint_map_get (map, real_cur->id);

      if (!d)
	{
	  bzla_hashint_table_add (map, real_cur->id);

	  BZLA_PUSH_STACK (stack, cur);
	  for (i = real_cur->arity - 1; i >= 0; i--)
	    BZLA_PUSH_STACK (stack, real_cur->e[i]);
	}
      else if (!d->as_ptr)
	{
	  /* bit vector variables should be existentially quantified */
	  assert (!bzla_node_is_bv_var (real_cur));
	  assert (BZLA_COUNT_STACK (args) >= real_cur->arity);
	  args.top -= real_cur->arity;
	  e = args.top;

	  if (real_cur->arity == 0)
	    {
	      if (bzla_node_is_param (real_cur))
		result = mk_param_with_symbol (bzla, real_cur);
	      else
		result = bzla_node_copy (bzla, real_cur);

	    }
	  else if (bzla_node_is_bv_slice (real_cur))
	    {
	      result = bzla_exp_bv_slice (bzla, e[0],
				       bzla_node_bv_slice_get_upper (real_cur),
				       bzla_node_bv_slice_get_lower (real_cur));
	    }
	  /* invert quantifier nodes */
	  else if (bzla_node_is_quantifier (real_cur))
	    {
	      /* quantifiers are never negated (but flipped) */
	      if (!bzla_node_is_quantifier (e[1]))
		e[1] = bzla_node_invert (e[1]);
	      result =
		bzla_exp_create (bzla,
				 real_cur->kind == BZLA_EXISTS_NODE
				 ? BZLA_FORALL_NODE
				 : BZLA_EXISTS_NODE,
				 e, real_cur->arity);
	    }
	  else
	    result = bzla_exp_create (bzla, real_cur->kind, e, real_cur->arity);

	  d->as_ptr = bzla_node_copy (bzla, result);

	  for (i = 0; i < real_cur->arity; i++)
	    bzla_node_release (bzla, e[i]);

	  if (node_map)
	    {
	      if (!bzla_contains_int_hash_map (node_map, real_cur->id))
		bzla_hashint_map_add (node_map, real_cur->id)->as_int =
		  bzla_node_real_addr (result)->id;
	    }
PUSH_RESULT:
	  /* quantifiers are never negated (but flipped) */
	  if (!bzla_node_is_quantifier (real_cur))
	    result = bzla_node_cond_invert (cur, result);
	  BZLA_PUSH_STACK (args, result);
	}
      else
	{
	  assert (d->as_ptr);
	  result = bzla_node_copy (bzla, d->as_ptr);
	  goto PUSH_RESULT;
	}

    }
  assert (BZLA_COUNT_STACK (args) == 1);
  result = BZLA_POP_STACK (args);

  BZLA_RELEASE_STACK (stack);
  BZLA_RELEASE_STACK (args);

  for (j = 0; j < map->size; j++)
    {
      if (!map->data[j].as_ptr) continue;
      bzla_node_release (bzla, map->data[j].as_ptr);
    }
  bzla_hashint_map_delete (map);

  /* quantifiers are never negated (but flipped) */
  if (!bzla_node_is_quantifier (result))
    result = bzla_node_invert (result);

  return result;
}
#endif
