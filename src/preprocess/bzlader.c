/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlader.h"

#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

static bool
occurs(Bzla *bzla,
       BzlaNode *param,
       BzlaNode *term,
       BzlaIntHashTable *deps,
       BzlaIntHashTable *subst_map)
{
  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));

  bool res = false;
  uint32_t i;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *mark, *var_deps;
  BzlaHashTableData *d;
  BzlaNode *cur;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  mark = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, term);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (cur == param)
    {
      res = true;
      break;
    }

    if (!cur->parameterized || bzla_hashint_table_contains(mark, cur->id))
      continue;

    /* be dependency aware when substituting variables */
    if (bzla_node_is_param(cur)
        && ((bzla_node_param_is_forall_var(param)
             && bzla_node_param_is_exists_var(cur))
            || (bzla_node_param_is_exists_var(param)
                && bzla_node_param_is_forall_var(cur))))
    {
      assert(bzla_hashint_map_contains(deps, cur->id));
      var_deps = bzla_hashint_map_get(deps, cur->id)->as_ptr;
      if (bzla_hashint_table_contains(var_deps, param->id))
      {
        res = true;
        break;
      }
    }

    bzla_hashint_table_add(mark, cur->id);
    if ((d = bzla_hashint_map_get(subst_map, cur->id)))
    {
      BZLA_PUSH_STACK(visit, d->as_ptr);
    }
    else
    {
      for (i = 0; i < cur->arity; i++)
      {
        BZLA_PUSH_STACK(visit, cur->e[i]);
      }
    }
  }
  bzla_hashint_table_delete(mark);
  BZLA_RELEASE_STACK(visit);
  return res;
}

static BzlaNode *
find_subst(BzlaIntHashTable *map, BzlaNode *node)
{
  bool inv = false;
  BzlaHashTableData *d;

  goto FIND_SUBST;

  while ((d = bzla_hashint_map_get(map, node->id)))
  {
    node = d->as_ptr;
  FIND_SUBST:
    if (bzla_node_is_inverted(node))
    {
      inv  = !inv;
      node = bzla_node_invert(node);
    }
  }
  return inv ? bzla_node_invert(node) : node;
}

static void
map_subst_node(BzlaIntHashTable *map, BzlaNode *left, BzlaNode *right)
{
  right = find_subst(map, right);
  if (bzla_node_is_inverted(left))
  {
    left  = bzla_node_invert(left);
    right = bzla_node_invert(right);
  }

  assert(bzla_node_is_regular(left));

  // TODO (ma): overwrite subst if substitution is "better"?
  if (bzla_hashint_map_contains(map, left->id))
  {
    return;
  }

  bzla_hashint_map_add(map, left->id)->as_ptr = right;
}

static void
find_substitutions(Bzla *bzla,
                   BzlaNode *root,
                   BzlaIntHashTable *vars,
                   BzlaIntHashTable *subst_map,
                   BzlaIntHashTable *deps,
                   bool elim_evars)
{
  assert(bzla);
  assert(root);
  assert(subst_map);

  BzlaNode *cur, *real_cur, *top_and = 0;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaMemMgr *mm;

  if (!bzla_node_is_bv_and(root)) return;

  if (elim_evars && !bzla_node_is_inverted(root))
    top_and = root;
  else if (!elim_evars && bzla_node_is_inverted(root))
    top_and = bzla_node_real_addr(root);

  if (!top_and) return;

  mm    = bzla->mm;
  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, top_and);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    if (bzla_hashint_table_contains(cache, real_cur->id)) continue;

    bzla_hashint_table_add(cache, real_cur->id);

    if (!bzla_node_is_inverted(cur) && bzla_node_is_bv_and(cur))
    {
      BZLA_PUSH_STACK(visit, cur->e[0]);
      BZLA_PUSH_STACK(visit, cur->e[1]);
    }
#if 0
      else if (!bzla_node_is_inverted (cur) && bzla_node_is_quantifier (cur))
	{
	  BZLA_PUSH_STACK (visit, cur->e[1]);
	}
#endif
    else if (!bzla_node_is_inverted(cur) && bzla_node_is_bv_eq(cur))
    {
      if (bzla_hashint_table_contains(vars, bzla_node_get_id(cur->e[0]))
          && !occurs(bzla, cur->e[0], cur->e[1], deps, subst_map))
        map_subst_node(subst_map, cur->e[0], cur->e[1]);
      else if (bzla_hashint_table_contains(vars, bzla_node_get_id(cur->e[1]))
               && !occurs(bzla, cur->e[1], cur->e[0], deps, subst_map))
        map_subst_node(subst_map, cur->e[1], cur->e[0]);
    }
  }
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
}

static BzlaIntHashTable *
collect_quantifier_block_vars(Bzla *bzla,
                              BzlaNode *block,
                              BzlaIntHashTable *qcache,
                              bool elim_evars)
{
  assert(bzla_node_is_quantifier(block));

  BzlaNode *cur;
  BzlaNodeIterator it;
  BzlaIntHashTable *vars;
  BzlaNodeKind kind;

  kind = elim_evars ? BZLA_EXISTS_NODE : BZLA_FORALL_NODE;
  vars = bzla_hashint_table_new(bzla->mm);

  /* collect all variables in quantifier block 'block' of given kind,
   * DER: kind == BZLA_FORALL_NODE
   * CER: kind == BZLA_EXISTS_NODE
   */
  bzla_iter_binder_init(&it, block);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    assert(bzla_node_is_regular(cur));
    assert(bzla_node_is_quantifier(cur));
    if (cur->kind == kind) bzla_hashint_table_add(vars, cur->e[0]->id);
    bzla_hashint_table_add(qcache, cur->id);
  }
  assert(it.cur == bzla_node_binder_get_body(block));
  return vars;
}

static BzlaIntHashTable *
compute_deps(Bzla *bzla, BzlaNode *root)
{
  uint32_t i;
  BzlaNode *cur, *q;
  BzlaNodePtrStack visit, quants;
  BzlaMemMgr *mm;
  BzlaIntHashTable *mark, *deps, *tmp;
  BzlaHashTableData *d;

  mm   = bzla->mm;
  mark = bzla_hashint_map_new(mm);
  deps = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, quants);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    d   = bzla_hashint_map_get(mark, cur->id);

    if (!d)
    {
      bzla_hashint_map_add(mark, cur->id);

      if (bzla_node_is_quantifier(cur)) BZLA_PUSH_STACK(quants, cur);

      BZLA_PUSH_STACK(visit, cur);
      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
    }
    else if (!d->as_int)
    {
      if (bzla_node_is_quantifier(cur))
      {
        tmp = bzla_hashint_table_new(mm);
        for (i = 0; i < BZLA_COUNT_STACK(quants); i++)
        {
          q = BZLA_PEEK_STACK(quants, i);
          if (q->kind != cur->kind) bzla_hashint_table_add(tmp, q->e[0]->id);
        }
        bzla_hashint_map_add(deps, cur->e[0]->id)->as_ptr = tmp;
        q = BZLA_POP_STACK(quants);
        assert(q == cur);
      }
      d->as_int = 1;
    }
  }
  bzla_hashint_map_delete(mark);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(quants);
  return deps;
}

static BzlaNode *
elim_vars(Bzla *bzla, BzlaNode *root, bool elim_evars)
{
  assert(bzla);
  assert(root);

  uint32_t i, num_quant_vars = 0, num_elim_vars = 0, opt_simp_const;
  BzlaNode *cur, *real_cur, *e[BZLA_NODE_MAX_CHILDREN], *result;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;
  BzlaIntHashTable *mark, *map, *vars, *qcache, *deps;
  BzlaHashTableData *cur_d, *d;

  opt_simp_const = bzla_opt_get(bzla, BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS);
  bzla_opt_set(bzla, BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS, 0);

  mm     = bzla->mm;
  mark   = bzla_hashint_map_new(mm);
  map    = bzla_hashint_map_new(mm);
  qcache = bzla_hashint_table_new(mm);
  deps   = compute_deps(bzla, root);

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    cur_d    = bzla_hashint_map_get(mark, real_cur->id);

    if (!cur_d)
    {
      bzla_hashint_map_add(mark, real_cur->id);

      /* search for var substitutions in current quantifier block */
      if (bzla_node_is_quantifier(real_cur)
          && !bzla_hashint_table_contains(qcache, real_cur->id))
      {
        vars =
            collect_quantifier_block_vars(bzla, real_cur, qcache, elim_evars);
        if (vars->count > 0)
          find_substitutions(bzla,
                             bzla_node_binder_get_body(real_cur),
                             vars,
                             map,
                             deps,
                             elim_evars);
        bzla_hashint_table_delete(vars);
      }

      if ((elim_evars && bzla_node_is_exists(real_cur))
          || (!elim_evars && bzla_node_is_forall(real_cur)))
        num_quant_vars++;

      BZLA_PUSH_STACK(visit, real_cur);
      for (i = 0; i < real_cur->arity; i++)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);

      /* we need to rebuild the substitution first */
      if ((d = bzla_hashint_map_get(map, real_cur->id)))
      {
        BZLA_PUSH_STACK(visit, d->as_ptr);
      }
    }
    else if (!cur_d->as_ptr)
    {
      for (i = 0; i < real_cur->arity; i++)
      {
        e[i] = find_subst(map, real_cur->e[i]);
        assert(e[i]);
        d = bzla_hashint_map_get(mark, bzla_node_real_addr(e[i])->id);
        assert(d);
        assert(d->as_ptr);
        e[i] = bzla_node_cond_invert(e[i], d->as_ptr);
      }
      if (real_cur->arity == 0)
      {
        /* variables in 'map' get substitued */
        if (bzla_hashint_map_contains(map, real_cur->id))
        {
          assert(bzla_node_is_param(real_cur));
          continue;
        }
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
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      /* param of quantifier got substituted */
      else if (bzla_node_is_quantifier(real_cur)
               && bzla_hashint_map_contains(map, real_cur->e[0]->id))
      {
        result = bzla_node_copy(bzla, e[1]);
        num_elim_vars++;
      }
      else
        result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);

      cur_d->as_ptr = result;
    }
  }
  d = bzla_hashint_map_get(mark, bzla_node_real_addr(root)->id);
  assert(d);
  assert(d->as_ptr);
  result = bzla_node_copy(bzla, bzla_node_cond_invert(root, d->as_ptr));
  assert(bzla_node_real_addr(result)->parameterized
         == bzla_node_real_addr(root)->parameterized);

  //  printf ("substituted %u out of %u %s variables\n",
  //	  num_elim_vars, num_quant_vars, elim_evars ? "existential" :
  //"universal");

  for (i = 0; i < mark->size; i++)
  {
    if (!mark->data[i].as_ptr) continue;
    bzla_node_release(bzla, mark->data[i].as_ptr);
  }
  for (i = 0; i < deps->size; i++)
  {
    if (!deps->data[i].as_ptr) continue;
    bzla_hashint_table_delete(deps->data[i].as_ptr);
  }
  bzla_hashint_map_delete(mark);
  bzla_hashint_map_delete(map);
  bzla_hashint_map_delete(deps);
  bzla_hashint_table_delete(qcache);
  BZLA_RELEASE_STACK(visit);
  bzla_opt_set(bzla, BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS, opt_simp_const);
  return result;
}

BzlaNode *
bzla_der_node(Bzla *bzla, BzlaNode *root)
{
  return elim_vars(bzla, root, false);
}

BzlaNode *
bzla_cer_node(Bzla *bzla, BzlaNode *root)
{
  return elim_vars(bzla, root, true);
}
