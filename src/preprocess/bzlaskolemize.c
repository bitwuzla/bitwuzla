/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaskolemize.h"

#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
#include "bzlasubst.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"

BzlaNode *
bzla_skolemize_node(Bzla *bzla,
                    BzlaNode *root,
                    BzlaIntHashTable *node_map,
                    BzlaPtrHashTable *skolem_consts)
{
  int32_t i;
  char *symbol, *buf;
  size_t j, len;
  BzlaNode *cur, *real_cur, *result, *quant, *param, *uf, **e;
  BzlaNodePtrStack visit, quants, args, params;
  BzlaMemMgr *mm;
  BzlaIntHashTable *map;
  BzlaHashTableData *d, *d_p;
  BzlaSortIdStack sorts;
  BzlaSortId tuple_s, fun_s;

  mm  = bzla->mm;
  map = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, params);
  BZLA_INIT_STACK(mm, quants);
  BZLA_INIT_STACK(mm, sorts);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    //      assert (!bzla_node_is_quantifier (real_cur) ||
    //      !bzla_node_is_inverted (cur));

    d = bzla_hashint_map_get(map, real_cur->id);

    if (!d)
    {
      bzla_hashint_map_add(map, real_cur->id);

      if (bzla_node_is_forall(real_cur)) BZLA_PUSH_STACK(quants, cur);

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
        {
          symbol = bzla_node_get_symbol(bzla, real_cur);
          buf    = 0;
          if (bzla_node_param_is_exists_var(real_cur))
          {
            if (symbol)
            {
              len = strlen(symbol) + 5;
              buf = bzla_mem_malloc(mm, len);
              sprintf(buf, "sk(%s)", symbol);
            }

            /* substitute param with skolem function */
            if (BZLA_COUNT_STACK(quants) > 0)
            {
              for (j = 0; j < BZLA_COUNT_STACK(quants); j++)
              {
                quant = BZLA_PEEK_STACK(quants, j);
                d_p   = bzla_hashint_map_get(map, quant->e[0]->id);
                assert(d_p);
                assert(d_p->as_ptr);
                param = d_p->as_ptr;
                BZLA_PUSH_STACK(params, param);
                BZLA_PUSH_STACK(sorts, param->sort_id);
              }

              tuple_s =
                  bzla_sort_tuple(bzla, sorts.start, BZLA_COUNT_STACK(sorts));
              fun_s = bzla_sort_fun(bzla, tuple_s, real_cur->sort_id);
              bzla_sort_release(bzla, tuple_s);

              uf = bzla_exp_uf(bzla, fun_s, buf);
              bzla_sort_release(bzla, fun_s);

              result = bzla_exp_apply_n(
                  bzla, uf, params.start, BZLA_COUNT_STACK(params));

              if (skolem_consts)
                bzla_hashptr_table_add(skolem_consts, bzla_node_copy(bzla, uf));

              bzla_node_release(bzla, uf);
              BZLA_RESET_STACK(sorts);
              BZLA_RESET_STACK(params);
            }
            /* substitute param with variable in outermost scope */
            else
            {
              result = bzla_exp_var(bzla, real_cur->sort_id, buf);
              if (skolem_consts)
                bzla_hashptr_table_add(skolem_consts,
                                       bzla_node_copy(bzla, result));
            }
          }
          else
          {
            if (symbol)
            {
              len = strlen(symbol) + 3;
              buf = bzla_mem_malloc(mm, len);
              sprintf(buf, "%s!0", symbol);
            }
            result = bzla_exp_param(bzla, real_cur->sort_id, buf);
          }

          if (buf) bzla_mem_freestr(mm, buf);
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
      else if (bzla_node_is_exists(real_cur))
      {
        assert(!bzla_node_is_param(e[0]));
        result = bzla_node_copy(bzla, e[1]);
      }
      else
        result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);

      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);
      if (node_map)
      {
        assert(!bzla_hashint_map_contains(node_map, real_cur->id));
        bzla_hashint_map_add(node_map, real_cur->id)->as_int =
            bzla_node_real_addr(result)->id;
      }
    PUSH_RESULT:

      if (bzla_node_is_forall(real_cur))
      {
        quant = BZLA_POP_STACK(quants);
        assert(quant == cur);
      }

      result = bzla_node_cond_invert(cur, result);
      assert(!bzla_node_is_quantifier(result)
             || !bzla_node_is_inverted(result));
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

  for (j = 0; j < map->size; j++)
  {
    if (!map->data[j].as_ptr) continue;
    bzla_node_release(bzla, map->data[j].as_ptr);
  }
  bzla_hashint_map_delete(map);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(quants);
  BZLA_RELEASE_STACK(params);
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(sorts);
  return result;
}

void
bzla_skolemize(Bzla *bzla)
{
  assert(bzla->synthesized_constraints->count == 0);
  assert(bzla->embedded_constraints->count == 0);
  assert(bzla->varsubst_constraints->count == 0);

  char *symbol, *buf;
  size_t i, len;
  BzlaNode *cur, *quant, *param, *uf, *app, *subst;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack visit, quants, args;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaNodeMap *map;
  BzlaSortIdStack sorts;
  BzlaSortId tuple_s, fun_s;
  BzlaNodeMapIterator nit;

  mm    = bzla->mm;
  cache = bzla_hashint_map_new(mm);
  map   = bzla_nodemap_new(bzla);

  BZLA_INIT_STACK(mm, visit);

  /* push roots */
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(visit, cur);
  }

  bzla_init_substitutions(bzla);
  BZLA_INIT_STACK(mm, quants);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, sorts);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    d   = bzla_hashint_map_get(cache, cur->id);

    if (!d)
    {
      (void) bzla_hashint_map_add(cache, cur->id);

      if (bzla_node_is_forall(cur)) BZLA_PUSH_STACK(quants, cur);

      BZLA_PUSH_STACK(visit, cur);
      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;

      if (bzla_node_is_forall(cur))
      {
        quant = BZLA_POP_STACK(quants);
        assert(quant == cur);
      }
      else if (bzla_node_is_exists(cur) && BZLA_COUNT_STACK(quants) > 0)
      {
        param = cur->e[0];
        for (i = 0; i < BZLA_COUNT_STACK(quants); i++)
        {
          quant = BZLA_PEEK_STACK(quants, i);
          BZLA_PUSH_STACK(args, quant->e[0]);
          BZLA_PUSH_STACK(sorts, quant->e[0]->sort_id);
        }

        tuple_s = bzla_sort_tuple(bzla, sorts.start, BZLA_COUNT_STACK(sorts));
        fun_s   = bzla_sort_fun(bzla, tuple_s, param->sort_id);

        symbol = bzla_node_get_symbol(bzla, param);
        //	      printf ("%s\n", symbol);
        if (symbol)
        {
          len = strlen(symbol) + 5;
          buf = bzla_mem_malloc(mm, len);
          sprintf(buf, "sk(%s)", symbol);
        }
        else
          buf = 0;
        uf  = bzla_exp_uf(bzla, fun_s, buf);
        app = bzla_exp_apply_n(bzla, uf, args.start, BZLA_COUNT_STACK(args));
        //	      printf ("%s -> %s\n", node2string (param), node2string
        //(uf));

        bzla_nodemap_map(map, param, app);
        bzla_mem_freestr(mm, buf);
        bzla_sort_release(bzla, tuple_s);
        bzla_sort_release(bzla, fun_s);
        bzla_node_release(bzla, uf);
        BZLA_RESET_STACK(sorts);
        BZLA_RESET_STACK(args);
      }
    }
  }

  bzla_iter_hashptr_init(&it, bzla->quantifiers);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);

    if (bzla_node_is_forall(cur)) continue;

    /* exists quantifier in most outer scope */
    if (!bzla_nodemap_mapped(map, cur->e[0])) continue;

    subst = bzla_substitute_nodes(bzla, bzla_node_binder_get_body(cur), map);
    bzla_nodemap_map(map, cur, subst);
    assert(!bzla_hashptr_table_get(bzla->substitutions, cur));
    bzla_insert_substitution(bzla, cur, subst, 0);
  }

  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);

  bzla_iter_nodemap_init(&nit, map);
  while (bzla_iter_nodemap_has_next(&nit))
  {
    cur = bzla_iter_nodemap_next_data(&nit)->as_ptr;
    bzla_node_release(bzla, cur);
  }

  bzla_nodemap_delete(map);
  bzla_hashint_map_delete(cache);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(quants);
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(sorts);
}
