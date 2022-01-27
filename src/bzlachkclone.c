/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "bzlachkclone.h"

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaopt.h"
#include "bzlaslv.h"
#include "bzlaslvaigprop.h"
#include "bzlaslvfun.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_EXPID(exp, clone)                                     \
  do                                                                        \
  {                                                                         \
    assert(bzla_node_real_addr(exp)->id == bzla_node_real_addr(clone)->id); \
  } while (0)

/*------------------------------------------------------------------------*/

static int32_t
cmp_data_as_int(const BzlaHashTableData *d1, const BzlaHashTableData *d2)
{
  assert(d1);
  assert(d2);

  return d1->as_int - d2->as_int;
}

static int32_t
cmp_data_as_dbl(const BzlaHashTableData *d1, const BzlaHashTableData *d2)
{
  assert(d1);
  assert(d2);

  return d1->as_dbl == d2->as_dbl ? 0 : (d1->as_dbl > d2->as_dbl ? 1 : -1);
}

static int32_t
cmp_data_as_bv_ptr(const BzlaHashTableData *d1, const BzlaHashTableData *d2)
{
  assert(d1);
  assert(d2);

  return bzla_bv_compare(d1->as_ptr, d2->as_ptr);
}

static int32_t
cmp_data_as_sls_constr_data_ptr(const BzlaHashTableData *d1,
                                const BzlaHashTableData *d2)
{
  assert(d1);
  assert(d2);

  BzlaSLSConstrData *scd1, *scd2;

  scd1 = (BzlaSLSConstrData *) d1->as_ptr;
  scd2 = (BzlaSLSConstrData *) d2->as_ptr;
  if (scd1->weight != scd2->weight) return 1;
  if (scd1->selected != scd2->selected) return 1;
  return 0;
}

static inline void
chkclone_int_hash_table(BzlaIntHashTable *table, BzlaIntHashTable *ctable)
{
  size_t i;

  if (!table)
  {
    assert(!ctable);
    return;
  }

  assert(table->size == ctable->size);
  assert(table->count == ctable->count);
  for (i = 0; i < table->size; i++)
  {
    assert(i < ctable->size);
    if (!table->keys[i])
    {
      assert(!ctable->keys[i]);
      continue;
    }
    assert(table->keys[i] == ctable->keys[i]);
  }
  assert(i >= ctable->size);
}

static inline void
chkclone_int_hash_map(BzlaIntHashTable *map,
                      BzlaIntHashTable *cmap,
                      int32_t (*cmp_data)(const BzlaHashTableData *,
                                          const BzlaHashTableData *))
{
  size_t i;

  if (!map)
  {
    assert(!cmap);
    return;
  }

  assert(map->size == cmap->size);
  assert(map->count == cmap->count);
  for (i = 0; i < map->size; i++)
  {
    assert(i < cmap->size);
    if (!map->keys[i])
    {
      assert(!cmap->keys[i]);
      continue;
    }
    assert(map->keys[i] == cmap->keys[i]);
    if (cmp_data) assert(!cmp_data(&map->data[i], &cmap->data[i]));
  }
  assert(i >= cmap->size);
}

static inline void
chkclone_node_ptr_hash_table(BzlaPtrHashTable *table,
                             BzlaPtrHashTable *ctable,
                             int32_t (*cmp_data)(const BzlaHashTableData *,
                                                 const BzlaHashTableData *))
{
  BzlaPtrHashTableIterator it, cit;

  if (!table)
  {
    assert(!ctable);
    return;
  }

  assert(table->size == ctable->size);
  assert(table->count == ctable->count);
  assert(table->hash == ctable->hash);
  assert(table->cmp == ctable->cmp);
  bzla_iter_hashptr_init(&it, table);
  bzla_iter_hashptr_init(&cit, ctable);
  while (bzla_iter_hashptr_has_next(&it))
  {
    assert(bzla_iter_hashptr_has_next(&cit));
    if (cmp_data) assert(!cmp_data(&it.bucket->data, &cit.bucket->data));
    BZLA_CHKCLONE_EXPID(bzla_iter_hashptr_next(&it),
                        bzla_iter_hashptr_next(&cit));
  }
  assert(!bzla_iter_hashptr_has_next(&cit));
}

/*------------------------------------------------------------------------*/

static void
chkclone_mem(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);
  assert(bzla->mm);
  assert(clone->mm);
  assert(bzla->mm->allocated
             - (bzla->msg->prefix
                    ? (strlen(bzla->msg->prefix) + 1) * sizeof(char)
                    : 0)
         == clone->mm->allocated
                - (clone->msg->prefix
                       ? (strlen(clone->msg->prefix) + 1) * sizeof(char)
                       : 0));
  assert(bzla->mm->sat_allocated == clone->mm->sat_allocated);
  /* Note: both maxallocated and sat_maxallocated may differ! */
}

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_STATE(field)       \
  do                                     \
  {                                      \
    assert(clone->field == bzla->field); \
  } while (0)

static void
chkclone_state(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);

  BZLA_CHKCLONE_STATE(rec_rw_calls);
  BZLA_CHKCLONE_STATE(valid_assignments);
  BZLA_CHKCLONE_STATE(vis_idx);
  BZLA_CHKCLONE_STATE(inconsistent);
  BZLA_CHKCLONE_STATE(found_constraint_false);
  BZLA_CHKCLONE_STATE(external_refs);
  BZLA_CHKCLONE_STATE(bzla_sat_bzla_called);
  BZLA_CHKCLONE_STATE(last_sat_result);
}

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_STATS(field)                   \
  do                                                 \
  {                                                  \
    assert(clone->stats.field == bzla->stats.field); \
  } while (0)

#define BZLA_CHKCLONE_CONSTRAINTSTATS(constraints, field)                    \
  do                                                                         \
  {                                                                          \
    assert(clone->stats.constraints.field == bzla->stats.constraints.field); \
  } while (0)

static void
chkclone_stats(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);

#ifndef NDEBUG
  BzlaPtrHashTableIterator it, cit;
  BzlaHashTableData *data, *cdata;
  char *key, *ckey;
#endif

  BZLA_CHKCLONE_STATS(max_rec_rw_calls);
  BZLA_CHKCLONE_STATS(var_substitutions);
  BZLA_CHKCLONE_STATS(uf_substitutions);
  BZLA_CHKCLONE_STATS(ec_substitutions);
  BZLA_CHKCLONE_STATS(linear_equations);
  BZLA_CHKCLONE_STATS(gaussian_eliminations);
  BZLA_CHKCLONE_STATS(eliminated_slices);
  BZLA_CHKCLONE_STATS(skeleton_constraints);
  BZLA_CHKCLONE_STATS(adds_normalized);
  BZLA_CHKCLONE_STATS(ands_normalized);
  BZLA_CHKCLONE_STATS(muls_normalized);
  BZLA_CHKCLONE_STATS(muls_normalized);
  BZLA_CHKCLONE_STATS(ackermann_constraints);
  BZLA_CHKCLONE_STATS(bv_uc_props);
  BZLA_CHKCLONE_STATS(fun_uc_props);
  BZLA_CHKCLONE_STATS(lambdas_merged);
  BZLA_CHKCLONE_STATS(expressions);
  BZLA_CHKCLONE_STATS(clone_calls);
  BZLA_CHKCLONE_STATS(node_bytes_alloc);
  BZLA_CHKCLONE_STATS(beta_reduce_calls);

  BZLA_CHKCLONE_CONSTRAINTSTATS(constraints, varsubst);
  BZLA_CHKCLONE_CONSTRAINTSTATS(constraints, embedded);
  BZLA_CHKCLONE_CONSTRAINTSTATS(constraints, unsynthesized);
  BZLA_CHKCLONE_CONSTRAINTSTATS(constraints, synthesized);
  BZLA_CHKCLONE_CONSTRAINTSTATS(oldconstraints, varsubst);
  BZLA_CHKCLONE_CONSTRAINTSTATS(oldconstraints, embedded);
  BZLA_CHKCLONE_CONSTRAINTSTATS(oldconstraints, unsynthesized);
  BZLA_CHKCLONE_CONSTRAINTSTATS(oldconstraints, synthesized);

#ifndef NDEBUG
  assert(bzla->stats.rw_rules_applied && clone->stats.rw_rules_applied);
  assert(bzla->stats.rw_rules_applied->size
         == clone->stats.rw_rules_applied->size);
  assert(bzla->stats.rw_rules_applied->count
         == clone->stats.rw_rules_applied->count);
  assert(bzla->stats.rw_rules_applied->hash
         == clone->stats.rw_rules_applied->hash);
  assert(bzla->stats.rw_rules_applied->cmp
         == clone->stats.rw_rules_applied->cmp);
  bzla_iter_hashptr_init(&it, bzla->stats.rw_rules_applied);
  bzla_iter_hashptr_init(&cit, clone->stats.rw_rules_applied);
  while (bzla_iter_hashptr_has_next(&it))
  {
    assert(bzla_iter_hashptr_has_next(&cit));
    data  = &it.bucket->data;
    cdata = &cit.bucket->data;
    key   = (char *) bzla_iter_hashptr_next(&it);
    ckey  = (char *) bzla_iter_hashptr_next(&cit);
    assert(!strcmp(key, ckey));
    assert(data->as_int == cdata->as_int);
  }
  assert(!bzla_iter_hashptr_has_next(&cit));
#endif

  BZLA_CHKCLONE_STATS(expressions);
  BZLA_CHKCLONE_STATS(node_bytes_alloc);
  BZLA_CHKCLONE_STATS(beta_reduce_calls);
}

/*------------------------------------------------------------------------*/

static void
chkclone_opts(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);

  BzlaOpt *opt, *copt;
  BzlaOption o;

  assert(bzla->options);
  assert(clone->options);

  for (o = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, o);
       o = bzla_opt_next(bzla, o))
  {
    opt  = &bzla->options[o];
    copt = &clone->options[o];
    assert(opt->expert == copt->expert);
    /* Note: auto_cleanup.val = 1 in clone! */
    if (o != BZLA_OPT_AUTO_CLEANUP && o != BZLA_OPT_AUTO_CLEANUP_INTERNAL)
      assert(opt->val == copt->val);
    assert(opt->dflt == copt->dflt);
    assert(opt->min == copt->min);
    assert(opt->max == copt->max);
    assert(opt->lng && !strcmp(opt->lng, copt->lng));
    assert((!opt->shrt && !copt->shrt)
           || (opt->shrt && !strcmp(opt->shrt, copt->shrt)));
    assert((!opt->desc && !copt->desc)
           || (opt->desc && !strcmp(opt->desc, copt->desc)));
    assert((!opt->valstr && !copt->valstr)
           || (opt->valstr && !strcmp(opt->valstr, copt->valstr)));
  }
}

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_AIG(field)                  \
  do                                              \
  {                                               \
    assert(real_clone->field == real_aig->field); \
  } while (0)

#define BZLA_CHKCLONE_AIGPID(field)                       \
  do                                                      \
  {                                                       \
    if (!real_aig->field)                                 \
    {                                                     \
      assert(!real_clone->field);                         \
      break;                                              \
    }                                                     \
    assert(bzla_aig_is_const(real_aig->field)             \
           || real_aig->field != real_clone->field);      \
    assert(real_aig->field->id == real_clone->field->id); \
  } while (0)

#define BZLA_CHKCLONE_AIGINV(field)                     \
  do                                                    \
  {                                                     \
    if (!real_aig->field)                               \
    {                                                   \
      assert(!real_clone->field);                       \
      break;                                            \
    }                                                   \
    assert(BZLA_IS_INVERTED_AIG(real_aig->field)        \
           == BZLA_IS_INVERTED_AIG(real_clone->field)); \
    BZLA_CHKCLONE_AIGPID(field);                        \
  } while (0)

static void
chkclone_aig(BzlaAIG *aig, BzlaAIG *clone)
{
  int32_t i;
  BzlaAIG *real_aig, *real_clone;

  real_aig   = BZLA_REAL_ADDR_AIG(aig);
  real_clone = BZLA_REAL_ADDR_AIG(clone);
  assert((real_aig == BZLA_AIG_FALSE && real_clone == BZLA_AIG_FALSE)
         || real_aig != real_clone);

  if (real_aig != BZLA_AIG_FALSE)
  {
    BZLA_CHKCLONE_AIG(id);
    BZLA_CHKCLONE_AIG(refs);
    BZLA_CHKCLONE_AIG(next);
    BZLA_CHKCLONE_AIG(cnf_id);
    BZLA_CHKCLONE_AIG(mark);
    BZLA_CHKCLONE_AIG(is_var);
    BZLA_CHKCLONE_AIG(local);
    if (!real_aig->is_var)
      for (i = 0; i < 2; i++) BZLA_CHKCLONE_AIG(children[i]);
  }
}

static inline void
chkclone_aig_unique_table(Bzla *bzla, Bzla *clone)
{
  uint32_t i;
  BzlaAIGUniqueTable *btable, *ctable;

  btable = &bzla_get_aig_mgr(bzla)->table;
  ctable = &bzla_get_aig_mgr(clone)->table;
  assert(btable != ctable);

  assert(btable->size == ctable->size);
  assert(btable->num_elements == ctable->num_elements);

  for (i = 0; i < btable->size; i++)
    assert(btable->chains[i] == ctable->chains[i]);
}

static inline void
chkclone_aig_id_table(Bzla *bzla, Bzla *clone)
{
  uint32_t i;
  BzlaAIGPtrStack *btable, *ctable;

  btable = &bzla_get_aig_mgr(bzla)->id2aig;
  ctable = &bzla_get_aig_mgr(clone)->id2aig;
  assert(btable != ctable);

  for (i = 0; i < BZLA_COUNT_STACK(*btable); i++)
    chkclone_aig(btable->start[i], ctable->start[i]);
}

static inline void
chkclone_aig_cnf_id_table(Bzla *bzla, Bzla *clone)
{
  uint32_t i;
  BzlaIntStack *btable, *ctable;

  btable = &bzla_get_aig_mgr(bzla)->cnfid2aig;
  ctable = &bzla_get_aig_mgr(clone)->cnfid2aig;
  assert(btable != ctable);

  for (i = 0; i < BZLA_SIZE_STACK(*btable); i++)
    assert(btable->start[i] == ctable->start[i]);
}

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_EXP(field)                 \
  do                                             \
  {                                              \
    assert(real_exp->field == real_cexp->field); \
  } while (0)

#define BZLA_CHKCLONE_EXPPTRID(field)                             \
  do                                                              \
  {                                                               \
    if (!real_exp->field)                                         \
    {                                                             \
      assert(!real_cexp->field);                                  \
      break;                                                      \
    }                                                             \
    assert(real_exp->field != real_cexp->field);                  \
    BZLA_CHKCLONE_EXPID(real_exp->field, real_cexp->field);       \
    assert(bzla_node_real_addr(real_exp->field)->bzla == bzla);   \
    assert(bzla_node_real_addr(real_cexp->field)->bzla == clone); \
  } while (0)

#define BZLA_CHKCLONE_EXPPTRINV(field)                  \
  do                                                    \
  {                                                     \
    assert(bzla_node_is_inverted(real_exp->field)       \
           == bzla_node_is_inverted(real_cexp->field)); \
  } while (0)

#define BZLA_CHKCLONE_EXPPTRTAG(field)              \
  do                                                \
  {                                                 \
    assert(bzla_node_get_tag(real_exp->field)       \
           == bzla_node_get_tag(real_cexp->field)); \
  } while (0)

void
bzla_chkclone_exp(Bzla *bzla,
                  Bzla *clone,
                  const BzlaNode *exp,
                  const BzlaNode *cexp)
{
  assert(bzla);
  assert(exp);
  assert(clone);
  assert(cexp);
  assert(bzla != clone);
  assert(exp != cexp);
  assert((!bzla_node_is_inverted(exp) && !bzla_node_is_inverted(cexp))
         || (bzla_node_is_inverted(exp) && bzla_node_is_inverted(cexp)));

  uint32_t i;
  BzlaNode *real_exp, *real_cexp, *e, *ce;
  BzlaPtrHashTableIterator it, cit;

  real_exp  = bzla_node_real_addr(exp);
  real_cexp = bzla_node_real_addr(cexp);
  assert(real_exp != real_cexp);
  assert(cexp);
  assert(real_exp->id == real_cexp->id);
  assert(real_exp->bzla == bzla);
  assert(real_cexp->bzla == clone);

  BZLA_CHKCLONE_EXP(kind);
  BZLA_CHKCLONE_EXP(constraint);
  BZLA_CHKCLONE_EXP(erased);
  BZLA_CHKCLONE_EXP(disconnected);
  BZLA_CHKCLONE_EXP(unique);
  BZLA_CHKCLONE_EXP(bytes);
  BZLA_CHKCLONE_EXP(parameterized);
  BZLA_CHKCLONE_EXP(lambda_below);

  if (bzla_node_is_bv_const(real_exp))
  {
    assert(bzla_bv_get_width(bzla_node_bv_const_get_bits_ptr(real_exp))
           == bzla_bv_get_width(bzla_node_bv_const_get_bits_ptr(real_cexp)));
    assert(bzla_bv_compare(bzla_node_bv_const_get_bits_ptr(real_exp),
                           bzla_node_bv_const_get_bits_ptr(real_cexp))
           == 0);
    if (bzla_node_bv_const_get_invbits_ptr(real_exp))
    {
      assert(
          bzla_bv_get_width(bzla_node_bv_const_get_invbits_ptr(real_exp))
          == bzla_bv_get_width(bzla_node_bv_const_get_invbits_ptr(real_cexp)));
      assert(bzla_bv_compare(bzla_node_bv_const_get_invbits_ptr(real_exp),
                             bzla_node_bv_const_get_invbits_ptr(real_cexp))
             == 0);
    }
  }
  else
  {
    assert((real_exp->av && real_cexp->av)
           || (!real_exp->av && !real_cexp->av));
  }

  BZLA_CHKCLONE_EXP(id);
  BZLA_CHKCLONE_EXP(refs);
  BZLA_CHKCLONE_EXP(ext_refs);
  BZLA_CHKCLONE_EXP(parents);
  BZLA_CHKCLONE_EXP(arity);

  if (!bzla_node_is_fun(real_exp))
  {
    if (real_exp->av)
    {
      assert(real_cexp->av);
      assert(real_exp->av->width == real_cexp->av->width);
      for (i = 0; i < real_exp->av->width; i++)
        chkclone_aig(real_exp->av->aigs[i], real_cexp->av->aigs[i]);
    }
    else
      assert(real_exp->av == real_cexp->av);
  }
  else if (real_exp->rho)
    chkclone_node_ptr_hash_table(real_exp->rho, real_cexp->rho, 0);

  BZLA_CHKCLONE_EXPPTRID(next);
  BZLA_CHKCLONE_EXPPTRID(simplified);
  BZLA_CHKCLONE_EXPPTRID(first_parent);
  BZLA_CHKCLONE_EXPPTRID(last_parent);
  BZLA_CHKCLONE_EXPPTRINV(simplified);
  BZLA_CHKCLONE_EXPPTRTAG(first_parent);
  BZLA_CHKCLONE_EXPPTRTAG(last_parent);

  if (bzla_node_is_proxy(real_exp)) return;

  if (!bzla_node_is_bv_const(real_exp))
  {
    if (!bzla_node_is_var(real_exp) && !bzla_node_is_uf(real_exp)
        && !bzla_node_is_param(real_exp))
    {
      if (real_exp->arity)
      {
        for (i = 0; i < real_exp->arity; i++) BZLA_CHKCLONE_EXPPTRINV(e[i]);
      }
    }

    if (bzla_node_is_bv_slice(real_exp))
    {
      assert(bzla_node_bv_slice_get_upper(real_exp)
             == bzla_node_bv_slice_get_upper(real_cexp));
      assert(bzla_node_bv_slice_get_lower(real_exp)
             == bzla_node_bv_slice_get_lower(real_cexp));
    }

    for (i = 0; i < real_exp->arity; i++)
    {
      BZLA_CHKCLONE_EXPPTRID(prev_parent[i]);
      BZLA_CHKCLONE_EXPPTRID(next_parent[i]);
      BZLA_CHKCLONE_EXPPTRTAG(prev_parent[i]);
      BZLA_CHKCLONE_EXPPTRTAG(next_parent[i]);
    }
  }

#if 0
  if (bzla_node_is_fun (real_exp))
    {
      BZLA_CHKCLONE_EXP (index_len);
      BZLA_CHKCLONE_EXPPTRID (first_aeq_acond_parent);
      BZLA_CHKCLONE_EXPPTRID (last_aeq_acond_parent);
      BZLA_CHKCLONE_EXPPTAG (first_aeq_acond_parent);
      BZLA_CHKCLONE_EXPPTAG (last_aeq_acond_parent);

      if (!BZLA_IS_ARRAY_VAR_NODE (real_exp))
	{
	  for (i = 0; i < real_exp->arity; i++)
	    {
	      BZLA_CHKCLONE_EXPPTRID (prev_aeq_acond_parent[i]);
	      BZLA_CHKCLONE_EXPPTRID (next_aeq_acond_parent[i]);
	      BZLA_CHKCLONE_EXPPTRTAG (prev_aeq_acond_parent[i]);
	      BZLA_CHKCLONE_EXPPTRTAG (next_aeq_acond_parent[i]);
	    }
	}
    }
#endif

  if (bzla_node_is_param(real_exp))
  {
    if (bzla_node_param_is_bound(real_exp))
    {
      assert(bzla_node_param_get_binder(real_exp)
             != bzla_node_param_get_binder(real_cexp));
      BZLA_CHKCLONE_EXPID(bzla_node_param_get_binder(real_exp),
                          bzla_node_param_get_binder(real_cexp));
    }
    else
      assert(!bzla_node_param_is_bound(real_cexp));

    if (((BzlaParamNode *) real_exp)->assigned_exp)
    {
      assert(((BzlaParamNode *) real_exp)->assigned_exp
             != ((BzlaParamNode *) real_cexp)->assigned_exp);
      BZLA_CHKCLONE_EXPID(((BzlaParamNode *) real_exp)->assigned_exp,
                          ((BzlaParamNode *) real_cexp)->assigned_exp);
    }
    else
      assert(!((BzlaParamNode *) real_cexp)->assigned_exp);
  }

  if (bzla_node_is_lambda(real_exp))
  {
    if (bzla_node_lambda_get_static_rho(real_exp))
    {
      bzla_iter_hashptr_init(&it, bzla_node_lambda_get_static_rho(real_exp));
      bzla_iter_hashptr_init(&cit, bzla_node_lambda_get_static_rho(real_cexp));
      while (bzla_iter_hashptr_has_next(&it))
      {
        assert(bzla_iter_hashptr_has_next(&cit));
        e  = bzla_iter_hashptr_next(&it);
        ce = bzla_iter_hashptr_next(&cit);
        if (e)
        {
          assert(ce);
          assert(e != ce);
          BZLA_CHKCLONE_EXPID(e, ce);
        }
        else
          assert(!ce);
      }
      assert(!bzla_iter_hashptr_has_next(&cit));
    }

#if 0
      if (((BzlaLambdaNode *) real_exp)->head)
	{
	  assert (((BzlaLambdaNode *) real_exp)->head
		  != ((BzlaLambdaNode *) real_cexp)->head);
	  BZLA_CHKCLONE_EXPID (((BzlaLambdaNode *) real_exp)->head,
			       ((BzlaLambdaNode *) real_cexp)->head);
	}
      else
	assert (!((BzlaLambdaNode *) real_cexp)->head);
#endif

    if (((BzlaLambdaNode *) real_exp)->body)
    {
      assert(((BzlaLambdaNode *) real_exp)->body
             != ((BzlaLambdaNode *) real_cexp)->body);
      BZLA_CHKCLONE_EXPID(((BzlaLambdaNode *) real_exp)->body,
                          ((BzlaLambdaNode *) real_cexp)->body);
    }
    else
      assert(!((BzlaLambdaNode *) real_cexp)->body);
  }
}

/*------------------------------------------------------------------------*/

static inline void
chkclone_node_ptr_stack(BzlaNodePtrStack *stack, BzlaNodePtrStack *cstack)
{
  uint32_t i;

  assert(BZLA_COUNT_STACK(*stack) == BZLA_COUNT_STACK(*cstack));
  for (i = 0; i < BZLA_COUNT_STACK(*stack); i++)
  {
    if (!BZLA_PEEK_STACK(*stack, i))
    {
      assert(!BZLA_PEEK_STACK(*cstack, i));
      continue;
    }

    BZLA_CHKCLONE_EXPID(BZLA_PEEK_STACK(*stack, i),
                        BZLA_PEEK_STACK(*cstack, i));
  }
}

/*------------------------------------------------------------------------*/

static inline void
chkclone_node_id_table(Bzla *bzla, Bzla *clone)
{
  uint32_t i;
  BzlaNodePtrStack *btable, *ctable;

  btable = &bzla->nodes_id_table;
  ctable = &clone->nodes_id_table;
  assert(btable != ctable);

  assert(BZLA_COUNT_STACK(*btable) == BZLA_COUNT_STACK(*ctable));

  for (i = 0; i < BZLA_COUNT_STACK(*btable); i++)
  {
    if (!BZLA_PEEK_STACK(*btable, i))
    {
      assert(!BZLA_PEEK_STACK(*ctable, i));
      continue;
    }

    bzla_chkclone_exp(
        bzla, clone, BZLA_PEEK_STACK(*btable, i), BZLA_PEEK_STACK(*ctable, i));
  }
}

/*------------------------------------------------------------------------*/

/* Note: no need to check next pointers here as we catch all of them when
 *	 traversing through nodes id table. */
static inline void
chkclone_node_unique_table(Bzla *bzla, Bzla *clone)
{
  uint32_t i;
  BzlaNodeUniqueTable *btable, *ctable;

  btable = &bzla->nodes_unique_table;
  ctable = &clone->nodes_unique_table;
  assert(btable != ctable);
  assert(btable->size == ctable->size);
  assert(btable->num_elements == ctable->num_elements);

  for (i = 0; i < btable->size; i++)
  {
    if (!btable->chains[i])
    {
      assert(!ctable->chains[i]);
      continue;
    }
    BZLA_CHKCLONE_EXPID(btable->chains[i], ctable->chains[i]);
  }
}

/*------------------------------------------------------------------------*/

static void
chkclone_assignment_lists(Bzla *bzla, Bzla *clone)
{
  BzlaBVAss *bvass, *cbvass;
  BzlaFunAss *funass, *cfunass;
  char **ind, **val, **cind, **cval;
  uint32_t i;

  assert(bzla->bv_assignments->count == clone->bv_assignments->count);

  for (bvass = bzla->bv_assignments->first,
      cbvass = clone->bv_assignments->first;
       bvass;
       bvass = bvass->next, cbvass = cbvass->next)
  {
    assert(cbvass);
    assert(!strcmp(bzla_ass_get_bv_str(bvass), bzla_ass_get_bv_str(cbvass)));
  }

  assert(bzla->fun_assignments->count == clone->fun_assignments->count);

  for (funass = bzla->fun_assignments->first,
      cfunass = clone->fun_assignments->first;
       funass;
       funass = funass->next, cfunass = cfunass->next)
  {
    assert(cfunass);
    assert(funass->size == cfunass->size);
    bzla_ass_get_fun_indices_values(funass, &ind, &val, funass->size);
    bzla_ass_get_fun_indices_values(cfunass, &cind, &cval, cfunass->size);
    for (i = 0; i < funass->size; i++)
    {
      assert(!strcmp(ind[i], cind[i]));
      assert(!strcmp(val[i], cval[i]));
    }
  }
}

/*------------------------------------------------------------------------*/

static void
chkclone_tables(Bzla *bzla, Bzla *clone)
{
  BzlaPtrHashTableIterator pit, cpit, npit, cnpit;
  BzlaIntHashTableIterator iit, ciit;
  char *sym, *csym;

  if (!bzla->node2symbol)
    assert(!clone->node2symbol);
  else
  {
    assert(clone->node2symbol);
    assert(bzla->node2symbol->size == clone->node2symbol->size);
    assert(bzla->node2symbol->count == clone->node2symbol->count);
    assert(bzla->node2symbol->hash == clone->node2symbol->hash);
    assert(bzla->node2symbol->cmp == clone->node2symbol->cmp);
    assert(!bzla->node2symbol->first || clone->node2symbol->first);
    bzla_iter_hashptr_init(&pit, bzla->node2symbol);
    bzla_iter_hashptr_init(&cpit, clone->node2symbol);
    while (bzla_iter_hashptr_has_next(&pit))
    {
      assert(bzla_iter_hashptr_has_next(&cpit));
      sym  = pit.bucket->data.as_str;
      csym = cpit.bucket->data.as_str;
      assert(sym != csym);
      assert(!strcmp(sym, csym));
      BZLA_CHKCLONE_EXPID(bzla_iter_hashptr_next(&pit),
                          bzla_iter_hashptr_next(&cpit));
    }
    assert(!bzla_iter_hashptr_has_next(&cpit));
  }

  chkclone_node_ptr_hash_table(bzla->bv_vars, clone->bv_vars, 0);
  chkclone_node_ptr_hash_table(bzla->lambdas, clone->lambdas, 0);
  chkclone_node_ptr_hash_table(bzla->feqs, clone->feqs, 0);
  chkclone_node_ptr_hash_table(bzla->substitutions, clone->substitutions, 0);
  chkclone_node_ptr_hash_table(
      bzla->varsubst_constraints, clone->varsubst_constraints, 0);
  chkclone_node_ptr_hash_table(
      bzla->embedded_constraints, clone->embedded_constraints, 0);
  chkclone_node_ptr_hash_table(
      bzla->unsynthesized_constraints, clone->unsynthesized_constraints, 0);
  chkclone_node_ptr_hash_table(
      bzla->synthesized_constraints, clone->synthesized_constraints, 0);
  chkclone_node_ptr_hash_table(bzla->assumptions, clone->assumptions, 0);

  if (!bzla->parameterized)
    assert(!clone->parameterized);
  else
  {
    assert(clone->parameterized);
    assert(bzla->parameterized->size == clone->parameterized->size);
    assert(bzla->parameterized->count == clone->parameterized->count);
    assert(bzla->parameterized->hash == clone->parameterized->hash);
    assert(bzla->parameterized->cmp == clone->parameterized->cmp);
    assert(!bzla->parameterized->first || clone->parameterized->first);
    bzla_iter_hashptr_init(&pit, bzla->parameterized);
    bzla_iter_hashptr_init(&cpit, clone->parameterized);
    while (bzla_iter_hashptr_has_next(&pit))
    {
      assert(bzla_iter_hashptr_has_next(&cpit));
      chkclone_int_hash_table((BzlaIntHashTable *) pit.bucket->data.as_ptr,
                              (BzlaIntHashTable *) cpit.bucket->data.as_ptr);
      BZLA_CHKCLONE_EXPID(bzla_iter_hashptr_next(&pit),
                          bzla_iter_hashptr_next(&cpit));
    }
    assert(!bzla_iter_hashptr_has_next(&cpit));
  }

  if (!bzla->bv_model)
    assert(!clone->bv_model);
  else
  {
    assert(clone->bv_model);
    assert(bzla->bv_model->size == clone->bv_model->size);
    assert(bzla->bv_model->count == clone->bv_model->count);
    bzla_iter_hashint_init(&iit, bzla->bv_model);
    bzla_iter_hashint_init(&ciit, clone->bv_model);
    while (bzla_iter_hashint_has_next(&iit))
    {
      assert(bzla_iter_hashint_has_next(&ciit));
      assert(bzla->bv_model->data[iit.cur_pos].as_ptr);
      assert(clone->bv_model->data[ciit.cur_pos].as_ptr);
      assert(!bzla_bv_compare(bzla->bv_model->data[iit.cur_pos].as_ptr,
                              clone->bv_model->data[ciit.cur_pos].as_ptr));
      assert(bzla_iter_hashint_next(&iit) == bzla_iter_hashint_next(&ciit));
    }
    assert(!bzla_iter_hashint_has_next(&ciit));
  }

  if (!bzla->fun_model)
    assert(!clone->fun_model);
  else
  {
    assert(clone->fun_model);
    assert(bzla->fun_model->size == clone->fun_model->size);
    assert(bzla->fun_model->count == clone->fun_model->count);
    bzla_iter_hashint_init(&iit, bzla->fun_model);
    bzla_iter_hashint_init(&ciit, clone->fun_model);
    while (bzla_iter_hashint_has_next(&iit))
    {
      assert(bzla_iter_hashint_has_next(&ciit));
      assert(bzla->fun_model->data[iit.cur_pos].as_ptr);
      assert(clone->fun_model->data[ciit.cur_pos].as_ptr);
      bzla_iter_hashptr_init(
          &npit,
          (BzlaPtrHashTable *) bzla->fun_model->data[iit.cur_pos].as_ptr);
      bzla_iter_hashptr_init(
          &cnpit,
          (BzlaPtrHashTable *) clone->fun_model->data[ciit.cur_pos].as_ptr);
      while (bzla_iter_hashptr_has_next(&npit))
      {
        assert(bzla_iter_hashptr_has_next(&cnpit));
        assert(!bzla_bv_compare((BzlaBitVector *) npit.bucket->data.as_ptr,
                                (BzlaBitVector *) cnpit.bucket->data.as_ptr));
        assert(!bzla_bv_compare_tuple((BzlaBitVectorTuple *) npit.cur,
                                      (BzlaBitVectorTuple *) cnpit.cur));
        (void) bzla_iter_hashptr_next(&npit);
        (void) bzla_iter_hashptr_next(&cnpit);
      }
      assert(!bzla_iter_hashptr_has_next(&cnpit));
      assert(bzla_iter_hashint_next(&iit) == bzla_iter_hashint_next(&ciit));
    }
    assert(!bzla_iter_hashint_has_next(&ciit));
  }
}

/*------------------------------------------------------------------------*/

void
bzla_chkclone_sort(Bzla *bzla,
                   Bzla *clone,
                   const BzlaSort *sort,
                   const BzlaSort *csort)
{
  assert(bzla);
  assert(clone);
  assert(bzla != clone);
  assert(sort->id == sort->id);
  assert(sort->kind == sort->kind);
  assert(sort->refs == sort->refs);
  assert(sort->ext_refs == sort->ext_refs);
  assert(sort->parents == sort->parents);
  assert(sort->bzla == bzla);
  assert(csort->bzla == clone);

  uint32_t i;

  switch (sort->kind)
  {
    case BZLA_BV_SORT: assert(sort->bitvec.width == csort->bitvec.width); break;

    case BZLA_ARRAY_SORT:
      assert(sort->array.index->id == csort->array.index->id);
      assert(sort->array.element->id == csort->array.element->id);
      break;

    case BZLA_FUN_SORT:
      assert(sort->fun.arity == csort->fun.arity);
      assert(sort->fun.domain->id == csort->fun.domain->id);
      assert(sort->fun.codomain->id == csort->fun.codomain->id);
      break;

    case BZLA_TUPLE_SORT:
      assert(sort->tuple.num_elements == csort->tuple.num_elements);
      for (i = 0; i < sort->tuple.num_elements; i++)
        assert(sort->tuple.elements[i]->id == csort->tuple.elements[i]->id);
      break;

    case BZLA_LST_SORT:
      assert(sort->lst.head->id == csort->lst.head->id);
      assert(sort->lst.tail->id == csort->lst.tail->id);
      break;

    default: break;
  }
}

/*------------------------------------------------------------------------*/

#define BZLA_CHKCLONE_SLV_STATS(solver, csolver, field)  \
  do                                                     \
  {                                                      \
    assert(csolver->stats.field == solver->stats.field); \
  } while (0)

#define BZLA_CHKCLONE_SLV_STATE(solver, csolver, field) \
  do                                                    \
  {                                                     \
    assert(csolver->field == solver->field);            \
  } while (0)

static void
chkclone_slv(Bzla *bzla, Bzla *clone)
{
  uint32_t i, h;

  h = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);

  assert((!bzla->slv && !clone->slv) || (bzla->slv && clone->slv));
  if (!bzla->slv) return;
  assert(bzla->slv != clone->slv);
  assert(bzla->slv->kind == clone->slv->kind);

  if (bzla->slv->kind == BZLA_FUN_SOLVER_KIND)
  {
    BzlaFunSolver *slv  = BZLA_FUN_SOLVER(bzla);
    BzlaFunSolver *cslv = BZLA_FUN_SOLVER(clone);
    BzlaPtrHashTableIterator it;
    BzlaPtrHashTableIterator cit;

    chkclone_node_ptr_hash_table(slv->lemmas, cslv->lemmas, 0);

    if (slv->score)
    {
      assert(cslv->score);
      assert(slv->score->size == cslv->score->size);
      assert(slv->score->count == cslv->score->count);
      assert(slv->score->hash == cslv->score->hash);
      assert(slv->score->cmp == cslv->score->cmp);
      assert(!slv->score->first || cslv->score->first);
      if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
      {
        bzla_iter_hashptr_init(&it, slv->score);
        bzla_iter_hashptr_init(&cit, cslv->score);
        while (bzla_iter_hashptr_has_next(&it))
        {
          assert(bzla_iter_hashptr_has_next(&cit));
          chkclone_node_ptr_hash_table(
              (BzlaPtrHashTable *) it.bucket->data.as_ptr,
              (BzlaPtrHashTable *) cit.bucket->data.as_ptr,
              0);
          BZLA_CHKCLONE_EXPID(bzla_iter_hashptr_next(&it),
                              bzla_iter_hashptr_next(&cit));
        }
        assert(!bzla_iter_hashptr_has_next(&cit));
      }
      else
      {
        assert(h == BZLA_JUST_HEUR_BRANCH_MIN_DEP);
        chkclone_node_ptr_hash_table(slv->score, cslv->score, cmp_data_as_int);
      }
    }
    else
    {
      assert(!cslv->score);
    }

    assert(BZLA_COUNT_STACK(slv->stats.lemmas_size)
           == BZLA_COUNT_STACK(cslv->stats.lemmas_size));
    for (i = 0; i < BZLA_COUNT_STACK(slv->stats.lemmas_size); i++)
      assert(BZLA_PEEK_STACK(slv->stats.lemmas_size, i)
             == BZLA_PEEK_STACK(cslv->stats.lemmas_size, i));

    BZLA_CHKCLONE_SLV_STATS(slv, cslv, lod_refinements);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, refinement_iterations);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, function_congruence_conflicts);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, beta_reduction_conflicts);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, extensionality_lemmas);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, lemmas_size_sum);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_failed_vars);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_assumed_vars);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_failed_applies);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_assumed_applies);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_failed_eqs);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, dp_assumed_eqs);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, eval_exp_calls);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, propagations);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, propagations_down);
  }
  else if (bzla->slv->kind == BZLA_SLS_SOLVER_KIND)
  {
    BzlaSLSMove *m, *cm;
    BzlaSLSSolver *slv  = BZLA_SLS_SOLVER(bzla);
    BzlaSLSSolver *cslv = BZLA_SLS_SOLVER(clone);

    chkclone_int_hash_map(slv->roots, cslv->roots, cmp_data_as_int);
    chkclone_int_hash_map(
        slv->weights, cslv->weights, cmp_data_as_sls_constr_data_ptr);
    chkclone_int_hash_map(slv->score, cslv->score, cmp_data_as_dbl);

    assert(BZLA_COUNT_STACK(slv->moves) == BZLA_COUNT_STACK(cslv->moves));
    for (i = 0; i < BZLA_COUNT_STACK(slv->moves); i++)
    {
      m = BZLA_PEEK_STACK(slv->moves, i);
      assert(m);
      cm = BZLA_PEEK_STACK(cslv->moves, i);
      assert(cm);
      assert(m->sc == cm->sc);
      chkclone_int_hash_map(m->cans, cm->cans, cmp_data_as_bv_ptr);
    }

    BZLA_CHKCLONE_SLV_STATE(slv, cslv, npropmoves);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, nslsmoves);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, sum_score);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, prop_flip_cond_const_prob);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, prop_flip_cond_const_prob_delta);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, prop_nflip_cond_const);

    chkclone_int_hash_map(slv->max_cans, cslv->max_cans, cmp_data_as_bv_ptr);

    BZLA_CHKCLONE_SLV_STATE(slv, cslv, max_score);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, max_move);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, max_gw);

    BZLA_CHKCLONE_SLV_STATS(slv, cslv, restarts);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, moves);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, flips);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_flip);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_inc);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_dec);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_not);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_range);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_seg);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_rand);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_rand_walk);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_prop);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_prop_rec_conf);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_prop_non_rec_conf);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_flip);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_inc);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_dec);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_not);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_range);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_seg);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_rand);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, move_gw_rand_walk);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, updates);
  }
  else if (bzla->slv->kind == BZLA_PROP_SOLVER_KIND)
  {
    BzlaPropSolver *slv  = BZLA_PROP_SOLVER(bzla);
    BzlaPropSolver *cslv = BZLA_PROP_SOLVER(clone);

    chkclone_int_hash_map(slv->roots, cslv->roots, cmp_data_as_int);
    chkclone_int_hash_map(slv->score, cslv->score, cmp_data_as_dbl);

    BZLA_CHKCLONE_SLV_STATE(slv, cslv, flip_cond_const_prob);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, flip_cond_const_prob_delta);
    BZLA_CHKCLONE_SLV_STATE(slv, cslv, nflip_cond_const);

    BZLA_CHKCLONE_SLV_STATS(slv, cslv, restarts);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, moves);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, rec_conf);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, non_rec_conf);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, props);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, props_inv);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, props_cons);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, updates);
#ifndef NDEBUG
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_add);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_and);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_eq);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_ult);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_sll);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_srl);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_mul);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_udiv);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_urem);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_concat);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, inv_slice);

    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_add);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_and);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_eq);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_ult);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_sll);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_srl);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_mul);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_udiv);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_urem);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_concat);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, cons_slice);
#endif
  }
  else if (bzla->slv->kind == BZLA_AIGPROP_SOLVER_KIND)
  {
    BzlaAIGPropSolver *slv  = BZLA_AIGPROP_SOLVER(bzla);
    BzlaAIGPropSolver *cslv = BZLA_AIGPROP_SOLVER(clone);

    assert(slv->aprop != cslv->aprop);
    assert(slv->aprop->roots == cslv->aprop->roots);

    chkclone_int_hash_map(
        slv->aprop->unsatroots, cslv->aprop->unsatroots, cmp_data_as_int);
    chkclone_int_hash_map(
        slv->aprop->model, cslv->aprop->model, cmp_data_as_int);
    chkclone_int_hash_map(
        slv->aprop->score, cslv->aprop->score, cmp_data_as_dbl);

    BZLA_CHKCLONE_SLV_STATE(slv->aprop, cslv->aprop, loglevel);
    BZLA_CHKCLONE_SLV_STATE(slv->aprop, cslv->aprop, seed);
    BZLA_CHKCLONE_SLV_STATE(slv->aprop, cslv->aprop, use_restarts);
    BZLA_CHKCLONE_SLV_STATE(slv->aprop, cslv->aprop, use_bandit);

    BZLA_CHKCLONE_SLV_STATS(slv, cslv, moves);
    BZLA_CHKCLONE_SLV_STATS(slv, cslv, restarts);
  }
}

/*------------------------------------------------------------------------*/

void
bzla_chkclone(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);
  assert(bzla != clone);

#ifdef BZLA_USE_LINGELING
  if (bzla_opt_get(bzla, BZLA_OPT_SAT_ENGINE) != BZLA_SAT_ENGINE_LINGELING)
    return;
#else
  return;
#endif

  chkclone_mem(bzla, clone);
  chkclone_state(bzla, clone);
  chkclone_stats(bzla, clone);

  chkclone_opts(bzla, clone);

  chkclone_assignment_lists(bzla, clone);

  assert((!bzla->avmgr && !clone->avmgr) || (bzla->avmgr && clone->avmgr));

  if (bzla->avmgr)
  {
    chkclone_aig_unique_table(bzla, clone);
    chkclone_aig_id_table(bzla, clone);
    chkclone_aig_cnf_id_table(bzla, clone);
  }

  chkclone_node_id_table(bzla, clone);
  chkclone_node_unique_table(bzla, clone);

  chkclone_node_ptr_stack(&bzla->functions_with_model,
                          &clone->functions_with_model);

  chkclone_tables(bzla, clone);

  chkclone_slv(bzla, clone);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
