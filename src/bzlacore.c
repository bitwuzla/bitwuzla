/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlacore.h"

#include <limits.h>

#ifndef NDEBUG
#include "bzlachkfailed.h"
#include "bzlachkmodel.h"
#endif
#include "bzlaclone.h"
#include "bzlaconfig.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlaopt.h"
#include "bzlarewrite.h"
#include "bzlaslvaigprop.h"
#include "bzlaslvfun.h"
#include "bzlaslvprop.h"
#include "bzlaslvquant.h"
#include "bzlaslvsls.h"
#include "bzlasubst.h"
#include "preprocess/bzlapreprocess.h"
#include "preprocess/bzlavarsubst.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_INIT_UNIQUE_TABLE(mm, table) \
  do                                      \
  {                                       \
    assert(mm);                           \
    (table).size         = 1;             \
    (table).num_elements = 0;             \
    BZLA_CNEW(mm, (table).chains);        \
  } while (0)

#define BZLA_RELEASE_UNIQUE_TABLE(mm, table)        \
  do                                                \
  {                                                 \
    assert(mm);                                     \
    BZLA_DELETEN(mm, (table).chains, (table).size); \
  } while (0)

#define BZLA_INIT_SORT_UNIQUE_TABLE(mm, table) \
  do                                           \
  {                                            \
    BZLA_INIT_UNIQUE_TABLE(mm, table);         \
    table.mm = mm;                             \
    BZLA_INIT_STACK(mm, table.id2sort);        \
    BZLA_PUSH_STACK(table.id2sort, 0);         \
  } while (0)

#define BZLA_RELEASE_SORT_UNIQUE_TABLE(mm, table) \
  do                                              \
  {                                               \
    BZLA_RELEASE_UNIQUE_TABLE(mm, table);         \
    BZLA_RELEASE_STACK(table.id2sort);            \
  } while (0)

#define BZLA_COND_INVERT_AIG_NODE(exp, aig) \
  ((BzlaAIG *) (((uint32_t long int) (exp) &1ul) ^ ((uint32_t long int) (aig))))

#define BZLA_AIGVEC_NODE(bzla, exp)                                   \
  (bzla_node_is_inverted(exp)                                         \
       ? bzla_aigvec_not((bzla)->avmgr, bzla_node_real_addr(exp)->av) \
       : bzla_aigvec_copy((bzla)->avmgr, exp->av))

/*------------------------------------------------------------------------*/

static BzlaAIG *exp_to_aig(Bzla *, BzlaNode *);

/*------------------------------------------------------------------------*/

enum BzlaSubstCompKind
{
  BZLA_SUBST_COMP_ULT_KIND,
  BZLA_SUBST_COMP_ULTE_KIND,
  BZLA_SUBST_COMP_UGT_KIND,
  BZLA_SUBST_COMP_UGTE_KIND
};

typedef enum BzlaSubstCompKind BzlaSubstCompKind;

/*------------------------------------------------------------------------*/

void
bzla_init_substitutions(Bzla *bzla)
{
  assert(bzla);
  assert(!bzla->substitutions);

  bzla->substitutions =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
}

void
bzla_delete_substitutions(Bzla *bzla)
{
  assert(bzla);

  if (!bzla->substitutions) return;

  BzlaNode *cur;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, bzla->substitutions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, (BzlaNode *) it.bucket->data.as_ptr);
    cur = bzla_iter_hashptr_next(&it);
    bzla_node_release(bzla, cur);
  }

  bzla_hashptr_table_delete(bzla->substitutions);
  bzla->substitutions = 0;
}

BzlaNode *
bzla_find_substitution(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  BzlaNode *result = 0;
  BzlaPtrHashBucket *b;

  if (!bzla->substitutions) return 0;

  while (1)
  {
    b = bzla_hashptr_table_get(bzla->substitutions, bzla_node_real_addr(exp));
    if (!b) break;
    result = bzla_node_cond_invert(exp, (BzlaNode *) b->data.as_ptr);
    exp    = result;
  }

  return result;
}

#ifndef NDEBUG
static bool
substitution_cycle_check_dbg(Bzla *bzla, BzlaNode *exp, BzlaNode *subst)
{
  uint32_t i;
  bool iscycle = false;
  BzlaMemMgr *mm;
  BzlaNode *cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;

  mm    = bzla->mm;
  exp   = bzla_node_real_addr(exp);
  cache = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, subst);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;

    if (cur == exp)
    {
      iscycle = true;
      break;
    }

    bzla_hashint_table_add(cache, cur->id);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
  return !iscycle;
}
#endif

void
bzla_insert_substitution(Bzla *bzla,
                         BzlaNode *exp,
                         BzlaNode *subst,
                         bool update)
{
  assert(bzla);
  assert(exp);
  assert(subst);
  assert(bzla->substitutions);
  assert(bzla_node_get_sort_id(exp) == bzla_node_get_sort_id(subst));
  assert(!bzla_node_is_simplified(exp));

  BzlaNode *simp;
  BzlaPtrHashBucket *b;
  exp = bzla_node_real_addr(exp);

  if (exp == bzla_node_real_addr(subst)) return;

  assert(substitution_cycle_check_dbg(bzla, exp, subst));

  b = bzla_hashptr_table_get(bzla->substitutions, exp);
  if (update && b)
  {
    assert(b->data.as_ptr);
    /* release data of current bucket */
    bzla_node_release(bzla, (BzlaNode *) b->data.as_ptr);
    bzla_hashptr_table_remove(bzla->substitutions, exp, 0, 0);
    /* release key of current bucket */
    bzla_node_release(bzla, exp);
  }
  else if (b)
  {
    assert((BzlaNode *) b->data.as_ptr == subst);
    /* substitution already inserted */
    return;
  }

  simp = bzla_find_substitution(bzla, subst);

  if (simp) subst = simp;

  assert(
      !bzla_hashptr_table_get(bzla->substitutions, bzla_node_real_addr(subst)));

  if (exp == bzla_node_real_addr(subst)) return;

  bzla_hashptr_table_add(bzla->substitutions, bzla_node_copy(bzla, exp))
      ->data.as_ptr = bzla_node_copy(bzla, subst);
}

/*------------------------------------------------------------------------*/

const char *
bzla_version(const Bzla *bzla)
{
  assert(bzla);
  (void) bzla;
  return BZLA_VERSION;
}

const char *
bzla_git_id(const Bzla *bzla)
{
  assert(bzla);
  (void) bzla;
  return BZLA_GIT_ID;
}

BzlaAIGMgr *
bzla_get_aig_mgr(const Bzla *bzla)
{
  assert(bzla);
  return bzla_aigvec_get_aig_mgr(bzla->avmgr);
}

BzlaSATMgr *
bzla_get_sat_mgr(const Bzla *bzla)
{
  assert(bzla);
  return bzla_aig_get_sat_mgr(bzla_get_aig_mgr(bzla));
}

void
bzla_reset_time(Bzla *bzla)
{
  assert(bzla);
  BZLA_CLR(&bzla->time);
}

void
bzla_reset_stats(Bzla *bzla)
{
  assert(bzla);
#ifndef NDEBUG
  if (bzla->stats.rw_rules_applied)
    bzla_hashptr_table_delete(bzla->stats.rw_rules_applied);
#endif
  BZLA_CLR(&bzla->stats);
#ifndef NDEBUG
  assert(!bzla->stats.rw_rules_applied);
  bzla->stats.rw_rules_applied = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmp);
#endif
}

static uint32_t
constraints_stats_changes(Bzla *bzla)
{
  uint32_t res;

  if (bzla->stats.oldconstraints.varsubst && !bzla->varsubst_constraints->count)
    return UINT32_MAX;

  if (bzla->stats.oldconstraints.embedded && !bzla->embedded_constraints->count)
    return UINT32_MAX;

  if (bzla->stats.oldconstraints.unsynthesized
      && !bzla->unsynthesized_constraints->count)
    return UINT32_MAX;

  res = bzla->stats.oldconstraints.varsubst >= bzla->varsubst_constraints->count
            ? bzla->stats.oldconstraints.varsubst
                  - bzla->varsubst_constraints->count
            : bzla->varsubst_constraints->count
                  - bzla->stats.oldconstraints.varsubst;
  res +=
      bzla->stats.oldconstraints.embedded >= bzla->embedded_constraints->count
          ? bzla->stats.oldconstraints.embedded
                - bzla->embedded_constraints->count
          : bzla->embedded_constraints->count
                - bzla->stats.oldconstraints.embedded;
  res += bzla->stats.oldconstraints.unsynthesized
                 >= bzla->unsynthesized_constraints->count
             ? bzla->stats.oldconstraints.unsynthesized
                   - bzla->unsynthesized_constraints->count
             : bzla->unsynthesized_constraints->count
                   - bzla->stats.oldconstraints.unsynthesized;
  res += bzla->stats.oldconstraints.synthesized
                 >= bzla->synthesized_constraints->count
             ? bzla->stats.oldconstraints.synthesized
                   - bzla->synthesized_constraints->count
             : bzla->synthesized_constraints->count
                   - bzla->stats.oldconstraints.synthesized;

  return res;
}

static void
report_constraint_stats(Bzla *bzla, bool force)
{
  uint32_t changes;

  if (!force)
  {
    if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) <= 0) return;

    changes = constraints_stats_changes(bzla);

    if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) == 1 && changes < 100000) return;

    if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) == 2 && changes < 1000) return;

    if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) == 3 && changes < 10) return;

    if (!changes) return;
  }

  BZLA_MSG(bzla->msg,
           1,
           "%d/%d/%d/%d constraints %d/%d/%d/%d %.1f MB",
           bzla->stats.constraints.varsubst,
           bzla->stats.constraints.embedded,
           bzla->stats.constraints.unsynthesized,
           bzla->stats.constraints.synthesized,
           bzla->varsubst_constraints->count,
           bzla->embedded_constraints->count,
           bzla->unsynthesized_constraints->count,
           bzla->synthesized_constraints->count,
           bzla->mm->allocated / (double) (1 << 20));

  bzla->stats.oldconstraints.varsubst = bzla->varsubst_constraints->count;
  bzla->stats.oldconstraints.embedded = bzla->embedded_constraints->count;
  bzla->stats.oldconstraints.unsynthesized =
      bzla->unsynthesized_constraints->count;
  bzla->stats.oldconstraints.synthesized = bzla->synthesized_constraints->count;
}

/* we do not count proxies */
static uint32_t
number_of_ops(Bzla *bzla)
{
  int32_t i, result;
  assert(bzla);

  result = 0;
  for (i = 1; i < BZLA_NUM_OPS_NODE - 1; i++) result += bzla->ops[i].cur;

  return result;
}

#ifdef BZLA_TIME_STATISTICS
static double
percent(double a, double b)
{
  return b ? 100.0 * a / b : 0.0;
}
#endif

void
bzla_print_stats(Bzla *bzla)
{
  uint32_t i, num_final_ops;
  uint32_t verbosity;

  if (!bzla) return;

  verbosity = bzla_opt_get(bzla, BZLA_OPT_VERBOSITY);

  report_constraint_stats(bzla, true);

  BZLA_MSG(bzla->msg, 1, "%u assumptions", bzla->assumptions->count);

  if (verbosity > 0)
  {
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg, 2, "%5d max rec. RW", bzla->stats.max_rec_rw_calls);
    BZLA_MSG(bzla->msg,
             2,
             "%5lld number of expressions ever created",
             bzla->stats.expressions);
    num_final_ops = number_of_ops(bzla);
    BZLA_MSG(bzla->msg, 2, "%5d number of final expressions", num_final_ops);
    assert(sizeof g_bzla_op2str / sizeof *g_bzla_op2str == BZLA_NUM_OPS_NODE);

    BZLA_MSG(bzla->msg,
             1,
             "%.2f MB allocated for nodes",
             bzla->stats.node_bytes_alloc / (double) (1 << 20));
    if (num_final_ops > 0)
      for (i = 1; i < BZLA_NUM_OPS_NODE - 1; i++)
        if (bzla->ops[i].cur || bzla->ops[i].max)
          BZLA_MSG(bzla->msg,
                   2,
                   " %s: %d max %d",
                   g_bzla_op2str[i],
                   bzla->ops[i].cur,
                   bzla->ops[i].max);
    BZLA_MSG(bzla->msg, 1, "");
  }

  if (bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION))
  {
    BZLA_MSG(
        bzla->msg, 1, "%5d unconstrained bv props", bzla->stats.bv_uc_props);
    BZLA_MSG(bzla->msg,
             1,
             "%5d unconstrained array props",
             bzla->stats.fun_uc_props);
    BZLA_MSG(bzla->msg,
             1,
             "%5d unconstrained parameterized props",
             bzla->stats.param_uc_props);
  }
  BZLA_MSG(bzla->msg,
           1,
           "%5d variable substitutions",
           bzla->stats.var_substitutions);
  BZLA_MSG(bzla->msg,
           1,
           "%5d uninterpreted function substitutions",
           bzla->stats.uf_substitutions);
  BZLA_MSG(bzla->msg,
           1,
           "%5d embedded constraint substitutions",
           bzla->stats.ec_substitutions);
  BZLA_MSG(bzla->msg,
           1,
           "%5d synthesized nodes rewritten",
           bzla->stats.rewrite_synth);

  BZLA_MSG(bzla->msg,
           1,
           "%5d linear constraint equations",
           bzla->stats.linear_equations);
  BZLA_MSG(bzla->msg,
           1,
           "%5d gaussian eliminations in linear equations",
           bzla->stats.gaussian_eliminations);
  BZLA_MSG(bzla->msg,
           1,
           "%5d eliminated sliced variables",
           bzla->stats.eliminated_slices);
  BZLA_MSG(bzla->msg,
           1,
           "%5d extracted skeleton constraints",
           bzla->stats.skeleton_constraints);
  BZLA_MSG(bzla->msg, 1, "%5d and normalizations", bzla->stats.ands_normalized);
  BZLA_MSG(bzla->msg, 1, "%5d add normalizations", bzla->stats.adds_normalized);
  BZLA_MSG(bzla->msg, 1, "%5d mul normalizations", bzla->stats.muls_normalized);
  BZLA_MSG(bzla->msg, 1, "%5lld lambdas merged", bzla->stats.lambdas_merged);
  BZLA_MSG(bzla->msg,
           1,
           "%5d static apply propagations over lambdas",
           bzla->stats.prop_apply_lambda);
  BZLA_MSG(bzla->msg,
           1,
           "%5d static apply propagations over updates",
           bzla->stats.prop_apply_update);
  BZLA_MSG(
      bzla->msg, 1, "%5lld beta reductions", bzla->stats.beta_reduce_calls);
  BZLA_MSG(bzla->msg, 1, "%5lld clone calls", bzla->stats.clone_calls);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "rewrite rule cache");
  BZLA_MSG(bzla->msg, 1, "  %lld cached (add) ", bzla->rw_cache->num_add);
  BZLA_MSG(bzla->msg, 1, "  %lld cached (get)", bzla->rw_cache->num_get);
  BZLA_MSG(bzla->msg, 1, "  %lld updated", bzla->rw_cache->num_update);
  BZLA_MSG(bzla->msg, 1, "  %lld removed (gc)", bzla->rw_cache->num_remove);
  BZLA_MSG(bzla->msg,
           1,
           "  %.2f MB cache",
           (bzla->rw_cache->cache->count * sizeof(BzlaRwCacheTuple)
            + bzla->rw_cache->cache->count * sizeof(BzlaPtrHashBucket)
            + bzla->rw_cache->cache->size * sizeof(BzlaPtrHashBucket *))
               / (double) (1 << 20));

#ifndef NDEBUG
  BzlaPtrHashTableIterator it;
  char *rule;
  int32_t num = 0;
  BZLA_MSG(bzla->msg, 1, "applied rewriting rules:");
  if (bzla->stats.rw_rules_applied->count == 0)
    BZLA_MSG(bzla->msg, 1, "  none");
  else
  {
    bzla_iter_hashptr_init(&it, bzla->stats.rw_rules_applied);
    while (bzla_iter_hashptr_has_next(&it))
    {
      num  = it.bucket->data.as_int;
      rule = bzla_iter_hashptr_next(&it);
      BZLA_MSG(bzla->msg, 1, "  %5d %s", num, rule);
    }
  }
#endif

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "bit blasting statistics:");
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld AIG vectors (%lld max)",
           bzla->avmgr ? bzla->avmgr->cur_num_aigvecs : 0,
           bzla->avmgr ? bzla->avmgr->max_num_aigvecs : 0);
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld AIG ANDs (%lld max)",
           bzla->avmgr ? bzla->avmgr->amgr->cur_num_aigs : 0,
           bzla->avmgr ? bzla->avmgr->amgr->max_num_aigs : 0);
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld AIG variables",
           bzla->avmgr ? bzla->avmgr->amgr->max_num_aig_vars : 0);
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld CNF variables",
           bzla->avmgr ? bzla->avmgr->amgr->num_cnf_vars : 0);
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld CNF clauses",
           bzla->avmgr ? bzla->avmgr->amgr->num_cnf_clauses : 0);
  BZLA_MSG(bzla->msg,
           1,
           "  %7lld CNF literals",
           bzla->avmgr ? bzla->avmgr->amgr->num_cnf_literals : 0);

  if (bzla->slv) bzla->slv->api.print_stats(bzla->slv);
  if (bzla->qslv) bzla->qslv->api.print_stats(bzla->qslv);

#ifdef BZLA_TIME_STATISTICS
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "%.3f seconds beta-reduction", bzla->time.beta);
  BZLA_MSG(bzla->msg,
           1,
           "%.3f seconds synthesize expressions",
           bzla->time.synth_exp);
  BZLA_MSG(bzla->msg,
           1,
           "%.3f seconds determining failed assumptions",
           bzla->time.failed);
  BZLA_MSG(bzla->msg, 1, "%.3f seconds cloning", bzla->time.cloning);
  BZLA_MSG(bzla->msg,
           1,
           "%.3f seconds substitute and rebuild",
           bzla->time.subst_rebuild);
  if (bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS))
    BZLA_MSG(
        bzla->msg, 1, "%.3f seconds model generation", bzla->time.model_gen);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "%.3f seconds solving", bzla->time.sat);
  BZLA_MSG(
      bzla->msg, 1, "  %.3f seconds rewriting engine", bzla->time.simplify);
  BZLA_MSG(bzla->msg,
           1,
           "    %.3f seconds variable substitution (%.0f%%)",
           bzla->time.subst,
           percent(bzla->time.subst, bzla->time.simplify));
  BZLA_MSG(bzla->msg, 1, "    %.3f seconds rewriting", bzla->time.rewrite);
  BZLA_MSG(
      bzla->msg, 1, "    %.3f seconds occurrence check", bzla->time.occurrence);

  BZLA_MSG(bzla->msg,
           1,
           "    %.3f seconds embedded substitution (%.0f%%)",
           bzla->time.embedded,
           percent(bzla->time.embedded, bzla->time.simplify));

  if (bzla_opt_get(bzla, BZLA_OPT_PP_ELIMINATE_EXTRACTS))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds variable slicing (%.0f%%)",
             bzla->time.slicing,
             percent(bzla->time.slicing, bzla->time.simplify));

#ifndef BZLA_DO_NOT_PROCESS_SKELETON
  BZLA_MSG(bzla->msg,
           1,
           "    %.3f seconds skeleton preprocessing (%.0f%%)",
           bzla->time.skel,
           percent(bzla->time.skel, bzla->time.simplify));
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds unconstrained optimization",
             bzla->time.ucopt);

  if (bzla_opt_get(bzla, BZLA_OPT_PP_EXTRACT_LAMBDAS))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds lambda extraction (%.0f%%)",
             bzla->time.extract,
             percent(bzla->time.extract, bzla->time.simplify));

  if (bzla_opt_get(bzla, BZLA_OPT_PP_MERGE_LAMBDAS))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds lambda merging (%.0f%%)",
             bzla->time.merge,
             percent(bzla->time.merge, bzla->time.simplify));

  if (bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds apply elimination (%.0f%%)",
             bzla->time.elimapplies,
             percent(bzla->time.elimapplies, bzla->time.simplify));

  if (bzla_opt_get(bzla, BZLA_OPT_PP_ACKERMANN))
    BZLA_MSG(bzla->msg,
             1,
             "    %.3f seconds ackermann constraints (%.0f%%)",
             bzla->time.ack,
             percent(bzla->time.ack, bzla->time.simplify));

  if (bzla->slv) bzla->slv->api.print_time_stats(bzla->slv);
  if (bzla->qslv) bzla->qslv->api.print_time_stats(bzla->qslv);
#endif

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(
      bzla->msg, 1, "%.1f MB", bzla->mm->maxallocated / (double) (1 << 20));
}

Bzla *
bzla_new(void)
{
  BzlaMemMgr *mm;
  Bzla *bzla;

  mm = bzla_mem_mgr_new();
  BZLA_CNEW(mm, bzla);

  bzla->mm  = mm;
  bzla->msg = bzla_msg_new(bzla);
  bzla_set_msg_prefix(bzla, "bitwuzla");

  BZLA_INIT_UNIQUE_TABLE(mm, bzla->nodes_unique_table);
  BZLA_INIT_SORT_UNIQUE_TABLE(mm, bzla->sorts_unique_table);
  BZLA_INIT_STACK(bzla->mm, bzla->nodes_id_table);
  BZLA_PUSH_STACK(bzla->nodes_id_table, 0);
  BZLA_INIT_STACK(bzla->mm, bzla->functions_with_model);
  BZLA_INIT_STACK(bzla->mm, bzla->outputs);

  bzla_opt_init_opts(bzla);

  bzla->avmgr = bzla_aigvec_mgr_new(bzla);

  bzla->word_blaster = bzla_fp_word_blaster_new(bzla);

  bzla->rng = bzla_rng_new(mm, bzla_opt_get(bzla, BZLA_OPT_SEED));

  bzla->bv_assignments  = bzla_ass_new_bv_list(mm);
  bzla->fun_assignments = bzla_ass_new_fun_list(mm);

  bzla->node2symbol =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla->inputs  = bzla_hashptr_table_new(mm,
                                        (BzlaHashPtr) bzla_node_hash_by_id,
                                        (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->bv_vars = bzla_hashptr_table_new(mm,
                                         (BzlaHashPtr) bzla_node_hash_by_id,
                                         (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->ufs     = bzla_hashptr_table_new(mm,
                                     (BzlaHashPtr) bzla_node_hash_by_id,
                                     (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->lambdas = bzla_hashptr_table_new(mm,
                                         (BzlaHashPtr) bzla_node_hash_by_id,
                                         (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->quantifiers =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->feqs = bzla_hashptr_table_new(mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla->valid_assignments = 1;

  bzla->varsubst_constraints =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->embedded_constraints =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->unsynthesized_constraints =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->synthesized_constraints =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->assumptions =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->orig_assumptions =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->parameterized =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  BZLA_INIT_STACK(mm, bzla->assertions);
  BZLA_INIT_STACK(mm, bzla->assertions_trail);
  bzla->assertions_cache = bzla_hashint_table_new(mm);

#ifndef NDEBUG
  bzla->stats.rw_rules_applied = bzla_hashptr_table_new(
      mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmp);
#endif

  bzla->true_exp = bzla_exp_true(bzla);

  BZLA_CNEW(mm, bzla->rw_cache);
  bzla_rw_cache_init(bzla->rw_cache, bzla);

  return bzla;
}

static int32_t
terminate_aux_bzla(void *bzla)
{
  assert(bzla);

  int32_t res;
  Bzla *bt;

  bt = (Bzla *) bzla;
  if (!bt->cbs.term.fun) return 0;
  res = ((int32_t(*)(void *)) bt->cbs.term.fun)(bt->cbs.term.state);
  return res;
}

int32_t
bzla_terminate(Bzla *bzla)
{
  assert(bzla);

  if (bzla->cbs.term.termfun) return bzla->cbs.term.termfun(bzla);
  return 0;
}

void
bzla_set_term(Bzla *bzla, int32_t (*fun)(void *), void *state)
{
  assert(bzla);

  BzlaSATMgr *smgr;

  bzla->cbs.term.termfun = terminate_aux_bzla;
  bzla->cbs.term.fun     = fun;
  bzla->cbs.term.state   = state;

  smgr = bzla_get_sat_mgr(bzla);
  bzla_sat_mgr_set_term(smgr, terminate_aux_bzla, bzla);
}

void *
bzla_get_term_state(Bzla *bzla)
{
  assert(bzla);
  return bzla->cbs.term.state;
}

static void
release_all_exp_refs(Bzla *bzla, bool internal)
{
  assert(bzla);

  uint32_t i, cnt;
  BzlaNode *exp;

  cnt = BZLA_COUNT_STACK(bzla->nodes_id_table);
  if (internal)
  {
    for (i = 1; i <= cnt; i++)
    {
      exp = BZLA_PEEK_STACK(bzla->nodes_id_table, cnt - i);
      if (!exp) continue;
      if (bzla_node_is_simplified(exp)) exp->simplified = 0;
    }
  }
  for (i = 1; i <= cnt; i++)
  {
    if (!(exp = BZLA_PEEK_STACK(bzla->nodes_id_table, cnt - i))) continue;
    assert(exp->ext_refs <= exp->refs);
    bzla->external_refs -= exp->ext_refs;
    if (internal)
    {
      exp->refs = 1;
    }
    else
    {
      exp->refs = exp->refs - exp->ext_refs + 1;
    }
    assert(exp->refs > 0);
    exp->ext_refs = 0;
    bzla_node_release(bzla, exp);
    assert(!internal || !BZLA_PEEK_STACK(bzla->nodes_id_table, cnt - i));
  }
}

static void
release_all_sort_refs(Bzla *bzla, bool internal)
{
  assert(bzla);

  uint32_t i, cnt;
  BzlaSort *sort;

  cnt = BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort);
  for (i = 1; i <= cnt; i++)
  {
    sort = BZLA_PEEK_STACK(bzla->sorts_unique_table.id2sort, cnt - i);
    if (!sort) continue;
    assert(sort->refs);
    assert(sort->ext_refs <= sort->refs);
    bzla->external_refs -= sort->ext_refs;
    if (internal)
    {
      sort->refs = 1;
    }
    else
    {
      sort->refs = sort->refs - sort->ext_refs + 1;
    }
    assert(sort->refs > 0);
    sort->ext_refs = 0;
    bzla_sort_release(bzla, sort->id);
  }
}

void
bzla_release_all_ext_refs(Bzla *bzla)
{
  release_all_exp_refs(bzla, false);
  release_all_sort_refs(bzla, false);
}

void
bzla_delete_varsubst_constraints(Bzla *bzla)
{
  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, bzla->varsubst_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, it.bucket->data.as_ptr);
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(bzla->varsubst_constraints);
}

void
bzla_delete(Bzla *bzla)
{
  assert(bzla);

  uint32_t i;
  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  BzlaNode *exp;
  BzlaPtrHashTableIterator it;

  mm = bzla->mm;
  bzla_rng_delete(bzla->rng);
  bzla_fp_word_blaster_delete(bzla);

  if (bzla->slv) bzla->slv->api.delet(bzla->slv);
  if (bzla->qslv) bzla->qslv->api.delet(bzla->qslv);

  bzla_ass_delete_bv_list(
      bzla->bv_assignments,
      bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP)
          || bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP_INTERNAL));
  bzla_ass_delete_fun_list(
      bzla->fun_assignments,
      bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP)
          || bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP_INTERNAL));

  bzla_delete_varsubst_constraints(bzla);

  bzla_iter_hashptr_init(&it, bzla->inputs);
  bzla_iter_hashptr_queue(&it, bzla->embedded_constraints);
  bzla_iter_hashptr_queue(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  bzla_iter_hashptr_queue(&it, bzla->orig_assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));

  bzla_hashptr_table_delete(bzla->inputs);
  bzla_hashptr_table_delete(bzla->embedded_constraints);
  bzla_hashptr_table_delete(bzla->unsynthesized_constraints);
  bzla_hashptr_table_delete(bzla->synthesized_constraints);
  bzla_hashptr_table_delete(bzla->assumptions);
  bzla_hashptr_table_delete(bzla->orig_assumptions);

  for (i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(bzla->assertions, i));
  BZLA_RELEASE_STACK(bzla->assertions);
  BZLA_RELEASE_STACK(bzla->assertions_trail);
  bzla_hashint_table_delete(bzla->assertions_cache);

  bzla_model_delete(bzla);
  bzla_node_release(bzla, bzla->true_exp);

  for (i = 0; i < BZLA_COUNT_STACK(bzla->functions_with_model); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(bzla->functions_with_model, i));
  BZLA_RELEASE_STACK(bzla->functions_with_model);

  for (i = 0; i < BZLA_COUNT_STACK(bzla->outputs); i++)
    bzla_node_release(bzla, BZLA_PEEK_STACK(bzla->outputs, i));
  BZLA_RELEASE_STACK(bzla->outputs);

  BZLA_INIT_STACK(mm, stack);
  /* copy lambdas and push onto stack since bzla->lambdas does not hold a
   * reference and they may get released if bzla_node_lambda_delete_static_rho
   * is called */
  bzla_iter_hashptr_init(&it, bzla->lambdas);
  while (bzla_iter_hashptr_has_next(&it))
  {
    exp = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(stack, bzla_node_copy(bzla, exp));
  }
  while (!BZLA_EMPTY_STACK(stack))
  {
    exp = BZLA_POP_STACK(stack);
    bzla_node_lambda_delete_static_rho(bzla, exp);
    bzla_node_release(bzla, exp);
  }
  BZLA_RELEASE_STACK(stack);

  if (bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP) && bzla->external_refs)
    release_all_exp_refs(bzla, false);
  if (bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP_INTERNAL))
    release_all_exp_refs(bzla, true);

  if (bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP) && bzla->external_refs)
    release_all_sort_refs(bzla, false);
  if (bzla_opt_get(bzla, BZLA_OPT_AUTO_CLEANUP_INTERNAL))
    release_all_sort_refs(bzla, true);

  assert(getenv("BZLALEAK") || bzla->external_refs == 0);

#ifndef NDEBUG
  bool node_leak = false;
  BzlaNode *cur;
  /* we need to check id_table here as not all nodes are in the unique table */
  for (i = 0; i < BZLA_COUNT_STACK(bzla->nodes_id_table); i++)
  {
    cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i);
    if (cur)
    {
      BZLALOG(1,
              "  unreleased node: %s (%d)",
              bzla_util_node2string(cur),
              cur->refs);
      node_leak = true;
    }
  }
  assert(getenv("BZLALEAK") || getenv("BZLALEAKEXP") || !node_leak);
#endif
  BZLA_RELEASE_UNIQUE_TABLE(mm, bzla->nodes_unique_table);
  BZLA_RELEASE_STACK(bzla->nodes_id_table);

  assert(getenv("BZLALEAK") || getenv("BZLALEAKSORT")
         || bzla->sorts_unique_table.num_elements == 0);
  BZLA_RELEASE_SORT_UNIQUE_TABLE(mm, bzla->sorts_unique_table);

  bzla_iter_hashptr_init(&it, bzla->node2symbol);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_mem_freestr(bzla->mm, (char *) bzla_iter_hashptr_next_data(&it));
  bzla_hashptr_table_delete(bzla->node2symbol);

  bzla_hashptr_table_delete(bzla->bv_vars);
  bzla_hashptr_table_delete(bzla->ufs);
  bzla_hashptr_table_delete(bzla->lambdas);
  bzla_hashptr_table_delete(bzla->quantifiers);
  bzla_hashptr_table_delete(bzla->feqs);
  bzla_hashptr_table_delete(bzla->parameterized);
#ifndef NDEBUG
  bzla_hashptr_table_delete(bzla->stats.rw_rules_applied);
#endif

  if (bzla->avmgr) bzla_aigvec_mgr_delete(bzla->avmgr);
  bzla_opt_delete_opts(bzla);

  bzla_rw_cache_delete(bzla->rw_cache);
  BZLA_DELETE(mm, bzla->rw_cache);

  assert(bzla->rec_rw_calls == 0);
  bzla_msg_delete(bzla->msg);
  BZLA_DELETE(mm, bzla);
  bzla_mem_mgr_delete(mm);
}

void
bzla_set_msg_prefix(Bzla *bzla, const char *prefix)
{
  assert(bzla);

  bzla_mem_freestr(bzla->mm, bzla->msg->prefix);
  bzla->msg->prefix =
      prefix ? bzla_mem_strdup(bzla->mm, prefix) : (char *) prefix;
}

/* synthesizes unsynthesized constraints and updates constraints tables. */
void
bzla_process_unsynthesized_constraints(Bzla *bzla)
{
  assert(bzla);
  assert(!bzla->inconsistent);

  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *uc, *sc;
  BzlaPtrHashBucket *bucket;
  BzlaNode *cur;
  BzlaAIG *aig;
  BzlaAIGMgr *amgr;

  uc   = bzla->unsynthesized_constraints;
  sc   = bzla->synthesized_constraints;
  amgr = bzla_get_aig_mgr(bzla);

  /* We have to always synthesize FP inputs in order to guarantee that they
   * have a valid assignment when unconstrained. If not, when the model is
   * generated, they will be word-blasted into components and are assigned a
   * default value (all zero) that does not represent a valid FP.
   * Note that we don't necessarily have to synthesize RM inputs (they would
   * be assigned zero as default value when unconstrained, which is a valid
   * RM value), but we still do. */
  bzla_iter_hashptr_init(&it, bzla->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    cur = bzla_node_get_simplified(bzla, cur);
    if (bzla_node_is_fp(bzla, cur) || bzla_node_is_rm(bzla, cur))
    {
      bzla_synthesize_exp(bzla, cur, 0);
    }
  }
  /* assert constraints added during word-blasting */
  bzla_fp_word_blaster_add_additional_assertions(bzla);

  while (uc->count > 0)
  {
    bucket = uc->first;
    assert(bucket);
    cur = (BzlaNode *) bucket->key;

#if 0
#ifndef NDEBUG
      if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2)
	{
	  BzlaNode * real_cur = bzla_node_real_addr (cur);
	  if (bzla_node_is_bv_eq (real_cur))
	    {
	      BzlaNode * left = real_cur->e[0];
	      BzlaNode * right = real_cur->e[1];
	      BzlaNode * other;

	      if (bzla_node_is_bv_const (left))
		other = right;
	      else if (bzla_node_is_bv_const (right))
		other = left;
	      else
		other = 0;

	      // FIXME fails with symbolic lemmas (during beta-reduction
	      // rewrite level is forced to 1, hence symbolic lemmas might
	      // not be simplified as much as possible). possible solution:
	      // use rewrite level > 1 for lemma generation.
	      //if (other 
	      //    && !bzla_node_is_inverted (other) 
	      //    && bzla_node_is_bv_add (other))
	      //  {
	      //    assert (!bzla_node_is_bv_const (other->e[0]));
	      //    assert (!bzla_node_is_bv_const (other->e[1]));
	      //  }
	    }
	}
#endif
#endif

    if (!bzla_hashptr_table_get(sc, cur))
    {
      aig = exp_to_aig(bzla, cur);
      if (aig == BZLA_AIG_FALSE)
      {
        bzla->found_constraint_false = true;
        break;
      }
      bzla_aig_add_toplevel_to_sat(amgr, aig);
      bzla_aig_release(amgr, aig);
      (void) bzla_hashptr_table_add(sc, cur);
      bzla_hashptr_table_remove(uc, cur, 0, 0);
      /* assert constraints added during word-blasting */
      bzla_fp_word_blaster_add_additional_assertions(bzla);

      bzla->stats.constraints.synthesized++;
      report_constraint_stats(bzla, false);
    }
    else
    {
      /* constraint is already in sc */
      bzla_hashptr_table_remove(uc, cur, 0, 0);
      bzla_node_release(bzla, cur);
    }
  }
}

void
bzla_insert_unsynthesized_constraint(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(!bzla_node_real_addr(exp)->parameterized);

  BzlaBitVector *bits;
  BzlaPtrHashTable *uc;

  if (bzla_node_is_bv_const(exp))
  {
    bits = bzla_node_bv_const_get_bits(exp);
    assert(bzla_bv_get_width(bits) == 1);
    if (!bzla_bv_get_bit(bits, 0))
    {
      bzla->inconsistent = true;
      return;
    }
    /* we do not add true */
    return;
  }

  uc = bzla->unsynthesized_constraints;
  if (!bzla_hashptr_table_get(uc, exp))
  {
    (void) bzla_hashptr_table_add(uc, bzla_node_copy(bzla, exp));
    bzla_node_real_addr(exp)->constraint = 1;
    bzla->stats.constraints.unsynthesized++;
    BZLALOG(1, "add unsynthesized constraint: %s", bzla_util_node2string(exp));
  }

  /* Insert into embedded constraint table if constraint has parents.
   * Expressions containing embedded constraints get rebuilt and the embedded
   * constraint is substituted by true/false. */
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1
      && bzla_node_real_addr(exp)->parents > 0
      && !bzla_hashptr_table_get(bzla->embedded_constraints, exp))
  {
    assert(!bzla_node_is_bv_const(exp));
    (void) bzla_hashptr_table_add(bzla->embedded_constraints,
                                  bzla_node_copy(bzla, exp));
    bzla->stats.constraints.embedded++;
    BZLALOG(1,
            "add embedded constraint: %s (%u parents)",
            bzla_util_node2string(exp),
            bzla_node_real_addr(exp)->parents);
  }
}

static bool
constraint_is_inconsistent(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  //  assert (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 1);
  assert(bzla_node_bv_get_width(bzla, exp) == 1);

  exp = bzla_simplify_exp(bzla, exp);

  return bzla_node_is_bv_const_zero(bzla, exp)
         || bzla_hashptr_table_get(bzla->synthesized_constraints,
                                   bzla_node_invert(exp))
         || bzla_hashptr_table_get(bzla->unsynthesized_constraints,
                                   bzla_node_invert(exp));
}

static void
insert_into_constraint_tables(Bzla *bzla, BzlaNode *exp)
{
  if (constraint_is_inconsistent(bzla, exp))
  {
    bzla->inconsistent = true;
  }
  else
  {
    if (!bzla_node_real_addr(exp)->constraint)
    {
      bzla_insert_unsynthesized_constraint(bzla, exp);
    }
    else
    {
      assert(bzla_hashptr_table_get(bzla->unsynthesized_constraints, exp)
             || bzla_hashptr_table_get(bzla->synthesized_constraints, exp));
    }
  }
}

static void
insert_varsubst_constraint(Bzla *bzla, BzlaNode *left, BzlaNode *right)
{
  assert(bzla);
  assert(left);
  assert(right);

  BzlaNode *eq;
  BzlaPtrHashTable *vsc;
  BzlaPtrHashBucket *bucket;

  vsc    = bzla->varsubst_constraints;
  bucket = bzla_hashptr_table_get(vsc, left);

  if (!bucket)
  {
    BZLALOG(1,
            "add variable substitution: %s -> %s",
            bzla_util_node2string(left),
            bzla_util_node2string(right));

    bzla_hashptr_table_add(vsc, bzla_node_copy(bzla, left))->data.as_ptr =
        bzla_node_copy(bzla, right);

    bzla->stats.constraints.varsubst++;

    /* Always add varsubst contraints into unsynthesized/embedded contraints.
     * Otherwise, we get an inconsistent state if varsubst is disabled and
     * not all varsubst constraints have been processed. */
    eq = bzla_exp_eq(bzla, left, right);
    insert_into_constraint_tables(bzla, eq);
    bzla_node_release(bzla, eq);
  }
  /* if v = t_1 is already in varsubst, we have to synthesize v = t_2 */
  else if (right != (BzlaNode *) bucket->data.as_ptr)
  {
    eq = bzla_exp_eq(bzla, left, right);
    insert_into_constraint_tables(bzla, eq);
    bzla_node_release(bzla, eq);
  }
}

static BzlaSubstCompKind
reverse_subst_comp_kind(Bzla *bzla, BzlaSubstCompKind comp)
{
  assert(bzla);
  (void) bzla;
  switch (comp)
  {
    case BZLA_SUBST_COMP_ULT_KIND: return BZLA_SUBST_COMP_UGT_KIND;
    case BZLA_SUBST_COMP_ULTE_KIND: return BZLA_SUBST_COMP_UGTE_KIND;
    case BZLA_SUBST_COMP_UGT_KIND: return BZLA_SUBST_COMP_ULT_KIND;
    default:
      assert(comp == BZLA_SUBST_COMP_UGTE_KIND);
      return BZLA_SUBST_COMP_ULTE_KIND;
  }
}

/* check if left does not occur on the right side */
static bool
occurrence_check(Bzla *bzla, BzlaNode *left, BzlaNode *right)
{
  assert(bzla);
  assert(left);
  assert(right);

  BzlaNode *cur, *real_left;
  BzlaNodePtrQueue queue;
  bool is_cyclic;
  uint32_t i;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache;

  double start = bzla_util_time_stamp();
  is_cyclic    = false;
  mm           = bzla->mm;
  cache        = bzla_hashint_table_new(mm);
  real_left    = bzla_node_real_addr(left);
  BZLA_INIT_QUEUE(mm, queue);

  cur = bzla_node_real_addr(right);
  goto OCCURRENCE_CHECK_ENTER_WITHOUT_POP;

  do
  {
    cur = bzla_node_real_addr(BZLA_DEQUEUE(queue));
  OCCURRENCE_CHECK_ENTER_WITHOUT_POP:
    assert(!bzla_node_is_simplified(cur)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    cur = bzla_node_real_addr(bzla_node_get_simplified(bzla, cur));

    if (real_left->id > cur->id) continue;

    if (!bzla_hashint_table_contains(cache, cur->id))
    {
      bzla_hashint_table_add(cache, cur->id);
      if (cur == real_left)
      {
        is_cyclic = true;
        break;
      }
      for (i = 1; i <= cur->arity; i++)
        BZLA_ENQUEUE(queue, cur->e[cur->arity - i]);
    }
  } while (!BZLA_EMPTY_QUEUE(queue));
  BZLA_RELEASE_QUEUE(queue);
  bzla_hashint_table_delete(cache);
  bzla->time.occurrence += bzla_util_time_stamp() - start;
  return is_cyclic;
}

/* checks if we can substitute and normalizes arguments to substitution,
 * substitute left_result with right_result, exp is child of AND_NODE */
static bool
normalize_substitution(Bzla *bzla,
                       BzlaNode *exp,
                       BzlaNode **left_result,
                       BzlaNode **right_result)
{
  assert(bzla_opt_get(bzla, BZLA_OPT_PP_VAR_SUBST));

  BzlaNode *left, *right, *real_left, *real_right, *tmp, *inv, *var, *lambda;
  BzlaNode *const_exp, *e0, *e1;
  uint32_t leadings;
  BzlaBitVector *ic, *fc, *bits;
  BzlaMemMgr *mm;
  BzlaSubstCompKind comp;
  BzlaSortId sort;

  assert(bzla);
  assert(exp);
  assert(left_result);
  assert(right_result);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1);
  assert(bzla_simplify_exp(bzla, exp) == exp);

  mm = bzla->mm;

  /* boolean BV_NODE, force assignment (right_result) w.r.t. phase */
  if (bzla_node_is_bv_var(exp))
  {
    assert(bzla_node_bv_get_width(bzla, exp) == 1);
    sort = bzla_sort_bv(bzla, 1);
    if (bzla_node_is_inverted(exp))
    {
      *left_result  = bzla_node_copy(bzla, bzla_node_real_addr(exp));
      *right_result = bzla_exp_bv_zero(bzla, sort);
    }
    else
    {
      *left_result  = bzla_node_copy(bzla, exp);
      *right_result = bzla_exp_bv_one(bzla, sort);
    }
    bzla_sort_release(bzla, sort);
    return true;
  }

  if (bzla_node_is_bv_ult(exp))
  {
    e0 = bzla_node_get_simplified(bzla, bzla_node_real_addr(exp)->e[0]);
    e1 = bzla_node_get_simplified(bzla, bzla_node_real_addr(exp)->e[1]);

    if (bzla_node_is_bv_var(e0) || bzla_node_is_bv_var(e1))
    {
      if (bzla_node_is_inverted(exp))
        comp = BZLA_SUBST_COMP_UGTE_KIND;
      else
        comp = BZLA_SUBST_COMP_ULT_KIND;

      if (bzla_node_is_bv_var(e0))
      {
        var   = e0;
        right = e1;
      }
      else
      {
        assert(bzla_node_is_bv_var(e1));
        var   = e1;
        right = e0;
        comp  = reverse_subst_comp_kind(bzla, comp);
      }

      /* ~a comp b is equal to a reverse_comp ~b,
       * where comp in ult, ulte, ugt, ugte
       * (e.g. reverse_comp of ult is ugt) */
      if (bzla_node_is_inverted(var))
      {
        var   = bzla_node_real_addr(var);
        right = bzla_node_invert(right);
        comp  = reverse_subst_comp_kind(bzla, comp);
      }

      /* we do not create a lambda (index) if variable is already in
       * substitution table */
      assert(!bzla_node_is_inverted(var));
      if (bzla_hashptr_table_get(bzla->varsubst_constraints, var)) return false;

      if (!bzla_node_is_bv_const(right)) return false;

      bits = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(right));

      if (comp == BZLA_SUBST_COMP_ULT_KIND || comp == BZLA_SUBST_COMP_ULTE_KIND)
      {
        leadings = bzla_bv_get_num_leading_zeros(bits);
        if (leadings > 0)
        {
          sort      = bzla_sort_bv(bzla, leadings);
          const_exp = bzla_exp_bv_zero(bzla, sort);
          bzla_sort_release(bzla, sort);
          sort =
              bzla_sort_bv(bzla, bzla_node_bv_get_width(bzla, var) - leadings);
          lambda = bzla_exp_var(bzla, sort, 0);
          bzla_sort_release(bzla, sort);
          tmp = bzla_exp_bv_concat(bzla, const_exp, lambda);
          insert_varsubst_constraint(bzla, var, tmp);
          bzla_node_release(bzla, const_exp);
          bzla_node_release(bzla, lambda);
          bzla_node_release(bzla, tmp);
        }
      }
      else
      {
        assert(comp == BZLA_SUBST_COMP_UGT_KIND
               || comp == BZLA_SUBST_COMP_UGTE_KIND);
        leadings = bzla_bv_get_num_leading_ones(bits);
        if (leadings > 0)
        {
          sort      = bzla_sort_bv(bzla, leadings);
          const_exp = bzla_exp_bv_ones(bzla, sort);
          bzla_sort_release(bzla, sort);
          sort =
              bzla_sort_bv(bzla, bzla_node_bv_get_width(bzla, var) - leadings);
          lambda = bzla_exp_var(bzla, sort, 0);
          bzla_sort_release(bzla, sort);
          tmp = bzla_exp_bv_concat(bzla, const_exp, lambda);
          insert_varsubst_constraint(bzla, var, tmp);
          bzla_node_release(bzla, const_exp);
          bzla_node_release(bzla, lambda);
          bzla_node_release(bzla, tmp);
        }
      }

      bzla_bv_free(bzla->mm, bits);
      return false;
    }
  }

  /* in the boolean case a != b is the same as a == ~b */
  if (bzla_node_is_inverted(exp) && bzla_node_is_bv_eq(exp)
      && bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[0]) == 1)
  {
    left  = bzla_node_get_simplified(bzla, bzla_node_real_addr(exp)->e[0]);
    right = bzla_node_get_simplified(bzla, bzla_node_real_addr(exp)->e[1]);

    if (bzla_node_is_bv_var(left))
    {
      *left_result  = bzla_node_copy(bzla, left);
      *right_result = bzla_node_invert(bzla_node_copy(bzla, right));
      goto BZLA_NORMALIZE_SUBST_RESULT;
    }

    if (bzla_node_is_bv_var(right))
    {
      *left_result  = bzla_node_copy(bzla, right);
      *right_result = bzla_node_invert(bzla_node_copy(bzla, left));
      goto BZLA_NORMALIZE_SUBST_RESULT;
    }
  }

  if (bzla_node_is_inverted(exp) || !bzla_node_is_eq(exp)) return false;

  left       = bzla_node_get_simplified(bzla, exp->e[0]);
  right      = bzla_node_get_simplified(bzla, exp->e[1]);
  real_left  = bzla_node_real_addr(left);
  real_right = bzla_node_real_addr(right);

  if (bzla_node_is_bv(bzla, real_left) && !bzla_node_is_bv_var(real_left)
      && !bzla_node_is_bv_var(real_right))
  {
    if (bzla_rewrite_linear_bv_term(bzla, left, &fc, left_result, &tmp))
      *right_result = bzla_exp_bv_sub(bzla, right, tmp);
    else if (bzla_rewrite_linear_bv_term(bzla, right, &fc, left_result, &tmp))
      *right_result = bzla_exp_bv_sub(bzla, left, tmp);
    else
      return false;

    bzla->stats.gaussian_eliminations++;

    bzla_node_release(bzla, tmp);
    ic = bzla_bv_mod_inverse(bzla->mm, fc);
    bzla_bv_free(bzla->mm, fc);
    inv = bzla_exp_bv_const(bzla, ic);
    bzla_bv_free(bzla->mm, ic);
    tmp = bzla_exp_bv_mul(bzla, *right_result, inv);
    bzla_node_release(bzla, inv);
    bzla_node_release(bzla, *right_result);
    *right_result = tmp;
  }
  else
  {
    if ((!bzla_node_is_var(real_left) && bzla_node_is_var(real_right))
        || (!bzla_node_is_uf(real_left) && bzla_node_is_uf(real_right)))
    {
      *left_result  = right;
      *right_result = left;
    }
    else
    {
      *left_result  = left;
      *right_result = right;
    }

    bzla_node_copy(bzla, left);
    bzla_node_copy(bzla, right);
  }

BZLA_NORMALIZE_SUBST_RESULT:
  if (bzla_node_is_inverted(*left_result))
  {
    *left_result  = bzla_node_invert(*left_result);
    *right_result = bzla_node_invert(*right_result);
  }

  if (occurrence_check(bzla, *left_result, *right_result))
  {
    bzla_node_release(bzla, *left_result);
    bzla_node_release(bzla, *right_result);
    return false;
  }

  return true;
}

static void
insert_new_constraint(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_bv_get_width(bzla, exp) == 1);
  assert(!bzla_node_real_addr(exp)->parameterized);

  BzlaBitVector *bits;
  BzlaNode *left, *right, *real_exp;

  exp      = bzla_simplify_exp(bzla, exp);
  real_exp = bzla_node_real_addr(exp);

  if (bzla_node_is_bv_const(real_exp))
  {
    bits = bzla_node_bv_const_get_bits(real_exp);
    assert(bzla_bv_get_width(bits) == 1);
    /* we do not add true/false */
    if ((bzla_node_is_inverted(exp) && bzla_bv_get_bit(bits, 0))
        || (!bzla_node_is_inverted(exp) && !bzla_bv_get_bit(bits, 0)))
    {
      BZLALOG(
          1, "inserted inconsistent constraint %s", bzla_util_node2string(exp));
      bzla->inconsistent = true;
    }
    else
    {
      assert((bzla_node_is_inverted(exp) && !bzla_bv_get_bit(bits, 0))
             || (!bzla_node_is_inverted(exp) && bzla_bv_get_bit(bits, 0)));
    }
    return;
  }

  if (!bzla_hashptr_table_get(bzla->synthesized_constraints, exp))
  {
    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1
        && bzla_opt_get(bzla, BZLA_OPT_PP_VAR_SUBST)
        && normalize_substitution(bzla, exp, &left, &right))
    {
      insert_varsubst_constraint(bzla, left, right);
      bzla_node_release(bzla, left);
      bzla_node_release(bzla, right);
    }
    else
    {
      insert_into_constraint_tables(bzla, exp);
      report_constraint_stats(bzla, false);
    }
  }
}

void
bzla_reset_assumptions(Bzla *bzla)
{
  assert(bzla);

  BzlaPtrHashTableIterator it;

  BZLALOG(2, "reset assumptions");

  bzla_iter_hashptr_init(&it, bzla->assumptions);
  bzla_iter_hashptr_queue(&it, bzla->orig_assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(bzla->assumptions);
  bzla_hashptr_table_delete(bzla->orig_assumptions);
  bzla->assumptions =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla->orig_assumptions =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
}

void
bzla_reset_functions_with_model(Bzla *bzla)
{
  BzlaNode *cur;
  uint32_t i;

  assert(bzla);

  for (i = 0; i < BZLA_COUNT_STACK(bzla->functions_with_model); i++)
  {
    cur = bzla->functions_with_model.start[i];
    assert(!bzla_node_is_inverted(cur));
    if (!bzla_node_is_simplified(cur))
    {
      assert(bzla_node_is_fun(cur));
      assert(cur->rho);
      bzla_hashptr_table_delete(cur->rho);
      cur->rho = 0;
    }
    bzla_node_release(bzla, cur);
  }
  BZLA_RESET_STACK(bzla->functions_with_model);
}

void
bzla_reset_incremental_usage(Bzla *bzla)
{
  assert(bzla);

  bzla_reset_assumptions(bzla);
  bzla_reset_functions_with_model(bzla);
  bzla->valid_assignments = 0;
  bzla_model_delete(bzla);
}

static void
add_constraint(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  BzlaNode *cur, *child;
  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  BzlaIntHashTable *mark;

  exp = bzla_simplify_exp(bzla, exp);
  assert(!bzla_node_is_fun(exp));
  assert(bzla_node_bv_get_width(bzla, exp) == 1);
  assert(!bzla_node_real_addr(exp)->parameterized);
  mm   = bzla->mm;
  mark = bzla_hashint_table_new(mm);

  if (bzla->valid_assignments) bzla_reset_incremental_usage(bzla);

  if (!bzla_node_is_inverted(exp) && bzla_node_is_bv_and(exp))
  {
    BZLA_INIT_STACK(mm, stack);
    cur = exp;
    goto ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP;

    do
    {
      cur = BZLA_POP_STACK(stack);
    ADD_CONSTRAINT_ENTER_LOOP_WITHOUT_POP:
      assert(!bzla_node_is_inverted(cur));
      assert(bzla_node_is_bv_and(cur));
      if (!bzla_hashint_table_contains(mark, cur->id))
      {
        bzla_hashint_table_add(mark, cur->id);
        child = cur->e[1];
        if (!bzla_node_is_inverted(child) && bzla_node_is_bv_and(child))
          BZLA_PUSH_STACK(stack, child);
        else
          insert_new_constraint(bzla, child);
        child = cur->e[0];
        if (!bzla_node_is_inverted(child) && bzla_node_is_bv_and(child))
          BZLA_PUSH_STACK(stack, child);
        else
          insert_new_constraint(bzla, child);
      }
    } while (!BZLA_EMPTY_STACK(stack));
    BZLA_RELEASE_STACK(stack);
  }
  else
    insert_new_constraint(bzla, exp);

  bzla_hashint_table_delete(mark);
  assert(bzla_dbg_check_constraints_not_const(bzla));
}

void
bzla_assert_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  exp = bzla_simplify_exp(bzla, exp);
  assert(!bzla_node_is_fun(exp));
  assert(bzla_node_bv_get_width(bzla, exp) == 1);
  assert(!bzla_node_real_addr(exp)->parameterized);

  add_constraint(bzla, exp);
}

static int32_t
exp_to_cnf_lit(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_bv_get_width(bzla, exp) == 1);

  int32_t res, sign, val;
  BzlaSATMgr *smgr;
  BzlaAIGMgr *amgr;
  BzlaAIG *aig;

  exp = bzla_simplify_exp(bzla, exp);

  sign = 1;

  if (bzla_node_is_inverted(exp))
  {
    exp = bzla_node_invert(exp);
    sign *= -1;
  }

  aig = exp_to_aig(bzla, exp);

  amgr = bzla_get_aig_mgr(bzla);
  smgr = bzla_get_sat_mgr(bzla);

  if (bzla_aig_is_const(aig))
  {
    res = smgr->true_lit;
    if (aig == BZLA_AIG_FALSE) sign *= -1;
  }
  else
  {
    if (BZLA_IS_INVERTED_AIG(aig))
    {
      aig = BZLA_INVERT_AIG(aig);
      sign *= -1;
    }

    if (!aig->cnf_id) bzla_aig_to_sat_tseitin(amgr, aig);

    res = aig->cnf_id;
    bzla_aig_release(amgr, aig);

    if ((val = bzla_sat_fixed(smgr, res)))
    {
      res = smgr->true_lit;
      if (val < 0) sign *= -1;
    }
  }
  res *= sign;

  return res;
}

void
bzla_assume_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
  assert(exp);
  assert(!bzla_node_real_addr(exp)->parameterized);

  if (bzla->valid_assignments) bzla_reset_incremental_usage(bzla);

  BZLALOG(2,
          "assume: %s (%s)",
          bzla_util_node2string(exp),
          bzla_util_node2string(bzla_simplify_exp(bzla, exp)));

  if (!bzla_hashptr_table_get(bzla->orig_assumptions, exp))
  {
    bzla_hashptr_table_add(bzla->orig_assumptions, bzla_node_copy(bzla, exp));
  }

  exp = bzla_simplify_exp(bzla, exp);
  if (!bzla_hashptr_table_get(bzla->assumptions, exp))
  {
    (void) bzla_hashptr_table_add(bzla->assumptions, bzla_node_copy(bzla, exp));
  }
}

bool
bzla_is_assumption_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
  assert(exp);

  BZLALOG(2, "is_assumption: %s", bzla_util_node2string(exp));
  return bzla_hashptr_table_get(bzla->orig_assumptions, exp) ? true : false;
}

bool
bzla_failed_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
  assert(bzla->last_sat_result == BZLA_RESULT_UNSAT);
  assert(exp);
  assert(bzla_is_assumption_exp(bzla, exp));
  BZLALOG(2,
          "check failed assumption: %s (%s)",
          bzla_util_node2string(exp),
          bzla_util_node2string(bzla_simplify_exp(bzla, exp)));

  bool res;
  int32_t i, lit;
  double start;
  BzlaAIG *aig;
  BzlaNode *real_exp, *cur, *e;
  BzlaNodePtrStack work_stack, assumptions;
  BzlaSATMgr *smgr;
  BzlaIntHashTable *mark;

  start = bzla_util_time_stamp();

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(!bzla_node_is_fun(exp));
  assert(bzla_node_bv_get_width(bzla, exp) == 1);
  assert(!bzla_node_real_addr(exp)->parameterized);
  mark = bzla_hashint_table_new(bzla->mm);
  smgr = bzla_get_sat_mgr(bzla);
  assert(smgr);

  if (bzla->inconsistent)
  {
    res = false;
  }
  else if (exp == bzla->true_exp)
  {
    res = false;
  }
  else if (exp == bzla_node_invert(bzla->true_exp))
  {
    res = true;
  }
  else if (!bzla_sat_is_initialized(smgr))
  {
    res = true;
  }
  else if (bzla_node_is_inverted(exp) || !bzla_node_is_bv_and(exp))
  {
    real_exp = bzla_node_real_addr(exp);
    assert(bzla->found_constraint_false || bzla_node_is_synth(real_exp));

    if (!bzla_node_is_synth(real_exp))
    {
      res = false;
    }
    else if (bzla->found_constraint_false)
    {
      res = ((bzla_node_is_inverted(exp)
              && real_exp->av->aigs[0] == BZLA_AIG_TRUE)
             || (!bzla_node_is_inverted(exp)
                 && real_exp->av->aigs[0] == BZLA_AIG_FALSE));
    }
    else
    {
      if ((bzla_node_is_inverted(exp)
           && real_exp->av->aigs[0] == BZLA_AIG_FALSE)
          || (!bzla_node_is_inverted(exp)
              && real_exp->av->aigs[0] == BZLA_AIG_TRUE))
      {
        res = false;
      }
      else
      {
        lit = exp_to_cnf_lit(bzla, exp);
        if (abs(lit) == smgr->true_lit)
          res = lit < 0;
        else
          res = bzla_sat_failed(smgr, lit) > 0;
      }
    }
  }
  else
  {
    res = false;
    BZLA_INIT_STACK(bzla->mm, assumptions);
    BZLA_INIT_STACK(bzla->mm, work_stack);
    BZLA_PUSH_STACK(work_stack, exp);
    while (!BZLA_EMPTY_STACK(work_stack))
    {
      cur = BZLA_POP_STACK(work_stack);
      assert(!bzla_node_is_inverted(cur));
      assert(bzla_node_is_bv_and(cur));
      if (bzla_hashint_table_contains(mark, cur->id)) continue;
      bzla_hashint_table_add(mark, cur->id);
      for (i = 0; i < 2; i++)
      {
        e = cur->e[i];
        if (!bzla_node_is_inverted(e) && bzla_node_is_bv_and(e))
          BZLA_PUSH_STACK(work_stack, e);
        else
        {
          if (!bzla_node_is_synth(bzla_node_real_addr(e))) continue;

          aig = bzla_node_real_addr(e)->av->aigs[0];
          if ((bzla_node_is_inverted(e) && aig == BZLA_AIG_FALSE)
              || (!bzla_node_is_inverted(e) && aig == BZLA_AIG_TRUE))
            continue;
          if ((bzla_node_is_inverted(e) && aig == BZLA_AIG_TRUE)
              || (!bzla_node_is_inverted(e) && aig == BZLA_AIG_FALSE))
            goto ASSUMPTION_FAILED;
          if (bzla->found_constraint_false) continue;
          BZLA_PUSH_STACK(assumptions, e);
        }
      }
    }

    while (!BZLA_EMPTY_STACK(assumptions))
    {
      cur = BZLA_POP_STACK(assumptions);
      assert(bzla_node_is_inverted(cur) || !bzla_node_is_bv_and(cur));
      lit = exp_to_cnf_lit(bzla, cur);
      if (lit == smgr->true_lit) continue;
      if (lit == -smgr->true_lit || bzla_sat_failed(smgr, lit))
      {
      ASSUMPTION_FAILED:
        res = true;
        break;
      }
    }
    BZLA_RELEASE_STACK(work_stack);
    BZLA_RELEASE_STACK(assumptions);
  }

  bzla_hashint_table_delete(mark);
  bzla->time.failed += bzla_util_time_stamp() - start;

  return res;
}

void
bzla_fixate_assumptions(Bzla *bzla)
{
  BzlaNode *exp;
  BzlaNodePtrStack stack;
  BzlaPtrHashTableIterator it;
  size_t i;

  BZLA_INIT_STACK(bzla->mm, stack);
  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    BZLA_PUSH_STACK(stack, bzla_node_copy(bzla, bzla_iter_hashptr_next(&it)));
  for (i = 0; i < BZLA_COUNT_STACK(stack); i++)
  {
    exp = BZLA_PEEK_STACK(stack, i);
    bzla_assert_exp(bzla, exp);
    bzla_node_release(bzla, exp);
  }
  BZLA_RELEASE_STACK(stack);
  bzla_reset_assumptions(bzla);
}

/*------------------------------------------------------------------------*/

static void
replace_constraint(Bzla *bzla, BzlaNode *old, BzlaNode *new)
{
  assert(bzla);
  assert(old);
  assert(bzla_node_is_regular(old));
  assert(old->constraint);
  assert(old->refs > 1);
  assert(!old->parameterized);
  assert(!bzla_node_real_addr(new)->parameterized);
  assert(bzla_node_is_simplified(old));
  assert(!bzla_node_is_simplified(new));

  BzlaPtrHashTable *unsynthesized_constraints, *synthesized_constraints;
  BzlaPtrHashTable *embedded_constraints, *pos, *neg;
  BzlaNode *not_new, *not_old;

  BZLALOG(1,
          "replace constraint: %s -> %s",
          bzla_util_node2string(old),
          bzla_util_node2string(new));

  not_old                   = bzla_node_invert(old);
  not_new                   = bzla_node_invert(new);
  embedded_constraints      = bzla->embedded_constraints;
  unsynthesized_constraints = bzla->unsynthesized_constraints;
  synthesized_constraints   = bzla->synthesized_constraints;
  pos = neg = 0;

  if (bzla_hashptr_table_get(unsynthesized_constraints, old))
  {
    add_constraint(bzla, new);
    assert(!pos);
    pos = unsynthesized_constraints;
  }

  if (bzla_hashptr_table_get(unsynthesized_constraints, not_old))
  {
    add_constraint(bzla, not_new);
    assert(!neg);
    neg = unsynthesized_constraints;
  }

  if (bzla_hashptr_table_get(synthesized_constraints, old))
  {
    add_constraint(bzla, new);
    assert(!pos);
    pos = synthesized_constraints;
  }

  if (bzla_hashptr_table_get(synthesized_constraints, not_old))
  {
    add_constraint(bzla, not_new);
    assert(!neg);
    neg = synthesized_constraints;
  }

  if (pos)
  {
    bzla_hashptr_table_remove(pos, old, 0, 0);
    bzla_node_release(bzla, old);

    if (bzla_hashptr_table_get(embedded_constraints, old))
    {
      bzla_hashptr_table_remove(embedded_constraints, old, 0, 0);
      bzla_node_release(bzla, old);
    }
  }

  if (neg)
  {
    bzla_hashptr_table_remove(neg, not_old, 0, 0);
    bzla_node_release(bzla, not_old);

    if (bzla_hashptr_table_get(embedded_constraints, not_old))
    {
      bzla_hashptr_table_remove(embedded_constraints, not_old, 0, 0);
      bzla_node_release(bzla, not_old);
    }
  }

  old->constraint = 0;
}

void
bzla_set_simplified_exp(Bzla *bzla, BzlaNode *exp, BzlaNode *simplified)
{
  assert(bzla);
  assert(exp);
  assert(simplified);
  assert(bzla_node_is_regular(exp));
  assert(exp != bzla_node_real_addr(simplified));
  assert(!bzla_node_real_addr(simplified)->simplified);
  assert(exp->arity <= 4);
  assert(bzla_node_get_sort_id(exp) == bzla_node_get_sort_id(simplified));
  assert(exp->parameterized || !bzla_node_real_addr(simplified)->parameterized);
  assert(!bzla_node_real_addr(simplified)->parameterized || exp->parameterized);

  BZLALOG(2,
          "set simplified: %s -> %s (synth: %u, param: %u)",
          bzla_util_node2string(exp),
          bzla_util_node2string(simplified),
          bzla_node_is_synth(exp),
          exp->parameterized);

  /* FIXME: indicator for slow-down in incremental mode, when too many
   * synthesized nodes are rewritten, it can significantly slow-down the
   * solver. */
  if (bzla_node_is_synth(exp)) bzla->stats.rewrite_synth++;

  if (exp->simplified) bzla_node_release(bzla, exp->simplified);

  exp->simplified = bzla_node_copy(bzla, simplified);

  if (exp->constraint) replace_constraint(bzla, exp, exp->simplified);

  if (!bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST))
  {
    bzla_node_set_to_proxy(bzla, exp);

    /* if simplified is parameterized, exp was also parameterized */
    if (bzla_node_real_addr(simplified)->parameterized) exp->parameterized = 1;
  }
}

/* Finds most simplified expression and shortens path to it */
static BzlaNode *
recursively_pointer_chase_simplified_exp(Bzla *bzla, BzlaNode *exp)
{
  BzlaNode *real_exp, *cur, *simplified, *not_simplified, *next;
  bool invert;

  assert(bzla);
  assert(exp);

  real_exp = bzla_node_real_addr(exp);

  assert(real_exp->simplified);
  assert(bzla_node_real_addr(real_exp->simplified)->simplified);

  /* shorten path to simplified expression */
  invert     = false;
  simplified = real_exp->simplified;
  do
  {
    assert(!bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST)
           || !bzla_node_is_proxy(simplified));
    assert(bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST)
           || bzla_node_is_proxy(simplified));
    if (bzla_node_is_inverted(simplified)) invert = !invert;
    simplified = bzla_node_real_addr(simplified)->simplified;
  } while (bzla_node_real_addr(simplified)->simplified);
  /* 'simplified' is representative element */
  assert(!bzla_node_real_addr(simplified)->simplified);
  if (invert) simplified = bzla_node_invert(simplified);

  invert         = false;
  not_simplified = bzla_node_invert(simplified);
  cur            = bzla_node_copy(bzla, real_exp);
  do
  {
    if (bzla_node_is_inverted(cur)) invert = !invert;
    cur  = bzla_node_real_addr(cur);
    next = bzla_node_copy(bzla, cur->simplified);
    bzla_set_simplified_exp(bzla, cur, invert ? not_simplified : simplified);
    bzla_node_release(bzla, cur);
    cur = next;
  } while (bzla_node_real_addr(cur)->simplified);
  bzla_node_release(bzla, cur);

  /* if starting expression is inverted, then we have to invert result */
  if (bzla_node_is_inverted(exp)) simplified = bzla_node_invert(simplified);

  return simplified;
}

BzlaNode *
bzla_node_get_simplified(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(!bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST)
         || !bzla_node_is_proxy(exp));

  (void) bzla;
  BzlaNode *real_exp;

  real_exp = bzla_node_real_addr(exp);

  /* no simplified expression ? */
  if (!real_exp->simplified)
  {
    return exp;
  }

  /* only one simplified expression ? */
  if (!bzla_node_real_addr(real_exp->simplified)->simplified)
  {
    if (bzla_node_is_inverted(exp))
      return bzla_node_invert(real_exp->simplified);
    return exp->simplified;
  }
  return recursively_pointer_chase_simplified_exp(bzla, exp);
}

static BzlaNode *
simplify_constraint_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_real_addr(exp)->constraint);
  assert(!bzla_node_real_addr(exp)->simplified);
  /* embedded constraints rewriting enabled with rwl > 1 */
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1);

  BzlaNode *real_exp, *result, *not_exp;

  real_exp = bzla_node_real_addr(exp);

  /* Do not simplify top-level constraint applies (we need the implication
   * dependencies for determining top applies when dual prop enabled) */
  if (bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP)
      && bzla_node_is_apply(real_exp))
    return exp;

  not_exp = bzla_node_invert(real_exp);

  if (bzla_node_is_bv_const(real_exp)) return exp;

  if (bzla_hashptr_table_get(bzla->unsynthesized_constraints, real_exp))
  {
    result = bzla->true_exp;
  }
  else if (bzla_hashptr_table_get(bzla->unsynthesized_constraints, not_exp))
  {
    result = bzla_node_invert(bzla->true_exp);
  }
  else if (bzla_hashptr_table_get(bzla->synthesized_constraints, real_exp))
  {
    result = bzla->true_exp;
  }
  else
  {
    assert(bzla_hashptr_table_get(bzla->synthesized_constraints, not_exp));
    result = bzla_node_invert(bzla->true_exp);
  }

  if (bzla_node_is_inverted(exp)) return bzla_node_invert(result);

  return result;
}

BzlaNode *
bzla_simplify_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(bzla_node_real_addr(exp)->refs > 0);

  BzlaNode *result;

  result = bzla_node_get_simplified(bzla, exp);

  /* NOTE: embedded constraints rewriting is enabled with rwl > 1 */
  if (bzla_opt_get(bzla, BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS)
      && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1
      && bzla_node_real_addr(result)->constraint)
    return simplify_constraint_exp(bzla, result);

  assert(bzla_node_real_addr(result)->bzla == bzla);
  assert(bzla_node_real_addr(result)->refs > 0);

  return result;
}

/*------------------------------------------------------------------------*/

/* bit vector skeleton is always encoded, i.e., if bzla_node_is_synth is true,
 * then it is also encoded. with option lazy_synthesize enabled,
 * 'bzla_synthesize_exp' stops at feq and apply nodes */
void
bzla_synthesize_exp(Bzla *bzla, BzlaNode *exp, BzlaPtrHashTable *backannotation)
{
  BzlaNodePtrStack exp_stack;
  BzlaNode *cur, *wb, *value, *args, *real_e;
  BzlaAIGVec *av0, *av1, *av2;
  BzlaMemMgr *mm;
  BzlaAIGVecMgr *avmgr;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTable *static_rho;
  BzlaPtrHashTableIterator it;
  char *indexed_name;
  const char *name;
  uint32_t count, i, j, len;
  bool is_same_children_mem;
  bool invert_av0 = false;
  bool invert_av1 = false;
  bool invert_av2 = false;
  double start;
  bool restart, opt_lazy_synth;
  BzlaIntHashTable *cache;

  assert(bzla);
  assert(exp);

  start          = bzla_util_time_stamp();
  mm             = bzla->mm;
  avmgr          = bzla->avmgr;
  count          = 0;
  cache          = bzla_hashint_table_new(mm);
  opt_lazy_synth = bzla_opt_get(bzla, BZLA_OPT_FUN_LAZY_SYNTHESIZE) == 1;

  BZLA_INIT_STACK(mm, exp_stack);
  BZLA_PUSH_STACK(exp_stack, exp);
  BZLALOG(2, "%s: %s", __FUNCTION__, bzla_util_node2string(exp));

  while (!BZLA_EMPTY_STACK(exp_stack))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(exp_stack));
    assert(!bzla_node_is_proxy(cur));
    assert(!bzla_node_is_simplified(cur));

    if (bzla_node_is_synth(cur)) continue;

    count++;
    if (!bzla_hashint_table_contains(cache, cur->id))
    {
      if (bzla_node_is_bv_const(cur))
      {
        cur->av = bzla_aigvec_const(avmgr, bzla_node_bv_const_get_bits(cur));
        BZLALOG(2, "  synthesized: %s", bzla_util_node2string(cur));
        /* no need to call bzla_aigvec_to_sat_tseitin here */
      }
      /* encode bv skeleton inputs: var, apply, feq
       * exception: FP/RM applies, we need to word-blast them first */
      else if (bzla_node_is_bv_var(cur)
               || (bzla_node_is_apply(cur) && !cur->parameterized
                   && bzla_node_is_bv(bzla, cur))
               || (bzla_node_is_fun_eq(cur) && !cur->parameterized))
      {
        assert(!cur->parameterized);
        cur->av = bzla_aigvec_var(avmgr, bzla_node_bv_get_width(bzla, cur));

        if (bzla_node_is_bv_var(cur) && backannotation
            && (name = bzla_node_get_symbol(bzla, cur)))
        {
          len = strlen(name) + 40;
          if (bzla_node_bv_get_width(bzla, cur) > 1)
          {
            indexed_name = bzla_mem_malloc(mm, len);
            for (i = 0; i < cur->av->width; i++)
            {
              b = bzla_hashptr_table_add(backannotation, cur->av->aigs[i]);
              assert(b->key == cur->av->aigs[i]);
              sprintf(indexed_name, "%s[%d]", name, cur->av->width - i - 1);
              b->data.as_str = bzla_mem_strdup(mm, indexed_name);
            }
            bzla_mem_free(mm, indexed_name, len);
          }
          else
          {
            assert(bzla_node_bv_get_width(bzla, cur) == 1);
            b = bzla_hashptr_table_add(backannotation, cur->av->aigs[0]);
            assert(b->key == cur->av->aigs[0]);
            b->data.as_str = bzla_mem_strdup(mm, name);
          }
        }
        BZLALOG(2, "  synthesized: %s", bzla_util_node2string(cur));
        bzla_aigvec_to_sat_tseitin(avmgr, cur->av);

        /* continue synthesizing children for apply and feq nodes if
         * lazy_synthesize is disabled */
        if (!opt_lazy_synth) goto PUSH_CHILDREN;
      }
      else if (bzla_node_is_quantifier(cur))
      {
        cur->av = bzla_aigvec_var(avmgr, bzla_node_bv_get_width(bzla, cur));
        BZLALOG(2, "  synthesized: %s", bzla_util_node2string(cur));
        bzla_aigvec_to_sat_tseitin(avmgr, cur->av);
      }
      /* we stop at function nodes as they will be lazily synthesized and
       * encoded during consistency checking */
      else if (bzla_node_is_fun(cur) && opt_lazy_synth)
      {
        continue;
      }
      else
      {
      PUSH_CHILDREN:
        assert(!opt_lazy_synth || !bzla_node_is_fun(cur));

        bzla_hashint_table_add(cache, cur->id);
        BZLA_PUSH_STACK(exp_stack, cur);
        if (bzla_node_fp_needs_word_blast(bzla, cur))
        {
          wb = bzla_fp_word_blast(bzla, cur);
          BZLA_PUSH_STACK(exp_stack, wb);
        }
        for (j = 1; j <= cur->arity; j++)
        {
          BZLA_PUSH_STACK(exp_stack, cur->e[cur->arity - j]);
        }

        /* synthesize nodes in static_rho of lambda nodes */
        if (bzla_node_is_lambda(cur))
        {
          static_rho = bzla_node_lambda_get_static_rho(cur);
          if (static_rho)
          {
            bzla_iter_hashptr_init(&it, static_rho);
            while (bzla_iter_hashptr_has_next(&it))
            {
              value = it.bucket->data.as_ptr;
              args  = bzla_iter_hashptr_next(&it);
              BZLA_PUSH_STACK(exp_stack, bzla_simplify_exp(bzla, value));
              BZLA_PUSH_STACK(exp_stack, bzla_simplify_exp(bzla, args));
            }
          }
        }
      }
    }
    /* paremterized nodes, argument nodes and functions are not
     * synthesizable */
    else if (!cur->parameterized && !bzla_node_is_args(cur)
             && !bzla_node_is_fun(cur))
    {
      /* FP nodes are now word-blasted. Set AIG vector of FP node to AIG vector
       * of word-blasted bit-vector node. */
      if (bzla_node_fp_needs_word_blast(bzla, cur))
      {
        wb         = bzla_fp_word_blast(bzla, cur);
        invert_av0 = bzla_node_is_inverted(wb);
        av0        = bzla_aigvec_copy(avmgr, bzla_node_real_addr(wb)->av);
        if (invert_av0) bzla_aigvec_invert(avmgr, av0);
        cur->av = av0;
      }
      else
      {
        assert(bzla_node_is_bv(bzla, cur));

        if (!opt_lazy_synth)
        {
          /* due to pushing nodes from static_rho onto 'exp_stack' a strict
           * DFS order is not guaranteed anymore. hence, we have to check
           * if one of the children of 'cur' is not yet synthesized and
           * thus, have to synthesize them before 'cur'. */
          restart = false;
          for (i = 0; i < cur->arity; i++)
          {
            real_e = bzla_node_real_addr(cur->e[i]);
            if (!bzla_node_is_synth(real_e))
            {
              BZLA_PUSH_STACK(exp_stack, cur->e[i]);
              restart = true;
              break;
            }
          }
          if (restart) continue;
        }

        if (cur->arity == 1)
        {
          assert(bzla_node_is_bv_slice(cur));
          invert_av0 = bzla_node_is_inverted(cur->e[0]);
          av0        = bzla_node_real_addr(cur->e[0])->av;
          if (invert_av0) bzla_aigvec_invert(avmgr, av0);
          cur->av = bzla_aigvec_slice(avmgr,
                                      av0,
                                      bzla_node_bv_slice_get_upper(cur),
                                      bzla_node_bv_slice_get_lower(cur));
          if (invert_av0) bzla_aigvec_invert(avmgr, av0);
        }
        else if (cur->arity == 2)
        {
          /* We have to check if the children are in the same memory
           * place if they are in the same memory place. Then we need to
           * allocate memory for the AIG vectors if they are not, then
           * we can invert them in place and invert them back afterwards
           * (only if necessary) .
           */
          is_same_children_mem =
              bzla_node_real_addr(cur->e[0]) == bzla_node_real_addr(cur->e[1]);
          if (is_same_children_mem)
          {
            av0 = BZLA_AIGVEC_NODE(bzla, cur->e[0]);
            av1 = BZLA_AIGVEC_NODE(bzla, cur->e[1]);
          }
          else
          {
            invert_av0 = bzla_node_is_inverted(cur->e[0]);
            av0        = bzla_node_real_addr(cur->e[0])->av;
            if (invert_av0) bzla_aigvec_invert(avmgr, av0);
            invert_av1 = bzla_node_is_inverted(cur->e[1]);
            av1        = bzla_node_real_addr(cur->e[1])->av;
            if (invert_av1) bzla_aigvec_invert(avmgr, av1);
          }
          switch (cur->kind)
          {
            case BZLA_BV_AND_NODE:
              cur->av = bzla_aigvec_and(avmgr, av0, av1);
              break;
            case BZLA_BV_EQ_NODE:
              cur->av = bzla_aigvec_eq(avmgr, av0, av1);
              break;
            case BZLA_BV_ADD_NODE:
              cur->av = bzla_aigvec_add(avmgr, av0, av1);
              break;
            case BZLA_BV_MUL_NODE:
              cur->av = bzla_aigvec_mul(avmgr, av0, av1);
              break;
            case BZLA_BV_ULT_NODE:
              cur->av = bzla_aigvec_ult(avmgr, av0, av1);
              break;
            case BZLA_BV_SLT_NODE:
              cur->av = bzla_aigvec_slt(avmgr, av0, av1);
              break;
            case BZLA_BV_SLL_NODE:
              cur->av = bzla_aigvec_sll(avmgr, av0, av1);
              break;
            case BZLA_BV_SRL_NODE:
              cur->av = bzla_aigvec_srl(avmgr, av0, av1);
              break;
            case BZLA_BV_UDIV_NODE:
              cur->av = bzla_aigvec_udiv(avmgr, av0, av1);
              break;
            case BZLA_BV_UREM_NODE:
              cur->av = bzla_aigvec_urem(avmgr, av0, av1);
              break;
            default:
              assert(cur->kind == BZLA_BV_CONCAT_NODE);
              cur->av = bzla_aigvec_concat(avmgr, av0, av1);
              break;
          }

          if (is_same_children_mem)
          {
            bzla_aigvec_release_delete(avmgr, av0);
            bzla_aigvec_release_delete(avmgr, av1);
          }
          else
          {
            if (invert_av0) bzla_aigvec_invert(avmgr, av0);
            if (invert_av1) bzla_aigvec_invert(avmgr, av1);
          }
          if (!opt_lazy_synth) bzla_aigvec_to_sat_tseitin(avmgr, cur->av);
        }
        else
        {
          assert(cur->arity == 3);

          if (bzla_node_is_bv_cond(cur))
          {
            is_same_children_mem =
                bzla_node_real_addr(cur->e[0]) == bzla_node_real_addr(cur->e[1])
                || bzla_node_real_addr(cur->e[0])
                       == bzla_node_real_addr(cur->e[2])
                || bzla_node_real_addr(cur->e[1])
                       == bzla_node_real_addr(cur->e[2]);
            if (is_same_children_mem)
            {
              av0 = BZLA_AIGVEC_NODE(bzla, cur->e[0]);
              av1 = BZLA_AIGVEC_NODE(bzla, cur->e[1]);
              av2 = BZLA_AIGVEC_NODE(bzla, cur->e[2]);
            }
            else
            {
              invert_av0 = bzla_node_is_inverted(cur->e[0]);
              av0        = bzla_node_real_addr(cur->e[0])->av;
              if (invert_av0) bzla_aigvec_invert(avmgr, av0);
              invert_av1 = bzla_node_is_inverted(cur->e[1]);
              av1        = bzla_node_real_addr(cur->e[1])->av;
              if (invert_av1) bzla_aigvec_invert(avmgr, av1);
              invert_av2 = bzla_node_is_inverted(cur->e[2]);
              av2        = bzla_node_real_addr(cur->e[2])->av;
              if (invert_av2) bzla_aigvec_invert(avmgr, av2);
            }
            cur->av = bzla_aigvec_cond(avmgr, av0, av1, av2);
            if (is_same_children_mem)
            {
              bzla_aigvec_release_delete(avmgr, av2);
              bzla_aigvec_release_delete(avmgr, av1);
              bzla_aigvec_release_delete(avmgr, av0);
            }
            else
            {
              if (invert_av0) bzla_aigvec_invert(avmgr, av0);
              if (invert_av1) bzla_aigvec_invert(avmgr, av1);
              if (invert_av2) bzla_aigvec_invert(avmgr, av2);
            }
          }
        }
      }
      assert(cur->av);
      BZLALOG(2, "  synthesized: %s", bzla_util_node2string(cur));
      bzla_aigvec_to_sat_tseitin(avmgr, cur->av);
    }
  }
  BZLA_RELEASE_STACK(exp_stack);
  bzla_hashint_table_delete(cache);

  if (count > 0 && bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) > 3)
    BZLA_MSG(
        bzla->msg, 3, "synthesized %u expressions into AIG vectors", count);

  bzla->time.synth_exp += bzla_util_time_stamp() - start;
}

/* forward assumptions to the SAT solver */
void
bzla_add_again_assumptions(Bzla *bzla)
{
  assert(bzla);
  assert(bzla_dbg_check_assumptions_simp_free(bzla));

  int32_t i;
  BzlaNode *exp, *cur, *e;
  BzlaNodePtrStack stack;
  BzlaPtrHashTable *assumptions;
  BzlaPtrHashTableIterator it;
  BzlaAIG *aig;
  BzlaSATMgr *smgr;
  BzlaAIGMgr *amgr;
  BzlaIntHashTable *mark;

  amgr = bzla_get_aig_mgr(bzla);
  smgr = bzla_get_sat_mgr(bzla);

  BZLA_INIT_STACK(bzla->mm, stack);
  mark = bzla_hashint_table_new(bzla->mm);

  assumptions = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    exp = bzla_iter_hashptr_next(&it);
    assert(!bzla_node_is_simplified(exp));

    if (bzla_node_is_inverted(exp) || !bzla_node_is_bv_and(exp))
    {
      if (!bzla_hashptr_table_get(assumptions, exp))
        bzla_hashptr_table_add(assumptions, exp);
    }
    else
    {
      BZLA_PUSH_STACK(stack, exp);
      while (!BZLA_EMPTY_STACK(stack))
      {
        cur = BZLA_POP_STACK(stack);
        assert(!bzla_node_is_inverted(cur));
        assert(bzla_node_is_bv_and(cur));
        if (bzla_hashint_table_contains(mark, cur->id)) continue;
        bzla_hashint_table_add(mark, cur->id);
        for (i = 0; i < 2; i++)
        {
          e = cur->e[i];
          if (!bzla_node_is_inverted(e) && bzla_node_is_bv_and(e))
            BZLA_PUSH_STACK(stack, e);
          else if (!bzla_hashptr_table_get(assumptions, e))
            bzla_hashptr_table_add(assumptions, e);
        }
      }
    }
  }

  bzla_iter_hashptr_init(&it, assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(bzla_node_bv_get_width(bzla, cur) == 1);
    assert(!bzla_node_is_simplified(cur));
    aig = exp_to_aig(bzla, cur);
    bzla_aig_to_sat(amgr, aig);
    if (aig == BZLA_AIG_TRUE) continue;
    if (bzla_sat_is_initialized(smgr))
    {
      assert(bzla_aig_get_cnf_id(aig) != 0);
      bzla_sat_assume(smgr, bzla_aig_get_cnf_id(aig));
    }
    bzla_aig_release(amgr, aig);
  }
  /* assert constraints added during word-blasting */
  bzla_fp_word_blaster_add_additional_assertions(bzla);

  BZLA_RELEASE_STACK(stack);
  bzla_hashptr_table_delete(assumptions);
  bzla_hashint_table_delete(mark);
}

#if 0
/* updates SAT assignments, reads assumptions and
 * returns if an assignment has changed
 */
static int32_t
update_sat_assignments (Bzla * bzla)
{
  assert (bzla);

  BzlaSATMgr *smgr;

  smgr = bzla_get_sat_mgr (bzla);
  add_again_assumptions (bzla);
#ifndef NDEBUG
  int32_t result;
  result = timed_sat_sat (bzla, -1);
  assert (result == BZLA_SAT);
#else
  (void) timed_sat_sat (bzla, -1);
#endif
  return bzla_sat_changed (smgr);
}
#endif

static bool
is_fp_logic(Bzla *bzla)
{
  BzlaNodeKind fp_ops[28] = {
      BZLA_RM_EQ_NODE,       BZLA_FP_ABS_NODE,        BZLA_FP_IS_INF_NODE,
      BZLA_FP_IS_NAN_NODE,   BZLA_FP_IS_NEG_NODE,     BZLA_FP_IS_NORM_NODE,
      BZLA_FP_IS_POS_NODE,   BZLA_FP_IS_SUBNORM_NODE, BZLA_FP_IS_ZERO_NODE,
      BZLA_FP_NEG_NODE,      BZLA_FP_TO_FP_BV_NODE,   BZLA_FP_EQ_NODE,
      BZLA_FP_LTE_NODE,      BZLA_FP_LT_NODE,         BZLA_FP_MIN_NODE,
      BZLA_FP_MAX_NODE,      BZLA_FP_SQRT_NODE,       BZLA_FP_REM_NODE,
      BZLA_FP_RTI_NODE,      BZLA_FP_TO_SBV_NODE,     BZLA_FP_TO_UBV_NODE,
      BZLA_FP_TO_FP_FP_NODE, BZLA_FP_TO_FP_SBV_NODE,  BZLA_FP_TO_FP_UBV_NODE,
      BZLA_FP_ADD_NODE,      BZLA_FP_MUL_NODE,        BZLA_FP_DIV_NODE,
      BZLA_FP_FMA_NODE};
  for (uint32_t i = 0; i < 28; i++)
  {
    if (bzla->ops[fp_ops[i]].cur > 0) return true;
  }
  return false;
}

int32_t
bzla_check_sat(Bzla *bzla, int32_t lod_limit, int32_t sat_limit)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
         || bzla->bzla_sat_bzla_called == 0);

#ifndef NDEBUG
  bool check = true;
#endif
  double start, delta;
  BzlaSolverResult res;
  uint32_t engine;

  start = bzla_util_time_stamp();

  BZLA_MSG(bzla->msg, 1, "calling SAT");

  if (bzla_opt_get(bzla, BZLA_OPT_FUN_PREPROP))
  {
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_NPROPS)
        == bzla_opt_get_dflt(bzla, BZLA_OPT_PROP_NPROPS))
    {
      bzla_opt_set(bzla, BZLA_OPT_PROP_NPROPS, 10000);
    }
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_NUPDATES)
        == bzla_opt_get_dflt(bzla, BZLA_OPT_PROP_NUPDATES))
    {
      bzla_opt_set(bzla, BZLA_OPT_PROP_NUPDATES, 2000000);
    }
  }

  if (bzla->valid_assignments == 1) bzla_reset_incremental_usage(bzla);

  /* 'bzla->assertions' contains all assertions that were asserted in context
   * levels > 0 (bitwuzla_push). We assume all these assertions on every
   * bzla_check_sat call since these assumptions are valid until the
   * corresponding context is popped. */
  if (BZLA_COUNT_STACK(bzla->assertions) > 0)
  {
    assert(BZLA_COUNT_STACK(bzla->assertions_trail) > 0
           || bzla_opt_get(bzla, BZLA_OPT_PRODUCE_UNSAT_CORES));
    uint32_t i;
    for (i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
    {
      bzla_assume_exp(bzla, BZLA_PEEK_STACK(bzla->assertions, i));
    }
  }

  // FIXME: this is temporary until we support FP handling with LOD for Lambdas
  if (is_fp_logic(bzla))
  {
    BZLA_MSG(bzla->msg, 1, "found FP expressions, disable lambda extraction");
    bzla_opt_set(bzla, BZLA_OPT_PP_EXTRACT_LAMBDAS, 0);
  }

#ifndef NDEBUG
  // NOTE: disable checking if quantifiers present for now (not supported yet)
  if (bzla->quantifiers->count) check = false;

  Bzla *uclone = 0;
  if (check && bzla_opt_get(bzla, BZLA_OPT_CHECK_UNCONSTRAINED)
      && bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)
      && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
      && !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL)
      && !bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS)
      && !bzla_opt_get(bzla, BZLA_OPT_PRINT_DIMACS))
  {
    uclone = bzla_clone(bzla);
    bzla_opt_set(uclone, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION, 0);
    bzla_opt_set(uclone, BZLA_OPT_CHECK_UNCONSTRAINED, 0);
    bzla_opt_set(uclone, BZLA_OPT_CHECK_MODEL, 0);
    bzla_opt_set(uclone, BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS, 0);
    bzla_set_term(uclone, 0, 0);

    bzla_opt_set(uclone, BZLA_OPT_ENGINE, BZLA_ENGINE_FUN);
    if (uclone->slv)
    {
      uclone->slv->api.delet(uclone->slv);
      uclone->slv = 0;
    }
  }
  BzlaCheckModelContext *chkmodel = 0;
  if (check && bzla_opt_get(bzla, BZLA_OPT_CHECK_MODEL))
  {
    chkmodel = bzla_check_model_init(bzla);
  }
#endif

#ifndef NBZLALOG
  bzla_opt_log_opts(bzla);
#endif

  /* set option based on formula characteristics */

  /* eliminate lambdas (define-fun) in the QF_BV case */
  if (bzla->ufs->count == 0 && bzla->feqs->count == 0
      && bzla->lambdas->count > 0
      && !bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE))
  {
    BZLA_MSG(bzla->msg,
             1,
             "no UFs or function equalities, enable beta-reduction=all");
    bzla_opt_set(bzla, BZLA_OPT_PP_BETA_REDUCE, BZLA_BETA_REDUCE_FUN);
  }

  /* Lambdas are not supported with FP right now since we can't handle FP
   * expressions in bzla_eval_exp yet. */
  if (is_fp_logic(bzla))
  {
    bzla_opt_set(bzla, BZLA_OPT_PP_BETA_REDUCE, BZLA_BETA_REDUCE_FUN);
  }

  // FIXME (ma): not sound with slice elimination. see red-vsl.proof3106.smt2
  /* disabling slice elimination is better on QF_ABV and BV */
  if (bzla->ufs->count > 0)
  {
    BZLA_MSG(bzla->msg,
             1,
             "found %s, disable slice elimination",
             bzla->ufs->count > 0 ? "UFs" : "quantifiers");
    // TODO: check if this is still the case
    bzla_opt_set(bzla, BZLA_OPT_PP_ELIMINATE_EXTRACTS, 0);
  }

  /* set options for quantifiers */
  if (bzla->quantifiers->count > 0 && bzla->bzla_sat_bzla_called == 0)
  {
    bzla_opt_set(bzla, BZLA_OPT_INCREMENTAL, 1);
    bzla_opt_set(bzla, BZLA_OPT_PRODUCE_MODELS, 1);
    bzla_opt_set(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION, 0);
  }

  res = bzla_simplify(bzla);

  if (res != BZLA_RESULT_UNSAT)
  {
    engine = bzla_opt_get(bzla, BZLA_OPT_ENGINE);

    if (!bzla->slv)
    {
      /* these engines work on QF_BV only */
      if (engine == BZLA_ENGINE_SLS && bzla->ufs->count == 0
          && bzla->feqs->count == 0)
      {
        assert(bzla->lambdas->count == 0
               || bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE));
        BZLA_ABORT(bzla->quantifiers->count,
                   "Quantifiers not supported for -E sls");
        bzla->slv = bzla_new_sls_solver(bzla);
      }
      else if (engine == BZLA_ENGINE_PROP && bzla->ufs->count == 0
               && bzla->feqs->count == 0)
      {
        assert(bzla->lambdas->count == 0
               || bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE));
        BZLA_ABORT(bzla->quantifiers->count,
                   "Quantifiers not supported for -E prop");
        bzla->slv = bzla_new_prop_solver(bzla);
      }
      else if (engine == BZLA_ENGINE_AIGPROP && bzla->ufs->count == 0
               && bzla->feqs->count == 0)
      {
        assert(bzla->lambdas->count == 0
               || bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE));
        BZLA_ABORT(bzla->quantifiers->count,
                   "Quantifiers not supported for -E aigprop");
        bzla->slv = bzla_new_aigprop_solver(bzla);
      }
      else
      {
        bzla->slv = bzla_new_fun_solver(bzla);
        // TODO (ma): make options for lod_limit and sat_limit
        BZLA_FUN_SOLVER(bzla)->lod_limit = lod_limit;
        BZLA_FUN_SOLVER(bzla)->sat_limit = sat_limit;
      }
    }

    if (bzla->quantifiers->count > 0)
    {
      if (!bzla->qslv)
      {
        bzla->qslv = bzla_new_quantifier_solver(bzla);
      }
      res = bzla->qslv->api.sat(bzla->qslv);
    }
    else
    {
      assert(bzla->slv);
      res = bzla->slv->api.sat(bzla->slv);
    }
  }
  bzla->last_sat_result = res;
  bzla->bzla_sat_bzla_called++;
  bzla->valid_assignments = 1;

  if (bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS) && res == BZLA_RESULT_SAT
      && bzla->quantifiers->count == 0)
  {
    switch (bzla_opt_get(bzla, BZLA_OPT_ENGINE))
    {
      case BZLA_ENGINE_SLS:
      case BZLA_ENGINE_PROP:
      case BZLA_ENGINE_AIGPROP:
        bzla->slv->api.generate_model(
            bzla->slv, bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS) == 2, false);
        break;
      default:
        bzla->slv->api.generate_model(
            bzla->slv, bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS) == 2, true);
    }
  }

#ifndef NDEBUG
  if (uclone)
  {
    assert(bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION));
    assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2);
    assert(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
    assert(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS));
    BzlaSolverResult ucres = bzla_check_sat(uclone, -1, -1);
    assert(res == ucres);
    bzla_delete(uclone);
  }

  if (chkmodel)
  {
    if (res == BZLA_RESULT_SAT
        && !bzla_opt_get(bzla, BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION))
    {
      bzla_check_model(chkmodel);
    }
    bzla_check_model_delete(chkmodel);
  }
#endif

#ifndef NDEBUG
  if (check && bzla_opt_get(bzla, BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS)
      && !bzla->inconsistent && bzla->last_sat_result == BZLA_RESULT_UNSAT)
    bzla_check_failed_assumptions(bzla);
#endif

  delta = bzla_util_time_stamp() - start;

  BZLA_MSG(bzla->msg,
           1,
           "SAT call %d returned %d in %.3f seconds",
           bzla->bzla_sat_bzla_called + 1,
           res,
           delta);

  bzla->time.sat += delta;

  return res;
}

static bool
is_valid_argument(Bzla *bzla, BzlaNode *exp)
{
  exp = bzla_node_real_addr(exp);
  if (bzla_node_is_fun(bzla_simplify_exp(bzla, exp))) return false;
  if (bzla_node_is_array(bzla_simplify_exp(bzla, exp))) return false;
  /* scope of bound parmaters already closed (cannot be used anymore) */
  if (bzla_node_is_param(exp) && bzla_node_param_is_bound(exp)) return false;
  return true;
}

int32_t
bzla_fun_sort_check(Bzla *bzla, BzlaNode *args[], uint32_t argc, BzlaNode *fun)
{
  (void) bzla;
  assert(bzla);
  assert(argc > 0);
  assert(args);
  assert(fun);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_fun(bzla_simplify_exp(bzla, fun)));
  assert(argc == bzla_node_fun_get_arity(bzla, fun));

  uint32_t i;
  int32_t pos;
  BzlaSortId sort;
  BzlaTupleSortIterator it;

  assert(bzla_sort_is_tuple(
      bzla, bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun))));
  bzla_iter_tuple_sort_init(
      &it, bzla, bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun)));
  for (i = 0, pos = -1; i < argc; i++)
  {
    assert(bzla_iter_tuple_sort_has_next(&it));
    sort = bzla_iter_tuple_sort_next(&it);
    /* NOTE: we do not allow functions or arrays as arguments yet */
    if (!is_valid_argument(bzla, args[i])
        || sort != bzla_node_get_sort_id(args[i]))
    {
      pos = i;
      break;
    }
  }
  return pos;
}

static BzlaAIG *
exp_to_aig(Bzla *bzla, BzlaNode *exp)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *av;
  BzlaAIG *result;

  assert(bzla);
  assert(exp);
  assert(bzla_node_bv_get_width(bzla, exp) == 1);
  assert(!bzla_node_real_addr(exp)->parameterized);

  amgr = bzla_get_aig_mgr(bzla);

  bzla_synthesize_exp(bzla, exp, 0);
  av = bzla_node_real_addr(exp)->av;

  assert(av);
  assert(av->width == 1);

  result = av->aigs[0];

  if (bzla_node_is_inverted(exp))
    result = bzla_aig_not(amgr, result);
  else
    result = bzla_aig_copy(amgr, result);

  return result;
}

BzlaAIGVec *
bzla_exp_to_aigvec(Bzla *bzla, BzlaNode *exp, BzlaPtrHashTable *backannotation)
{
  BzlaAIGVecMgr *avmgr;
  BzlaAIGVec *result;

  assert(exp);

  avmgr = bzla->avmgr;

  bzla_synthesize_exp(bzla, exp, backannotation);
  result = bzla_node_real_addr(exp)->av;
  assert(result);

  if (bzla_node_is_inverted(exp))
    result = bzla_aigvec_not(avmgr, result);
  else
    result = bzla_aigvec_copy(avmgr, result);

  return result;
}
