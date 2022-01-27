/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaslvprop.h"

#include <math.h>

#include "bzlaaigvec.h"
#include "bzlabv.h"
#include "bzlabvprop.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlalsutils.h"
#include "bzlamodel.h"
#include "bzlanode.h"
#include "bzlaopt.h"
#include "bzlaprintmodel.h"
#include "bzlaproputils.h"
#include "bzlaslsutils.h"
#include "dumper/bzladumpsmt.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahash.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_PROP_MAXSTEPS_CFACT 100
#define BZLA_PROP_MAXSTEPS(i) \
  (BZLA_PROP_MAXSTEPS_CFACT * ((i) &1u ? 1 : 1 << ((i) >> 1)))

#define BZLA_PROP_SELECT_CFACT 20

/*------------------------------------------------------------------------*/

static BzlaNode *
select_constraint(Bzla *bzla, uint32_t nmoves)
{
  assert(bzla);

  BzlaNode *res, *cur;
  BzlaPropSolver *slv;
  BzlaIntHashTableIterator it;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);
  assert(slv->roots);
  assert(slv->roots->count);

#ifndef NDEBUG
  BzlaPtrHashTableIterator pit;
  BzlaNode *root;
  bzla_iter_hashptr_init(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_init(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    root = bzla_iter_hashptr_next(&pit);
    if (bzla_bv_is_false(bzla_model_get_bv(bzla, root)))
      assert(bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root)));
    else
      assert(!bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root)));
  }
#endif

  res = 0;

  if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
  {
    assert(slv->score);

    int32_t *selected;
    double value, max_value, score;
    max_value = 0.0;
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it))
    {
      selected = &slv->roots->data[it.cur_pos].as_int;
      cur      = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));

      assert(bzla_hashint_map_contains(slv->score, bzla_node_get_id(cur)));
      score = bzla_hashint_map_get(slv->score, bzla_node_get_id(cur))->as_dbl;
      assert(score < 1.0);
      value = score + BZLA_PROP_SELECT_CFACT * sqrt(log(*selected) / nmoves);

      if (!res || value > max_value)
      {
        res       = cur;
        max_value = value;
        *selected += 1;
      }
    }
  }
  else
  {
    size_t j, r;

    j = 0;
    r = bzla_rng_pick_rand(bzla->rng, 0, slv->roots->count - 1);
    bzla_iter_hashint_init(&it, slv->roots);
    while (bzla_iter_hashint_has_next(&it) && j <= r)
    {
      res = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));
      j += 1;
    }
    assert(res);
    assert(!bzla_node_is_bv_const(res));
  }

  assert(res);
  assert(bzla_bv_is_zero(bzla_model_get_bv(bzla, res)));

  BZLALOG(1, "");
  BZLALOG(1, "***** select constraint: %s", bzla_util_node2string(res));
  BZLALOG(1, "--------------------------------------------------------------");

  return res;
}

static void
print_progress(BzlaPropSolver *slv)
{
  uint64_t num_total_roots, num_unsat_roots;
  Bzla *bzla;

  bzla            = slv->bzla;
  num_total_roots = bzla->assumptions->count
                    + bzla->synthesized_constraints->count
                    + bzla->unsynthesized_constraints->count;

  num_unsat_roots = slv->roots ? slv->roots->count : 0;

  BZLA_MSG(bzla->msg,
           1,
           "%zu/%zu roots satisfied (%.1f%%), "
           "moves: %u, "
           "propagations: %zu, "
           "model updates: %zu",
           num_total_roots - num_unsat_roots,
           num_total_roots,
           (double) (num_total_roots - num_unsat_roots) / num_total_roots * 100,
           slv->stats.moves,
           slv->stats.props,
           slv->stats.updates);
}

static bool
move(Bzla *bzla, uint64_t nprops)
{
  assert(bzla);

  BZLALOG(1, "");

  BzlaNode *root, *input;
  BzlaBitVector *bvroot, *assignment;
  BzlaPropSolver *slv;
  BzlaIntHashTable *exps;
  BzlaPropEntailInfo prop;
  int32_t idx_x;
  uint64_t props;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);
  assert(BZLA_EMPTY_STACK(slv->prop_path));

  BZLALOG(1, "*** move %u", slv->stats.moves + 1);
  BZLALOG(1, "unsatisfied roots: %u", slv->roots->count);
  BZLALOG(1,
          "satisfied roots:   %u",
          bzla->assumptions->count + bzla->synthesized_constraints->count
              + bzla->unsynthesized_constraints->count - slv->roots->count);
  BZLALOG(1, "propagations: %zu", slv->stats.props);
  BZLALOG(1, "moves skipped: %zu", slv->stats.moves_skipped);

  bvroot = 0;
  do
  {
    if (bvroot) bzla_bv_free(bzla->mm, bvroot);
    if (nprops && slv->stats.props >= nprops) goto DONE;

#ifndef NDEBUG
    bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->prop_path);
#endif

#ifndef NBZLALOG
    BZLALOG(1, "entailed propagations: %u", BZLA_COUNT_STACK(slv->toprop));
    for (size_t i = 0; i < BZLA_COUNT_STACK(slv->toprop); i++)
    {
      BzlaPropEntailInfo *p = &slv->toprop.start[i];
      char *bvprop          = bzla_bv_to_char(bzla->mm, p->bvexp);
      BZLALOG(1, "  %s: %s", bzla_util_node2string(p->exp), bvprop);
      bzla_mem_freestr(bzla->mm, bvprop);
    }
#endif

    if (BZLA_EMPTY_STACK(slv->toprop))
    {
      root   = select_constraint(bzla, slv->stats.moves);
      bvroot = bzla_bv_one(bzla->mm, 1);
      idx_x  = -1;
    }
    else
    {
      prop   = BZLA_POP_STACK(slv->toprop);
      root   = prop.exp;
      bvroot = bzla_bv_copy(bzla->mm, prop.bvexp);
      idx_x  = prop.idx_x;
    }

    props = bzla_proputils_select_move_prop(
        bzla, root, bvroot, idx_x, &input, &assignment);
    slv->stats.props += props;
    if (idx_x != -1) slv->stats.props_entailed += props;
  } while (!input);

  assert(assignment);

  bzla_bv_free(bzla->mm, bvroot);

#ifndef NBZLALOG
  char *a;
  BzlaBitVector *ass;
  ass = (BzlaBitVector *) bzla_model_get_bv(bzla, input);
  a   = bzla_bv_to_char(bzla->mm, ass);
  BZLALOG(1, "");
  BZLALOG(1, "move");
  BZLALOG(1,
          "  input: %s%s (parents: %u)",
          bzla_node_is_regular(input) ? "" : "-",
          bzla_util_node2string(input),
          bzla_node_real_addr(input)->parents);
  BZLALOG(1, "  prev. assignment: %s", a);
  bzla_mem_freestr(bzla->mm, a);
  a = bzla_bv_to_char(bzla->mm, assignment);
  BZLALOG(1, "  new   assignment: %s", a);
  bzla_mem_freestr(bzla->mm, a);
#endif

  exps = bzla_hashint_map_new(bzla->mm);
  assert(bzla_node_is_regular(input));
  bzla_hashint_map_add(exps, input->id)->as_ptr = assignment;
  bzla_lsutils_update_cone(
      bzla,
      bzla->bv_model,
      slv->roots,
      bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT) ? slv->score : 0,
      exps,
      true,
      &slv->stats.updates,
      &slv->time.update_cone,
      &slv->time.update_cone_reset,
      &slv->time.update_cone_model_gen,
      &slv->time.update_cone_compute_score);
  bzla_hashint_map_delete(exps);

#ifndef NDEBUG
  size_t cnt;
  BzlaBitVector *bvass, *bvtarget;
  BzlaNode *n;
  cnt = BZLA_COUNT_STACK(slv->prop_path);
  size_t i;
  for (i = 0; i < cnt; i++)
  {
    n = BZLA_PEEK_STACK(slv->prop_path, cnt - 1 - i).exp;
    assert(bzla_node_is_regular(n));
    bvass    = (BzlaBitVector *) bzla_model_get_bv(bzla, n);
    bvtarget = BZLA_PEEK_STACK(slv->prop_path, cnt - 1 - i).bvexp;
    if (bzla_bv_compare(bvass, bvtarget)) break;
  }
  BZLALOG(1, "  matching target values: %u", i);
#endif

  slv->stats.moves += 1;
  if (idx_x != -1)
  {
    slv->stats.moves_entailed += 1;
    slv->stats.fixed_conf += 1;
  }
  bzla_bv_free(bzla->mm, assignment);

DONE:
#ifndef NDEBUG
  bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->prop_path);
#endif
  return true;
}

/*------------------------------------------------------------------------*/

static BzlaPropSolver *
clone_prop_solver(Bzla *clone, BzlaPropSolver *slv, BzlaNodeMap *exp_map)
{
  assert(clone);
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);

  BzlaPropSolver *res;

  (void) exp_map;

  BZLA_NEW(clone->mm, res);
  memcpy(res, slv, sizeof(BzlaPropSolver));

  res->bzla  = clone;
  res->roots = bzla_hashint_map_clone(clone->mm, slv->roots, 0, 0);
  res->score =
      bzla_hashint_map_clone(clone->mm, slv->score, bzla_clone_data_as_dbl, 0);
  // TODO clone const_bits

  bzla_proputils_clone_prop_info_stack(
      clone->mm, &slv->toprop, &res->toprop, exp_map);
#ifndef NDEBUG
  bzla_proputils_clone_prop_info_stack(
      clone->mm, &slv->prop_path, &res->prop_path, exp_map);
#endif
  return res;
}

static void
delete_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->domains);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  BzlaIntHashTableIterator it;

  if (slv->score) bzla_hashint_map_delete(slv->score);
  if (slv->roots) bzla_hashint_map_delete(slv->roots);

  bzla_iter_hashint_init(&it, slv->domains);
  while (bzla_iter_hashint_has_next(&it))
  {
    bzla_bvdomain_free(slv->bzla->mm, bzla_iter_hashint_next_data(&it)->as_ptr);
  }
  bzla_hashint_map_delete(slv->domains);

  assert(BZLA_EMPTY_STACK(slv->toprop));
  BZLA_RELEASE_STACK(slv->toprop);
#ifndef NDEBUG
  assert(BZLA_EMPTY_STACK(slv->prop_path));
  BZLA_RELEASE_STACK(slv->prop_path);
#endif
  BZLA_DELETE(slv->bzla->mm, slv);
}

void
bzla_prop_solver_init_domains(Bzla *bzla,
                              BzlaIntHashTable *domains,
                              BzlaNode *root)
{
  assert(bzla);
  assert(domains);
  assert(root);

  uint32_t i, bw, idx;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaHashTableData *data;
  BzlaMemMgr *mm;
  BzlaAIGVec *av;
  BzlaBvDomain *domain, *invdomain;
  bool opt_prop_const_bits;

  mm                  = bzla->mm;
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS) != 0;

  cache = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, visit);

  BZLA_PUSH_STACK(visit, root);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    if (bzla_hashint_map_contains(domains, real_cur->id)) continue;

    /* We do post order traversal even though it is not strictly necessary for
     * now, but it will be in the future (as soon as we use the propagators to
     * init the domains rather than the the AIG layer). */
    data = bzla_hashint_map_get(cache, real_cur->id);
    if (!data)
    {
      bzla_hashint_map_add(cache, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);
      if (!bzla_lsutils_is_leaf_node(real_cur))
      {
        for (i = 0; i < real_cur->arity; i++)
          BZLA_PUSH_STACK(visit, real_cur->e[i]);
      }
    }
    else if (!data->flag)
    {
      assert(!bzla_node_is_fun(real_cur));
      assert(!bzla_node_is_args(real_cur));
      assert(!real_cur->parameterized);
      data->flag = true;

      bw     = bzla_node_bv_get_width(bzla, real_cur);
      domain = bzla_bvdomain_new_init(mm, bw);
      bzla_hashint_map_add(domains, real_cur->id)->as_ptr = domain;
      /* inverted nodes are additionally stored with negative id */
      invdomain = bzla_bvdomain_new_init(mm, bw);
      bzla_hashint_map_add(domains, -real_cur->id)->as_ptr = invdomain;

      if (opt_prop_const_bits)
      {
        assert(bzla_node_is_synth(real_cur));
        assert(real_cur->av->width == bw);
        av = real_cur->av;
        bw = av->width;
        for (i = 0; i < bw; i++)
        {
          idx = bw - 1 - i;
          if (bzla_aig_is_const(av->aigs[i]))
          {
            bzla_bvdomain_fix_bit(domain, idx, bzla_aig_is_true(av->aigs[i]));
            assert(invdomain);
            bzla_bvdomain_fix_bit(
                invdomain, idx, bzla_aig_is_false(av->aigs[i]));
            BZLA_PROP_SOLVER(bzla)->stats.fixed_bits++;
          }
        }
        BZLA_PROP_SOLVER(bzla)->stats.total_bits += bw;
      }
    }
  }
  bzla_hashint_map_delete(cache);
  BZLA_RELEASE_STACK(visit);
}

static bool
update_domain(Bzla *bzla,
              BzlaIntHashTable *domains,
              const BzlaNode *n,
              BzlaBvDomain *old_domain,
              BzlaBvDomain *new_domain)
{
  assert(domains);
  assert(n);
  assert(old_domain);

  int32_t id;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;

  if (!new_domain) return false;
  if (bzla_bvdomain_is_equal(old_domain, new_domain)) return false;

  mm = bzla->mm;
  id = bzla_node_get_id(bzla_node_real_addr(n));
  d  = bzla_hashint_map_get(domains, id);
  assert(d);
  bzla_bvdomain_free(mm, d->as_ptr);
  d->as_ptr = bzla_bvdomain_copy(mm, new_domain);

  d = bzla_hashint_map_get(domains, -id);
  assert(d);
  bzla_bvdomain_free(mm, d->as_ptr);
  d->as_ptr = bzla_bvdomain_not(mm, new_domain);
  return true;
}

static void
propagate_domains(Bzla *bzla,
                  BzlaNode *root,
                  BzlaIntHashTable *domains,
                  BzlaIntHashTable *cache)
{
  int32_t id, child_id;
  uint32_t i;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack visit;
  BzlaBvDomain *d_cur, *d_res_cur, *d_e[3], *d_res_e[3];
  BzlaMemMgr *mm;
  BzlaPropSolver *slv;

  slv = BZLA_PROP_SOLVER(bzla);
  mm  = bzla->mm;
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, root);

  do
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    id       = bzla_node_get_id(real_cur);

    if (bzla_hashint_table_contains(cache, id))
    {
      continue;
    }

    bzla_hashint_table_add(cache, id);

    assert(bzla_hashint_map_contains(domains, id));
    assert(bzla_hashint_map_contains(domains, -id));
    d_cur = bzla_hashint_map_get(domains, id)->as_ptr;
    assert(d_cur);

    for (i = 0; i < real_cur->arity; ++i)
    {
      child_id = bzla_node_get_id(real_cur->e[i]);
      assert(bzla_hashint_map_contains(domains, child_id));
      d_e[i]     = bzla_hashint_map_get(domains, child_id)->as_ptr;
      d_res_e[i] = 0;
    }
    d_res_cur = 0;

    if (bzla_node_is_bv_slice(real_cur))
    {
      bzla_bvprop_slice(mm,
                        d_e[0],
                        d_cur,
                        bzla_node_bv_slice_get_upper(real_cur),
                        bzla_node_bv_slice_get_lower(real_cur),
                        &d_res_e[0],
                        &d_res_cur);
    }
    else if (bzla_node_is_bv_and(real_cur))
    {
      bzla_bvprop_and(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_eq(real_cur))
    {
      bzla_bvprop_eq(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_add(real_cur))
    {
      bzla_bvprop_add(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_mul(real_cur))
    {
      bzla_bvprop_mul(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_ult(real_cur))
    {
      bzla_bvprop_ult(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_sll(real_cur))
    {
      bzla_bvprop_sll(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_srl(real_cur))
    {
      bzla_bvprop_srl(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_udiv(real_cur))
    {
      bzla_bvprop_udiv(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_urem(real_cur))
    {
      bzla_bvprop_urem(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_concat(real_cur))
    {
      bzla_bvprop_concat(
          mm, d_e[0], d_e[1], d_cur, &d_res_e[0], &d_res_e[1], &d_res_cur);
    }
    else if (bzla_node_is_bv_cond(real_cur))
    {
      bzla_bvprop_cond(mm,
                       d_e[1],
                       d_e[2],
                       d_cur,
                       d_e[0],
                       &d_res_e[1],
                       &d_res_e[2],
                       &d_res_cur,
                       &d_res_e[0]);
    }

#ifndef NDEBUG
    if (d_res_cur)
    {
      assert(bzla_bvdomain_is_valid(mm, d_res_cur));
    }
    for (i = 0; i < real_cur->arity; ++i)
    {
      if (d_res_e[i])
      {
        assert(bzla_bvdomain_is_valid(mm, d_res_e[i]));
      }
    }
#endif

    if (update_domain(bzla, domains, real_cur, d_cur, d_res_cur))
    {
      ++slv->stats.updated_domains;
    }

    if (d_res_cur)
    {
      bzla_bvdomain_free(mm, d_res_cur);
    }

    for (i = 0; i < real_cur->arity; ++i)
    {
      if (update_domain(bzla, domains, real_cur->e[i], d_e[i], d_res_e[i]))
      {
        ++slv->stats.updated_domains_children;
      }
      if (d_res_e[i])
      {
        bzla_bvdomain_free(mm, d_res_e[i]);
      }

      BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
  } while (!BZLA_EMPTY_STACK(visit));

  BZLA_RELEASE_STACK(visit);
}

/* Note: We only want to synthesize the constraints but don't want to add them
 * to the SAT solver. Hence, we do not call
 * bzla_process_unsynthesized_constraints, but use this function.
 */
static void
synthesize_constraints(Bzla *bzla)
{
  BzlaNode *cur;
  BzlaAIGVec *av;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    bzla_synthesize_exp(bzla, cur, 0);
    av = bzla_node_real_addr(cur)->av;
    assert(av->width == 1);

    if ((bzla_node_is_inverted(cur) && bzla_aig_is_true(av->aigs[0]))
        || (bzla_node_is_regular(cur) && bzla_aig_is_false(av->aigs[0])))
    {
      bzla->found_constraint_false = true;
      break;
    }
  }

  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    bzla_synthesize_exp(bzla, cur, 0);
  }
}

/* This is an extra function in order to be able to test completeness
 * via test suite. */
int32_t
bzla_prop_solver_sat(Bzla *bzla)
{
  assert(bzla);

  double start;
  uint32_t j, max_steps;
  int32_t sat_result;
  uint32_t nprops, opt_prop_const_bits, opt_verbosity = 0;
  uint64_t progress_steps, progress_steps_inc, nupdates;
  BzlaNode *root, *not_root;
  BzlaPtrHashTableIterator it;
  BzlaIntHashTableIterator iit;
  BzlaPropSolver *slv;
  BzlaIntHashTable *cache;

  slv = BZLA_PROP_SOLVER(bzla);
  assert(slv);
  assert(slv->domains);
  assert(slv->domains->count == 0);

  progress_steps     = 100;
  progress_steps_inc = progress_steps * 10;

  start               = bzla_util_time_stamp();
  nprops              = bzla_opt_get(bzla, BZLA_OPT_PROP_NPROPS);
  nupdates            = bzla_opt_get(bzla, BZLA_OPT_PROP_NUPDATES);
  opt_prop_const_bits = bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS);
  opt_verbosity       = bzla_opt_get(bzla, BZLA_OPT_VERBOSITY);

  if (nprops)
  {
    nprops += slv->stats.props;
    BZLA_MSG(bzla->msg, 1, "Set propagation limit to %zu", nprops);
  }
  if (nupdates)
  {
    nupdates += slv->stats.updates;
    BZLA_MSG(bzla->msg, 1, "Set model update limit to %zu", nupdates);
  }

  if (opt_prop_const_bits)
  {
    synthesize_constraints(bzla);
    if (bzla->found_constraint_false) goto UNSAT;
  }

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    root = bzla_iter_hashptr_next(&it);
    if (opt_prop_const_bits)
    {
      bzla_prop_solver_init_domains(bzla, slv->domains, root);
    }
  }

  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    root     = bzla_iter_hashptr_next(&it);
    not_root = bzla_node_invert(root);

    /* check for constraints occurring in both phases */
    if (bzla_hashptr_table_get(bzla->unsynthesized_constraints, not_root))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->synthesized_constraints, not_root))
      goto UNSAT;
    if (bzla_hashptr_table_get(bzla->assumptions, not_root)) goto UNSAT;

    /* initialize propagator domains for inverse values / const bits handling */
    if (opt_prop_const_bits)
    {
      bzla_prop_solver_init_domains(bzla, slv->domains, root);
    }
  }

  if (opt_prop_const_bits && bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_DOMAINS))
  {
    cache = bzla_hashint_table_new(bzla->mm);
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->assumptions);
    while (bzla_iter_hashptr_has_next(&it))
    {
      root = bzla_iter_hashptr_next(&it);
      propagate_domains(bzla, root, slv->domains, cache);
    }
    bzla_hashint_table_delete(cache);
  }

  for (;;)
  {
    assert(BZLA_EMPTY_STACK(slv->toprop));

    /* collect unsatisfied roots (kept up-to-date in update_cone) */
    assert(!slv->roots);
    slv->roots = bzla_hashint_map_new(bzla->mm);
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->assumptions);
    while (bzla_iter_hashptr_has_next(&it))
    {
      root = bzla_iter_hashptr_next(&it);

      if (!bzla_hashint_map_contains(slv->roots, bzla_node_get_id(root))
          && bzla_bv_is_zero(bzla_model_get_bv(bzla, root)))
      {
        if (bzla_node_is_bv_const(root))
          goto UNSAT; /* contains false constraint -> unsat */
        bzla_hashint_map_add(slv->roots, bzla_node_get_id(root));
      }
    }

    if (!slv->score && bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
      slv->score = bzla_hashint_map_new(bzla->mm);

    if (bzla_terminate(bzla))
    {
      sat_result = BZLA_RESULT_UNKNOWN;
      goto DONE;
    }

    /* all constraints sat? */
    if (!slv->roots->count) goto SAT;

    /* compute initial sls score */
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
      bzla_slsutils_compute_sls_scores(
          bzla, bzla->bv_model, bzla->fun_model, slv->score);

    /* init */
    slv->flip_cond_const_prob =
        bzla_opt_get(bzla, BZLA_OPT_PROP_PROB_FLIP_COND_CONST);
    slv->flip_cond_const_prob_delta =
        slv->flip_cond_const_prob > (BZLA_PROB_50)
            ? -BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA
            : BZLA_PROPUTILS_PROB_FLIP_COND_CONST_DELTA;

    /* move */
    for (j = 0, max_steps = BZLA_PROP_MAXSTEPS(slv->stats.restarts + 1);
         !bzla_opt_get(bzla, BZLA_OPT_PROP_USE_RESTARTS) || j < max_steps;
         j++)
    {
      if (bzla_terminate(bzla) || (nprops && slv->stats.props >= nprops)
          || (nupdates && slv->stats.updates >= nupdates))
      {
        sat_result = BZLA_RESULT_UNKNOWN;
        goto DONE;
      }

      if (opt_verbosity && j % progress_steps == 0)
      {
        print_progress(slv);
        if (j <= 1000000 && j >= progress_steps_inc)
        {
          progress_steps = progress_steps_inc;
          progress_steps_inc *= 10;
        }
      }

      if (!(move(bzla, nprops))) goto UNSAT;

      /* all constraints sat? */
      if (!slv->roots->count) goto SAT;
    }

    /* restart */
    slv->api.generate_model((BzlaSolver *) slv, false, true);
    bzla_hashint_map_delete(slv->roots);
    slv->roots = 0;
    if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
    {
      bzla_hashint_map_delete(slv->score);
      slv->score = bzla_hashint_map_new(bzla->mm);
    }
    slv->stats.restarts += 1;
    bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->toprop);
  }

SAT:
  sat_result = BZLA_RESULT_SAT;
  goto DONE;

UNSAT:
  sat_result = BZLA_RESULT_UNSAT;

DONE:
  print_progress(slv);

  if (slv->roots)
  {
    bzla_hashint_map_delete(slv->roots);
    slv->roots = 0;
  }
  if (slv->score)
  {
    bzla_hashint_map_delete(slv->score);
    slv->score = 0;
  }
  // TODO: domains shouldn't be deleted after every sat call
  if (slv->domains)
  {
    bzla_iter_hashint_init(&iit, slv->domains);
    while (bzla_iter_hashint_has_next(&iit))
    {
      bzla_bvdomain_free(slv->bzla->mm,
                         bzla_iter_hashint_next_data(&iit)->as_ptr);
    }
    bzla_hashint_map_clear(slv->domains);
  }
  bzla_proputils_reset_prop_info_stack(slv->bzla->mm, &slv->toprop);
  assert(BZLA_EMPTY_STACK(slv->prop_path));

  slv->time.check_sat += bzla_util_time_stamp() - start;

  return sat_result;
}

/* Note: failed assumptions handling not necessary, prop only works for SAT */
static int32_t
sat_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  int32_t sat_result;
  Bzla *bzla;

  bzla = slv->bzla;
  assert(!bzla->inconsistent);

  if (bzla_terminate(bzla))
  {
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  /* Generate intial model, all bv vars are initialized with zero. We do
   * not have to consider model_for_all_nodes, but let this be handled by
   * the model generation (if enabled) after SAT has been determined. */
  slv->api.generate_model((BzlaSolver *) slv, false, true);
  sat_result = bzla_prop_solver_sat(bzla);
DONE:
  assert(BZLA_EMPTY_STACK(slv->toprop));
  return sat_result;
}

static void
generate_model_prop_solver(BzlaPropSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla = slv->bzla;

  if (!reset && bzla->bv_model) return;
  bzla_lsutils_initialize_bv_model((BzlaSolver *) slv);
  bzla_model_init_fun(bzla, &bzla->fun_model);
  bzla_model_generate(
      bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
}

static void
print_stats_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla    = slv->bzla;
  bool entailed = bzla_opt_get(slv->bzla, BZLA_OPT_PROP_ENTAILED);

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "restarts: %u", slv->stats.restarts);
  BZLA_MSG(bzla->msg, 1, "moves: %u", slv->stats.moves);
  BZLA_MSG(bzla->msg, 1, "    skipped moves: %u", slv->stats.moves_skipped);
  if (entailed)
    BZLA_MSG(bzla->msg, 1, "    entailed moves: %u", slv->stats.moves_entailed);

  BZLA_MSG(bzla->msg,
           1,
           "moves per second: %.1f",
           (double) slv->stats.moves / slv->time.check_sat);
  BZLA_MSG(bzla->msg, 1, "propagation (steps): %u", slv->stats.props);
  if (entailed)
    BZLA_MSG(bzla->msg,
             1,
             "    entailed propagations: %u",
             slv->stats.props_entailed);
  BZLA_MSG(bzla->msg,
           1,
           "    consistent value propagations: %u",
           slv->stats.props_cons);
  BZLA_MSG(
      bzla->msg, 1, "    inverse value propagations: %u", slv->stats.props_inv);
  BZLA_MSG(bzla->msg,
           1,
           "propagation (steps) per second: %.1f",
           (double) slv->stats.props / slv->time.check_sat);
  BZLA_MSG(bzla->msg,
           1,
           "propagation conflicts (non-recoverable): %u",
           slv->stats.non_rec_conf);
  BZLA_MSG(bzla->msg,
           1,
           "propagation conflicts (recoverable): %u",
           slv->stats.rec_conf);
  if (entailed)
  {
    BZLA_MSG(bzla->msg,
             1,
             "   fixed recoverable conflicts: %u",
             slv->stats.fixed_conf);
    BZLA_MSG(bzla->msg,
             1,
             "   recoverable conflicts fixed without an entailed move: %u",
             slv->stats.fixed_conf - slv->stats.moves_entailed);
  }
  BZLA_MSG(bzla->msg, 1, "updates (cone): %u", slv->stats.updates);
  BZLA_MSG(bzla->msg,
           1,
           "updates per second: %u",
           slv->stats.updates / slv->time.check_sat);
#ifndef NDEBUG
  char *s_cons = "    consistent fun calls";
  char *s_inv  = "    inverse fun calls";
  /* Consistent value computation stats. */
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "consistent value computations:");
  BZLA_MSG(bzla->msg, 1, "%s (add): %u", s_cons, slv->stats.cons_add);
  BZLA_MSG(bzla->msg, 1, "%s (and): %u", s_cons, slv->stats.cons_and);
  BZLA_MSG(bzla->msg, 1, "%s (eq): %u", s_cons, slv->stats.cons_eq);
  BZLA_MSG(bzla->msg, 1, "%s (ult): %u", s_cons, slv->stats.cons_ult);
  BZLA_MSG(bzla->msg, 1, "%s (sll): %u", s_cons, slv->stats.cons_sll);
  BZLA_MSG(bzla->msg, 1, "%s (slt): %u", s_cons, slv->stats.cons_slt);
  BZLA_MSG(bzla->msg, 1, "%s (srl): %u", s_cons, slv->stats.cons_srl);
  BZLA_MSG(bzla->msg, 1, "%s (sra): %u", s_cons, slv->stats.cons_sra);
  BZLA_MSG(bzla->msg, 1, "%s (mul): %u", s_cons, slv->stats.cons_mul);
  BZLA_MSG(bzla->msg, 1, "%s (udiv): %u", s_cons, slv->stats.cons_udiv);
  BZLA_MSG(bzla->msg, 1, "%s (urem): %u", s_cons, slv->stats.cons_urem);
  BZLA_MSG(bzla->msg, 1, "%s (concat): %u", s_cons, slv->stats.cons_concat);
  BZLA_MSG(bzla->msg, 1, "%s (slice): %u", s_cons, slv->stats.cons_slice);
  BZLA_MSG(bzla->msg, 1, "%s (cond): %u", s_cons, slv->stats.cons_cond);
  BZLA_MSG(bzla->msg, 1, "%s (xor): %u", s_cons, slv->stats.cons_xor);

  /* Inverse value computation stats. */
  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg, 1, "inverse value computations:");

  BZLA_MSG(bzla->msg, 1, "%s (add): %u", s_inv, slv->stats.inv_add);
  BZLA_MSG(bzla->msg, 1, "%s (and): %u", s_inv, slv->stats.inv_and);
  BZLA_MSG(bzla->msg, 1, "%s (eq): %u", s_inv, slv->stats.inv_eq);
  BZLA_MSG(bzla->msg, 1, "%s (ult): %u", s_inv, slv->stats.inv_ult);
  BZLA_MSG(bzla->msg, 1, "%s (sll): %u", s_inv, slv->stats.inv_sll);
  BZLA_MSG(bzla->msg, 1, "%s (slt): %u", s_inv, slv->stats.inv_slt);
  BZLA_MSG(bzla->msg, 1, "%s (srl): %u", s_inv, slv->stats.inv_srl);
  BZLA_MSG(bzla->msg, 1, "%s (sra): %u", s_inv, slv->stats.inv_sra);
  BZLA_MSG(bzla->msg, 1, "%s (mul): %u", s_inv, slv->stats.inv_mul);
  BZLA_MSG(bzla->msg, 1, "%s (udiv): %u", s_inv, slv->stats.inv_udiv);
  BZLA_MSG(bzla->msg, 1, "%s (urem): %u", s_inv, slv->stats.inv_urem);
  BZLA_MSG(bzla->msg, 1, "%s (concat): %u", s_inv, slv->stats.inv_concat);
  BZLA_MSG(bzla->msg, 1, "%s (slice): %u", s_inv, slv->stats.inv_slice);
  BZLA_MSG(bzla->msg, 1, "%s (cond): %u", s_inv, slv->stats.inv_cond);
  BZLA_MSG(bzla->msg, 1, "%s (xor): %u", s_inv, slv->stats.inv_xor);
#endif

  if (bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_BITS))
  {
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg,
             1,
             "fixed bits: %zu/%zu (%.1f%%)",
             slv->stats.fixed_bits,
             slv->stats.total_bits,
             (double) slv->stats.fixed_bits / slv->stats.total_bits * 100);
  }

  if (bzla_opt_get(bzla, BZLA_OPT_PROP_CONST_DOMAINS))
  {
    BZLA_MSG(bzla->msg, 1, "");
    BZLA_MSG(bzla->msg, 1, "updated domains: %zu", slv->stats.updated_domains);
    BZLA_MSG(bzla->msg,
             1,
             "updated domains (children): %zu",
             slv->stats.updated_domains_children);
  }
}

static void
print_time_stats_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  Bzla *bzla = slv->bzla;

  BZLA_MSG(bzla->msg, 1, "");
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (total)",
           slv->time.update_cone);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (reset)",
           slv->time.update_cone_reset);
  BZLA_MSG(bzla->msg,
           1,
           "%.2f seconds for updating cone (model gen)",
           slv->time.update_cone_model_gen);
  if (bzla_opt_get(bzla, BZLA_OPT_PROP_USE_BANDIT))
    BZLA_MSG(bzla->msg,
             1,
             "%.2f seconds for updating cone (compute score)",
             slv->time.update_cone_compute_score);
  BZLA_MSG(bzla->msg, 1, "");
}

static void
print_model_prop_solver(BzlaPropSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbvfp(slv->bzla, format, file);
}

BzlaSolver *
bzla_new_prop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaPropSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->bzla    = bzla;
  slv->kind    = BZLA_PROP_SOLVER_KIND;
  slv->domains = bzla_hashint_map_new(bzla->mm);

  slv->api.clone = (BzlaSolverClone) clone_prop_solver;
  slv->api.delet = (BzlaSolverDelete) delete_prop_solver;
  slv->api.sat   = (BzlaSolverSat) sat_prop_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_prop_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_prop_solver;

  BZLA_INIT_STACK(bzla->mm, slv->toprop);
#ifndef NDEBUG
  BZLA_INIT_STACK(bzla->mm, slv->prop_path);
#endif

  BZLA_MSG(bzla->msg, 1, "enabled prop engine");

  return (BzlaSolver *) slv;
}
