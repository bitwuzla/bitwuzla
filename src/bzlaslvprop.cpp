/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <iostream>
#ifndef NDEBUG
#include <iomanip>
#include <sstream>
#endif

extern "C" {
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlamsg.h"
#include "bzlaprintmodel.h"
#include "bzlaslvprop.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"
}

#include "bv/bitvector.h"
#include "ls/bv/bitvector_domain.h"
#include "ls/ls_bv.h"

struct BzlaPropSolver;

namespace bzla {
namespace prop {

template <typename T>
using NodeMap   = std::unordered_map<BzlaNode *, T>;
using NodeSet   = std::unordered_set<BzlaNode *>;
using NodeStack = std::vector<BzlaNode *>;

class PropSolverState
{
 public:
  struct
  {
    uint64_t d_nfixed_bits = 0;
    uint64_t d_ntotal_bits = 0;
  } d_statistics;
  struct
  {
    double d_check_sat = 0;
  } d_time_statistics;

  PropSolverState(Bzla *bzla)
      : d_bzla(bzla), d_use_sext(bzla_opt_get(d_bzla, BZLA_OPT_PROP_SEXT))
  {
    assert(bzla);

    d_ls.reset(new bzla::ls::LocalSearchBV(
        bzla_opt_get(d_bzla, BZLA_OPT_PROP_NPROPS),
        bzla_opt_get(d_bzla, BZLA_OPT_PROP_NUPDATES),
        bzla_opt_get(d_bzla, BZLA_OPT_SEED)));

    d_ls->d_options.use_ineq_bounds =
        bzla_opt_get(d_bzla, BZLA_OPT_PROP_INFER_INEQ_BOUNDS);
    d_ls->d_options.use_opt_lt_concat_sext =
        bzla_opt_get(d_bzla, BZLA_OPT_PROP_USE_INV_LT_CONCAT);
    d_ls->d_options.prob_pick_inv_value =
      bzla_opt_get(d_bzla, BZLA_OPT_PROP_PROB_USE_INV_VALUE);

    assert(bzla_opt_get(d_bzla, BZLA_OPT_PROP_PATH_SEL)
               == BZLA_PROP_PATH_SEL_ESSENTIAL
           || bzla_opt_get(d_bzla, BZLA_OPT_PROP_PATH_SEL)
                  == BZLA_PROP_PATH_SEL_RANDOM);
    d_ls->d_options.use_path_sel_essential =
        bzla_opt_get(d_bzla, BZLA_OPT_PROP_PATH_SEL)
                == BZLA_PROP_PATH_SEL_ESSENTIAL
            ? true
            : false;
    d_ls->d_options.prob_pick_ess_input =
        1000 - bzla_opt_get(d_bzla, BZLA_OPT_PROP_PROB_RANDOM_INPUT);

    d_ls->set_log_level(bzla_opt_get(d_bzla, BZLA_OPT_LOGLEVEL));
    d_ls->init();
  }

  void init_nodes();
  BzlaSolverResult check_sat();
  void generate_model();
  void print_statistics();

 private:
  uint32_t mk_node(BzlaNode *node);
  void synthesize_constraints();
  void print_progress() const;
  Bzla *d_bzla;
  std::unique_ptr<bzla::ls::LocalSearchBV> d_ls;
  NodeMap<uint32_t> d_node_map;
  NodeStack d_leafs;
  /**
   * True to create sign extend nodes for concats that represent a sign extend.
   */
  bool d_use_sext = false;
};

namespace {
bool
is_leaf_node(BzlaNode *n)
{
  assert(n);
  return bzla_node_is_bv_var(n) || bzla_node_is_bv_const(n)
         || bzla_node_is_apply(n) || bzla_node_is_fun_eq(n)
         || bzla_node_is_quantifier(n);
}
}  // namespace

uint32_t
PropSolverState::mk_node(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_bv(d_bzla, node) || is_leaf_node(node));

  uint32_t res = 0;
  uint32_t bw  = bzla_node_bv_get_width(d_bzla, node);

  if (!is_leaf_node(node))
  {
    for (uint32_t i = 0; i < node->arity; ++i)
    {
      BzlaNode *e      = node->e[i];
      BzlaNode *real_e = bzla_node_real_addr(e);
      auto it          = d_node_map.find(real_e);
      assert(it != d_node_map.end());
      if (bzla_node_is_inverted(e))
      {
        auto iit = d_node_map.find(e);
        if (iit == d_node_map.end())
        {
          d_node_map[e] = d_ls->invert_node(it->second);
        }
      }
    }
  }

  bzla::ls::BitVectorDomain domain(bw);

  if (node->av)
  {
    BzlaAIGVec *av = node->av;
    assert(av->width == bw);
    for (uint32_t i = 0; i < bw; ++i)
    {
      uint32_t idx = bw - 1 - i;
      if (bzla_aig_is_const(av->aigs[i]))
      {
        domain.fix_bit(idx, bzla_aig_is_true(av->aigs[i]));
        d_statistics.d_nfixed_bits += 1;
      }
    }
    d_statistics.d_ntotal_bits += bw;
  }
  else if (bzla_node_is_bv_const(node))
  {
    BzlaBitVector* bits = bzla_node_bv_const_get_bits(node);
    for (uint32_t i = 0; i < bw; ++i)
    {
      domain.fix_bit(i, bzla_bv_get_bit(bits, i));
    }
  }

  switch (node->kind)
  {
    case BZLA_BV_ADD_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_ADD,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_AND_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_AND,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_CONCAT_NODE:
      assert(node->arity == 2);
      if (d_use_sext && bzla_exp_is_bv_sext(d_bzla, node))
      {
        res =
            d_ls->mk_indexed_node(bzla::ls::OperatorKind::BV_SEXT,
                                  domain,
                                  d_node_map.at(node->e[1]),
                                  {bzla_node_bv_get_width(d_bzla, node->e[0])});
      }
      else
      {
        res = d_ls->mk_node(
            bzla::ls::OperatorKind::BV_CONCAT,
            domain,
            {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      }
      break;
    case BZLA_BV_EQ_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::EQ,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_MUL_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_MUL,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_ULT_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_ULT,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SLICE_NODE:
      assert(node->arity == 1);
      res = d_ls->mk_indexed_node(bzla::ls::OperatorKind::BV_EXTRACT,
                                  domain,
                                  d_node_map.at(node->e[0]),
                                  {bzla_node_bv_slice_get_upper(node),
                                   bzla_node_bv_slice_get_lower(node)});
      break;
    case BZLA_BV_SLL_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_SHL,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SLT_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_SLT,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SRL_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_SHR,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_UDIV_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_UDIV,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_UREM_NODE:
      assert(node->arity == 2);
      res =
          d_ls->mk_node(bzla::ls::OperatorKind::BV_UREM,
                        domain,
                        {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_COND_NODE:
      assert(node->arity == 3);
      res = d_ls->mk_node(bzla::ls::OperatorKind::ITE,
                          domain,
                          {d_node_map.at(node->e[0]),
                           d_node_map.at(node->e[1]),
                           d_node_map.at(node->e[2])});
      break;
    default:
      assert(is_leaf_node(node));
      res = d_ls->mk_node(domain.lo(), domain);
  }

  return res;
}

void
PropSolverState::synthesize_constraints()
{
  BzlaNode *cur;
  BzlaAIGVec *av;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, d_bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it));
    bzla_synthesize_exp(d_bzla, cur, nullptr);
    av = bzla_node_real_addr(cur)->av;
    assert(av->width == 1);

    if ((bzla_node_is_inverted(cur) && bzla_aig_is_true(av->aigs[0]))
        || (bzla_node_is_regular(cur) && bzla_aig_is_false(av->aigs[0])))
    {
      d_bzla->found_constraint_false = true;
      break;
    }
  }

  bzla_iter_hashptr_init(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it));
    bzla_synthesize_exp(d_bzla, cur, 0);
  }
}

void
PropSolverState::init_nodes()
{
  NodeStack roots;
  NodeStack visit;
  NodeSet cache;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, d_bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaNode *cur = static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it));
    roots.push_back(cur);
    visit.push_back(bzla_node_real_addr(cur));
  }

  while (!visit.empty())
  {
    BzlaNode *cur = bzla_node_real_addr(visit.back());
    visit.pop_back();

    if (d_node_map.find(cur) != d_node_map.end()) continue;

    if (cache.find(cur) != cache.end())
    {
      assert(bzla_node_is_regular(cur));
      d_node_map[cur] = mk_node(cur);
    }
    else
    {
      cache.emplace(cur);
      visit.push_back(cur);
      if (is_leaf_node(cur))
      {
        d_leafs.push_back(cur);
      }
      else
      {
        for (uint32_t i = 0; i < cur->arity; ++i)
        {
          visit.push_back(cur->e[i]);
        }
      }
    }
  }

  for (BzlaNode *root : roots)
  {
    if (d_node_map.find(root) == d_node_map.end())
    {
      assert(bzla_node_is_inverted(root));
      auto it = d_node_map.find(bzla_node_real_addr(root));
      assert(it != d_node_map.end());
      d_node_map[root] = d_ls->invert_node(it->second);
    }
  }
}

void
PropSolverState::print_progress() const
{
  uint32_t nroots_total = d_bzla->assumptions->count
                          + d_bzla->unsynthesized_constraints->count
                          + d_bzla->synthesized_constraints->count;
  uint32_t nroots_unsat = d_ls->get_num_roots_unsat();

  BZLA_MSG(d_bzla->msg,
           1,
           "%u/%u roots satisfied (%.1f%%), "
           "moves: %u, "
           "propagation steps: %zu, "
           "cone updates: %zu",
           nroots_total - nroots_unsat,
           nroots_total,
           (double) (nroots_total - nroots_unsat) / nroots_total * 100,
           d_ls->d_statistics.d_nmoves,
           d_ls->d_statistics.d_nprops,
           d_ls->d_statistics.d_nupdates);
}

BzlaSolverResult
PropSolverState::check_sat()
{
  double start                = bzla_util_time_stamp();
  BzlaSolverResult sat_result = BZLA_RESULT_UNKNOWN;

  bool const_bits    = bzla_opt_get(d_bzla, BZLA_OPT_PROP_CONST_BITS) == 1;
  uint32_t verbosity = bzla_opt_get(d_bzla, BZLA_OPT_VERBOSITY);

  uint64_t nprops   = bzla_opt_get(d_bzla, BZLA_OPT_PROP_NPROPS);
  uint64_t nupdates = bzla_opt_get(d_bzla, BZLA_OPT_PROP_NUPDATES);

  uint32_t progress_steps     = 100;
  uint32_t progress_steps_inc = progress_steps * 10;

  if (nprops)
  {
    nprops += d_ls->d_statistics.d_nprops;
    d_ls->set_max_nprops(nprops);
    BZLA_MSG(d_bzla->msg, 1, "Set propagation limit to %zu", nprops);
  }
  if (nupdates)
  {
    nupdates += d_ls->d_statistics.d_nupdates;
    d_ls->set_max_nupdates(nupdates);
    BZLA_MSG(d_bzla->msg, 1, "Set model update limit to %zu", nupdates);
  }

  if (const_bits)
  {
    synthesize_constraints();
    if (d_bzla->found_constraint_false) goto UNSAT;
  }
  init_nodes();

  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, d_bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaNode *root = static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it));
    assert(d_node_map.find(root) != d_node_map.end());
    d_ls->register_root(d_node_map.at(root));
  }

  for (uint32_t j = 0;; ++j)
  {
    if (bzla_terminate(d_bzla)
        || (nprops && d_ls->d_statistics.d_nprops >= nprops)
        || (nupdates && d_ls->d_statistics.d_nupdates >= nupdates))
    {
      assert(sat_result == BZLA_RESULT_UNKNOWN);
      goto DONE;
    }

    if (verbosity > 0 && j % progress_steps == 0)
    {
      print_progress();
      if (j <= 1000000 && j >= progress_steps_inc)
      {
        progress_steps = progress_steps_inc;
        progress_steps_inc *= 10;
      }
    }

    bzla::ls::Result res = d_ls->move();

    if (res == bzla::ls::Result::UNSAT)
    {
      goto UNSAT;
    }

    if (res == bzla::ls::Result::SAT)
    {
      goto SAT;
    }
  }

SAT:
  sat_result = BZLA_RESULT_SAT;
  goto DONE;
UNSAT:
  sat_result = BZLA_RESULT_UNSAT;
DONE:
  print_progress();

  d_time_statistics.d_check_sat += bzla_util_time_stamp() - start;

  return sat_result;
}

void
PropSolverState::generate_model()
{
  bzla_model_init_bv(d_bzla, &d_bzla->bv_model);
  bzla_model_init_fun(d_bzla, &d_bzla->fun_model);
  for (BzlaNode *leaf : d_leafs)
  {
    assert(bzla_node_is_regular(leaf));
    assert(is_leaf_node(leaf));

    auto iit = d_node_map.find(leaf);
    assert(iit != d_node_map.end());
    const BitVector &assignment         = d_ls->get_assignment(iit->second);
    BzlaBitVector *bv_assignment        = bzla_bv_const(
        d_bzla->mm, assignment.to_string().c_str(), assignment.size());
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, leaf, bv_assignment);
    bzla_bv_free(d_bzla->mm, bv_assignment);
  }
}

void
PropSolverState::print_statistics()
{
  uint64_t nmoves   = d_ls->d_statistics.d_nmoves;
  uint64_t nprops   = d_ls->d_statistics.d_nprops;
  uint64_t nupdates = d_ls->d_statistics.d_nupdates;

  BZLA_MSG(d_bzla->msg, 1, "");
  BZLA_MSG(d_bzla->msg, 1, "moves: %u", nmoves);
  // BZLA_MSG(d_bzla->msg, 1, "    skipped moves: %u", TODO);

  BZLA_MSG(d_bzla->msg,
           1,
           "moves per second: %.1f",
           (double) nmoves / d_time_statistics.d_check_sat);
  BZLA_MSG(d_bzla->msg, 1, "propagation steps: %u", nprops);
  BZLA_MSG(d_bzla->msg,
           1,
           "    inverse value propagations: %u",
           d_ls->d_statistics.d_nprops_inv);
  BZLA_MSG(d_bzla->msg,
           1,
           "    consistent value propagations: %u",
           d_ls->d_statistics.d_nprops_cons);
  BZLA_MSG(d_bzla->msg,
           1,
           "propagation steps per second: %.1f",
           (double) nprops / d_time_statistics.d_check_sat);
  BZLA_MSG(d_bzla->msg,
           1,
           "propagation conflicts (non-recoverable): %u",
           d_ls->d_statistics.d_nconf);
  BZLA_MSG(d_bzla->msg, 1, "cone updates: %u", nupdates);
  BZLA_MSG(d_bzla->msg,
           1,
           "updates per second: %.1f",
           (double) nupdates / d_time_statistics.d_check_sat);
#ifndef NDEBUG
  BZLA_MSG(d_bzla->msg, 1, "");
  BZLA_MSG(d_bzla->msg, 1, "value computations:");
  BZLA_MSG(d_bzla->msg, 1, "  inverse:");
  for (const auto &p : d_ls->d_statistics.d_ninv)
  {
    std::stringstream ss;
    ss << std::setw(8) << p.second << " " << p.first;
    BZLA_MSG(d_bzla->msg, 1, ss.str().c_str());
  }

  BZLA_MSG(d_bzla->msg, 1, "  consistent:");
  for (const auto &p : d_ls->d_statistics.d_ncons)
  {
    std::stringstream ss;
    ss << std::setw(8) << p.second << " " << p.first;
    BZLA_MSG(d_bzla->msg, 1, ss.str().c_str());
  }
#endif

  if (bzla_opt_get(d_bzla, BZLA_OPT_PROP_CONST_BITS))
  {
    BZLA_MSG(d_bzla->msg, 1, "");
    BZLA_MSG(
        d_bzla->msg,
        1,
        "fixed bits: %zu/%zu (%.1f%%)",
        d_statistics.d_nfixed_bits,
        d_statistics.d_ntotal_bits,
        (double) d_statistics.d_nfixed_bits / d_statistics.d_ntotal_bits * 100);
  }
}
}  // namespace prop
}  // namespace bzla

struct BzlaPropSolver
{
  BZLA_SOLVER_STRUCT;
  std::unique_ptr<bzla::prop::PropSolverState> d_state;
};

namespace {

BzlaSolverResult
check_sat_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  BzlaSolverResult sat_result;
  Bzla *bzla = slv->bzla;
  assert(!bzla->inconsistent);

  if (bzla_terminate(bzla))
  {
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  sat_result = slv->d_state->check_sat();

DONE:
  return sat_result;
}

void
delete_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla = slv->bzla;
  delete slv;
  bzla->slv = nullptr;
}

void
generate_model_prop_solver(BzlaPropSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
  assert(slv);

  Bzla *bzla = slv->bzla;

  if (!reset && bzla->bv_model) return;

  bzla_model_init_bv(bzla, &bzla->bv_model);
  bzla_model_init_fun(bzla, &bzla->fun_model);

  slv->d_state->generate_model();
  /* generate model for non-input nodes */
  bzla_model_generate(
      bzla, bzla->bv_model, bzla->fun_model, model_for_all_nodes);
}

void
print_stats_prop_solver(BzlaPropSolver *slv)
{
  slv->d_state->print_statistics();
}

void
print_time_stats_prop_solver(BzlaPropSolver *slv)
{
  (void) slv;
  // nothing to print yet
}

void
print_model_prop_solver(BzlaPropSolver *slv, const char *format, FILE *file)
{
  bzla_print_model_aufbvfp(slv->bzla, format, file);
}
}  // namespace

BzlaSolver *
bzla_new_prop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaPropSolver *slv = new BzlaPropSolver();
  slv->d_state.reset(new bzla::prop::PropSolverState(bzla));
  slv->kind      = BZLA_PROP_SOLVER_KIND;
  slv->bzla      = bzla;
  slv->api.delet = (BzlaSolverDelete) delete_prop_solver;
  slv->api.sat   = (BzlaSolverSat) check_sat_prop_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_prop_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_prop_solver;

  BZLA_MSG(bzla->msg, 1, "enabled prop engine");

  return (BzlaSolver *) slv;
}
