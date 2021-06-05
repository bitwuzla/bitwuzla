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

extern "C" {
#include "bzlacore.h"
#include "bzlamodel.h"
#include "bzlamsg.h"
#include "bzlaslvprop.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"
}

#include "bitvector.h"
#include "bitvector_domain.h"
#include "bzlals.h"

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
    uint64_t nfixed_bits = 0;
    uint64_t ntotal_bits = 0;
  } d_statistics;
  struct
  {
    double check_sat = 0;
  } d_time_statistics;

  PropSolverState(Bzla *bzla, uint32_t max_nprops, uint32_t seed) : d_bzla(bzla)
  {
    assert(bzla);
    d_bzlals.reset(new bzlals::BzlaLs(max_nprops, seed));
    d_bzlals->set_log_level(bzla_opt_get(d_bzla, BZLA_OPT_LOGLEVEL));
  }

  void init_nodes();
  BzlaSolverResult check_sat();
  void generate_model();

 private:
  uint32_t mk_node(BzlaNode *node);
  void synthesize_constraints();
  void print_progress() const;
  Bzla *d_bzla;
  std::unique_ptr<bzlals::BzlaLs> d_bzlals;
  NodeMap<uint32_t> d_node_map;
  NodeStack d_leafs;
};

uint32_t
PropSolverState::mk_node(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_bv(d_bzla, node));

  uint32_t res = 0;
  uint32_t bw  = bzla_node_bv_get_width(d_bzla, node);

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
        d_node_map[e] = d_bzlals->invert_node(it->second);
      }
    }
  }

  bzlals::BitVectorDomain domain(bw);

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
        d_statistics.nfixed_bits += 1;
      }
    }
    d_statistics.ntotal_bits += bw;
  }

  switch (node->kind)
  {
    case BZLA_BV_ADD_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::ADD,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_AND_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::AND,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_CONCAT_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::CONCAT,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_EQ_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::EQ,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_MUL_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::MUL,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_ULT_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::ULT,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SLICE_NODE:
      assert(node->arity == 1);
      res = d_bzlals->mk_indexed_node(bzlals::BzlaLs::OperatorKind::EXTRACT,
                                      domain,
                                      d_node_map.at(node->e[0]),
                                      {bzla_node_bv_slice_get_upper(node),
                                       bzla_node_bv_slice_get_lower(node)});
      break;
    case BZLA_BV_SLL_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::SHL,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SLT_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::SLT,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_SRL_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::SHR,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_UDIV_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::UDIV,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_BV_UREM_NODE:
      assert(node->arity == 2);
      res = d_bzlals->mk_node(
          bzlals::BzlaLs::OperatorKind::UREM,
          domain,
          {d_node_map.at(node->e[0]), d_node_map.at(node->e[1])});
      break;
    case BZLA_COND_NODE:
      assert(node->arity == 3);
      res = d_bzlals->mk_node(bzlals::BzlaLs::OperatorKind::ITE,
                              domain,
                              {d_node_map.at(node->e[0]),
                               d_node_map.at(node->e[1]),
                               d_node_map.at(node->e[2])});
      break;
    case BZLA_BV_CONST_NODE:
    case BZLA_VAR_NODE: res = d_bzlals->mk_node(domain.lo(), domain); break;
    default: assert(false);
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
    bzla_synthesize_exp(d_bzla, cur, 0);
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
  NodeStack visit;
  NodeSet cache;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, d_bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, d_bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    visit.push_back(static_cast<BzlaNode *>(bzla_iter_hashptr_next(&it)));
  }

  while (!visit.empty())
  {
    BzlaNode *cur = visit.back();
    visit.pop_back();
    BzlaNode *real_cur = bzla_node_real_addr(cur);

    if (d_node_map.find(real_cur) != d_node_map.end()) continue;

    if (cache.find(real_cur) != cache.end())
    {
      assert(bzla_node_is_regular(cur));
      uint32_t real_node   = mk_node(real_cur);
      d_node_map[real_cur] = real_node;
      if (bzla_node_is_bv_var(real_cur)) d_leafs.push_back(real_cur);
    }
    else
    {
      cache.emplace(real_cur);
      visit.push_back(real_cur);
      for (uint32_t i = 0; i < real_cur->arity; ++i)
      {
        visit.push_back(real_cur->e[i]);
      }
    }
  }
}

void
PropSolverState::print_progress() const
{
  uint32_t nroots_total = d_bzla->assumptions->count
                          + d_bzla->unsynthesized_constraints->count
                          + d_bzla->synthesized_constraints->count;
  uint32_t nroots_unsat = d_bzlals->get_num_roots_unsat();

  BZLA_MSG(d_bzla->msg,
           1,
           "%u/%u roots satisfied (%.1f%%), "
           "moves: %u, "
           "propagations: %zu, "
           "model updates: %zu",
           nroots_total - nroots_unsat,
           nroots_total,
           (double) (nroots_total - nroots_unsat) / nroots_total * 100,
           d_bzlals->get_nmoves(),
           d_bzlals->get_nprops(),
           d_bzlals->get_nupdates());
}

BzlaSolverResult
PropSolverState::check_sat()
{
  double start                = bzla_util_time_stamp();
  BzlaSolverResult sat_result = BZLA_RESULT_UNKNOWN;

  BzlaPropSolver *slv = (BzlaPropSolver *) d_bzla->slv;
  assert(slv);

  bool const_bits    = bzla_opt_get(d_bzla, BZLA_OPT_PROP_CONST_BITS) == 1;
  uint32_t verbosity = bzla_opt_get(d_bzla, BZLA_OPT_VERBOSITY);

  uint64_t nprops   = bzla_opt_get(d_bzla, BZLA_OPT_PROP_NPROPS);
  uint64_t nupdates = bzla_opt_get(d_bzla, BZLA_OPT_PROP_NUPDATES);

  uint32_t progress_steps     = 100;
  uint32_t progress_steps_inc = progress_steps * 10;

  if (nprops)
  {
    nprops += d_bzlals->get_nprops();
    d_bzlals->set_max_nprops(nprops);
    BZLA_MSG(d_bzla->msg, 1, "Set propagation limit to %zu", nprops);
  }
  if (nupdates)
  {
    nupdates += d_bzlals->get_nupdates();
    d_bzlals->set_max_nupdates(nupdates);
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
    d_bzlals->register_root(d_node_map.at(root));
  }

  for (uint32_t j = 0;; ++j)
  {
    if (bzla_terminate(d_bzla) || (nprops && d_bzlals->get_nprops() >= nprops)
        || (nupdates && d_bzlals->get_nupdates() >= nupdates))
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

    bzlals::BzlaLs::Result res = d_bzlals->move();

    if (res == bzlals::BzlaLs::Result::UNSAT)
    {
      goto UNSAT;
    }

    if (res == bzlals::BzlaLs::Result::SAT)
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

  d_time_statistics.check_sat += bzla_util_time_stamp() - start;

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
    assert(bzla_node_is_bv_var(leaf));

    auto iit = d_node_map.find(leaf);
    assert(iit != d_node_map.end());
    const bzlals::BitVector &assignment = d_bzlals->get_assignment(iit->second);
    BzlaBitVector *bv_assignment        = bzla_bv_const(
        d_bzla->mm, assignment.to_string().c_str(), assignment.size());
    bzla_model_add_to_bv(d_bzla, d_bzla->bv_model, leaf, bv_assignment);
    bzla_bv_free(d_bzla->mm, bv_assignment);
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

BzlaPropSolver *
clone_prop_solver(Bzla *clone, Bzla *bzla, BzlaNodeMap *exp_map)
{
  (void) clone;
  (void) bzla;
  (void) exp_map;
  return nullptr;
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
  // TODO
}

void
print_time_stats_prop_solver(BzlaPropSolver *slv)
{
  // TODO
}

void
print_model_prop_solver(BzlaPropSolver *slv, const char *format, FILE *file)
{
  // TODO
}
}  // namespace

BzlaSolver *
bzla_new_prop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaPropSolver *slv = new BzlaPropSolver();
  // TODO: max_nprops, seed
  slv->d_state.reset(new bzla::prop::PropSolverState(bzla, 0, 0));
  slv->kind      = BZLA_PROP_SOLVER_KIND;
  slv->bzla      = bzla;
  slv->api.clone = (BzlaSolverClone) clone_prop_solver;
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
