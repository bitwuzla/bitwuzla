/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_prop_solver.h"

#include <iostream>

#include "ls/bv/bitvector_domain.h"
#include "ls/ls_bv.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "option/option.h"
#include "solver/bv/bv_solver.h"
#include "solver/result.h"
#include "solving_context.h"
#include "util/logger.h"

namespace bzla::bv {

using namespace bzla::node;

BvPropSolver::BvPropSolver(Env& env,
                           SolverState& state,
                           BvBitblastSolver& bb_solver)
    : Solver(env, state),
      d_bb_solver(bb_solver),
      d_ls_backtrack(state.backtrack_mgr(), nullptr),
      d_stats(env.statistics(), "solver::bv::prop::")
{
  const option::Options& options = d_env.options();

  d_ls.reset(new ls::LocalSearchBV(
      options.prop_nprops(), options.prop_nupdates(), options.seed()));

  d_ls->d_options.use_ineq_bounds        = options.prop_ineq_bounds();
  d_ls->d_options.use_opt_lt_concat_sext = options.prop_opt_lt_concat_sext();
  d_ls->d_options.prob_pick_inv_value    = options.prop_prob_pick_inv_value();
  d_ls->d_options.use_path_sel_essential =
      options.prop_path_sel() == option::PropPathSelection::ESSENTIAL;

  d_ls->d_options.prob_pick_ess_input =
      1000 - options.prop_prob_pick_random_input();

  d_ls->set_log_level(options.log_level());
  d_ls->init();

  d_ls_backtrack.d_ls = d_ls.get();

  d_use_sext       = options.prop_sext();
  d_use_const_bits = options.prop_const_bits();
}

BvPropSolver::~BvPropSolver() {}

Result
BvPropSolver::solve()
{
  util::Timer timer(d_stats.time_check);

  ++d_stats.num_checks;

  Result sat_result = Result::UNKNOWN;

  uint32_t verbosity = d_env.options().verbosity();
  uint64_t nprops    = d_env.options().prop_nprops();
  uint64_t nupdates  = d_env.options().prop_nupdates();

  uint32_t progress_steps     = 100;
  uint32_t progress_steps_inc = progress_steps * 10;

  if (d_env.options().prop_normalize())
  {
    d_ls->normalize();
  }

  // incremental: increase limit by given nprops/nupdates
  if (nprops)
  {
    nprops += d_ls->d_statistics.d_nprops;
  }
  d_ls->set_max_nprops(nprops);
  Log(1) << "set propagation limit to " << nprops;

  if (nupdates)
  {
    nupdates += d_ls->d_statistics.d_nupdates;
  }
  d_ls->set_max_nupdates(nupdates);
  Log(1) << "set cone update limit to " << nupdates;

  for (uint32_t j = 0;; ++j)
  {
    if (d_env.terminate() || (nprops && d_ls->d_statistics.d_nprops >= nprops)
        || (nupdates && d_ls->d_statistics.d_nupdates >= nupdates))
    {
      assert(sat_result == Result::UNKNOWN);
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
  sat_result = Result::SAT;
  goto DONE;
UNSAT:
  sat_result = Result::UNSAT;
DONE:
  d_stats.num_moves += d_ls->d_statistics.d_nmoves;
  d_stats.num_props += d_ls->d_statistics.d_nprops;
  d_stats.num_props_inv += d_ls->d_statistics.d_nprops_inv;
  d_stats.num_props_cons += d_ls->d_statistics.d_nprops_cons;
  d_stats.num_updates += d_ls->d_statistics.d_nupdates;
  d_stats.num_conflicts += d_ls->d_statistics.d_nconf_total;
#ifndef NDEBUG
  d_stats.num_props_inv_per_kind.import_map(d_ls->d_statistics.d_ninv);
  d_stats.num_props_cons_per_kind.import_map(d_ls->d_statistics.d_ncons);
  d_stats.num_props_conflicts_per_kind.import_map(d_ls->d_statistics.d_nconf);
#endif

  print_progress();

  return sat_result;
}

void
BvPropSolver::register_assertion(const Node& assertion,
                                 bool top_level,
                                 bool is_lemma)
{
  (void) top_level;
  (void) is_lemma;

  d_stats.num_assertions += 1;

  node::node_ref_vector visit{assertion};
  node::unordered_node_ref_map<bool> cache;

  if (d_use_const_bits)
  {
    d_bb_solver.bitblaster().bitblast(assertion);
  }

  do
  {
    const Node& cur = visit.back();

    if (d_node_map.find(cur) != d_node_map.end())
    {
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = cache.emplace(cur, true);

    if (inserted)
    {
      if (!BvSolver::is_leaf(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second)
    {
      it->second      = false;
      d_node_map[cur] = mk_node(cur);
      visit.pop_back();
    }
  } while (!visit.empty());

  uint64_t id = d_node_map.at(assertion);
  d_ls->register_root(id, top_level);
  // Reverse map assertions for unsat cores.
  d_root_id_node_map[id] = assertion;
}

Node
BvPropSolver::value(const Node& term)
{
  assert(BvSolver::is_leaf(term));
  auto it = d_node_map.find(term);
  if (it == d_node_map.end())
  {
    return utils::mk_default_value(term.type());
  }
  const BitVector& value = d_ls->get_assignment(it->second);
  if (term.type().is_bool())
  {
    return NodeManager::get().mk_value(value.is_true());
  }
  return NodeManager::get().mk_value(value);
}

void
BvPropSolver::unsat_core(std::vector<Node>& core) const
{
  // The LocalSearchBV library can only determine unsat if a single root is
  // false. Hence, the unsat core always consists of one root.
  auto it = d_root_id_node_map.find(d_ls->get_false_root());
  assert(it != d_root_id_node_map.end());
  core.push_back(it->second);
}

uint64_t
BvPropSolver::mk_node(const Node& node)
{
  assert(node.type().is_bv() || node.type().is_bool());

  uint64_t res  = 0;
  uint64_t size = node.type().is_bool() ? 1 : node.type().bv_size();

  bzla::ls::BitVectorDomain domain(size);

  if (node.is_value())
  {
    if (node.type().is_bv())
    {
      domain.fix(node.value<BitVector>());
    }
    else
    {
      assert(node.type().is_bool());
      assert(domain.size() == 1);
      domain.fix_bit(0, node.value<bool>());
    }
  }
  else if (d_use_const_bits)
  {
    const auto& bits = d_bb_solver.bitblaster().bits(node);
    assert(bits.size() == size);

    for (uint64_t i = 0; i < size; ++i)
    {
      uint64_t idx = size - 1 - i;
      if (bits[i].is_true())
      {
        domain.fix_bit(idx, true);
        d_stats.num_bits_fixed += 1;
      }
      else if (bits[i].is_false())
      {
        domain.fix_bit(idx, false);
        d_stats.num_bits_fixed += 1;
      }
    }
    d_stats.num_bits_total += size;
  }

  std::string symbol =
      node.symbol() ? node.symbol()->get() : "@t" + std::to_string(node.id());

  switch (node.kind())
  {
    case Kind::BV_ADD:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_ADD,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_AND:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_AND,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_ASHR:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_ASHR,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_CONCAT:
      assert(node.num_children() == 2);
      {
        Node child;
        if (d_use_sext && node::utils::is_bv_sext(node, child))
        {
          res = d_ls->mk_node(bzla::ls::NodeKind::BV_SEXT,
                              domain,
                              {d_node_map.at(child)},
                              {node[0].type().bv_size()},
                              symbol);
        }
        else
        {
          res = d_ls->mk_node(bzla::ls::NodeKind::BV_CONCAT,
                              domain,
                              {d_node_map.at(node[0]), d_node_map.at(node[1])},
                              {},
                              symbol);
        }
      }
      break;
    case Kind::BV_EXTRACT:
      assert(node.num_children() == 1);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_EXTRACT,
                          domain,
                          {d_node_map.at(node[0])},
                          {node.index(0), node.index(1)},
                          symbol);
      break;
    case Kind::BV_MUL:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_MUL,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_NOT:
      assert(node.num_children() == 1);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_NOT,
                          domain,
                          {d_node_map.at(node[0])},
                          {},
                          symbol);
      break;
    case Kind::BV_ULT:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_ULT,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_SHL:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SHL,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_SLT:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SLT,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_SHR:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_SHR,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_UDIV:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_UDIV,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_UREM:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_UREM,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_XOR:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::BV_XOR,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::AND:
      assert(node.num_children() == 2);
      res = d_ls->mk_node(bzla::ls::NodeKind::AND,
                          domain,
                          {d_node_map.at(node[0]), d_node_map.at(node[1])},
                          {},
                          symbol);
      break;
    case Kind::BV_COMP:
    case Kind::EQUAL:
      assert(node.num_children() == 2);
      if (BvSolver::is_leaf(node))
      {
        res = d_ls->mk_node(domain.lo(), domain, symbol);
      }
      else
      {
        res = d_ls->mk_node(bzla::ls::NodeKind::EQ,
                            domain,
                            {d_node_map.at(node[0]), d_node_map.at(node[1])},
                            {},
                            symbol);
      }
      break;
    case Kind::ITE:
      assert(node.num_children() == 3);
      res = d_ls->mk_node(bzla::ls::NodeKind::ITE,
                          domain,
                          {d_node_map.at(node[0]),
                           d_node_map.at(node[1]),
                           d_node_map.at(node[2])},
                          {},
                          symbol);
      break;
    case Kind::NOT:
      assert(node.num_children() == 1);
      res = d_ls->mk_node(bzla::ls::NodeKind::NOT,
                          domain,
                          {d_node_map.at(node[0])},
                          {},
                          symbol);
      break;
    default:
      assert(BvSolver::is_leaf(node));
      res = d_ls->mk_node(domain.lo(), domain, symbol);
  }

  return res;
}

void
BvPropSolver::print_progress() const
{
  if (d_logger.is_msg_enabled(2))
  {
    size_t nroots_sat   = d_ls->get_num_roots_sat();
    size_t nroots_total = d_ls->get_num_roots();
    double perc_sat     = static_cast<double>(nroots_sat) / nroots_total * 100;
    Msg(1) << nroots_sat << "/" << nroots_total << " roots satisfied ("
           << std::setprecision(3) << perc_sat
           << "%), moves: " << d_ls->d_statistics.d_nmoves
           << ", propagation steps: " << d_ls->d_statistics.d_nprops
           << ", updates: " << d_ls->d_statistics.d_nupdates;
  }
}

BvPropSolver::Statistics::Statistics(util::Statistics& stats,
                                     const std::string& prefix)
    : num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      num_assertions(stats.new_stat<uint64_t>(prefix + "num_assertions")),
      num_bits_fixed(stats.new_stat<uint64_t>(prefix + "num_bits_fixed")),
      num_bits_total(stats.new_stat<uint64_t>(prefix + "num_bits_total")),
      num_moves(stats.new_stat<uint64_t>(prefix + "num_moves")),
      num_props(stats.new_stat<uint64_t>(prefix + "num_props")),
      num_props_inv(stats.new_stat<uint64_t>(prefix + "num_props_inv")),
      num_props_cons(stats.new_stat<uint64_t>(prefix + "num_props_cons")),
      num_updates(stats.new_stat<uint64_t>(prefix + "num_updates")),
      num_conflicts(stats.new_stat<uint64_t>(prefix + "num_conflicts")),
#ifndef NDEBUG
      num_props_inv_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_props_inv_per")),
      num_props_cons_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_props_cons_per")),
      num_props_conflicts_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_conflicts_per")),
#endif
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}
}  // namespace bzla::bv
