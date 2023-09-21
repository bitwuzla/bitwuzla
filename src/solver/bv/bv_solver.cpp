/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_solver.h"

#include "bv/bitvector.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "solver/bv/bv_bitblast_solver.h"
#include "solving_context.h"

namespace bzla::bv {

using namespace bzla::node;

/* --- BvBitblastSolver public ---------------------------------------------- */

bool
BvSolver::is_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::CONSTANT
         || k == Kind::VALUE
         // Quantifiers
         || k == Kind::FORALL
         || k == Kind::EXISTS
         // Array selects and function applications
         || k == Kind::SELECT
         || k == Kind::APPLY
         // FP predicates
         || k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORMAL || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORMAL || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LEQ
         || k == Kind::FP_LT
         // FP to BV conversion
         || k == Kind::FP_TO_SBV
         || k == Kind::FP_TO_UBV
         // Equalities over terms that are not Booleans or bit-vectors
         || (k == Kind::EQUAL && !term[0].type().is_bool()
             && !term[0].type().is_bv());
}

BvSolver::BvSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_bitblast_solver(env, state),
      d_prop_solver(env, state, d_bitblast_solver),
      d_cur_solver(env.options().bv_solver()),
      d_solver_mode(env.options().bv_solver()),
      d_stats(env.statistics())
{
}

BvSolver::~BvSolver() {}

void
BvSolver::register_assertion(const Node& assertion,
                             bool top_level,
                             bool is_lemma)
{
  ++d_stats.num_assertions;
  if (d_solver_mode == option::BvSolver::BITBLAST
      || d_solver_mode == option::BvSolver::PREPROP)
  {
    d_bitblast_solver.register_assertion(assertion, top_level, is_lemma);
  }
  if (d_solver_mode == option::BvSolver::PROP
      || d_solver_mode == option::BvSolver::PREPROP)
  {
    d_prop_solver.register_assertion(assertion, top_level, is_lemma);
  }
}

Result
BvSolver::solve()
{
  util::Timer timer(d_stats.time_check);

  if (d_env.terminate())
  {
    return Result::UNKNOWN;
  }

  ++d_stats.num_checks;
  reset_cached_values();
  switch (d_env.options().bv_solver())
  {
    case option::BvSolver::BITBLAST:
      assert(d_cur_solver == option::BvSolver::BITBLAST);
      d_sat_state = d_bitblast_solver.solve();
      break;
    case option::BvSolver::PROP:
      assert(d_cur_solver == option::BvSolver::PROP);
      d_sat_state = d_prop_solver.solve();
      break;
    case option::BvSolver::PREPROP:
      d_cur_solver = option::BvSolver::PROP;
      d_sat_state  = d_prop_solver.solve();
      if (d_sat_state == Result::UNKNOWN)
      {
        d_cur_solver = option::BvSolver::BITBLAST;
        d_sat_state = d_bitblast_solver.solve();
      }
      break;
  }
  return d_sat_state;
}

Node
BvSolver::value(const Node& term)
{
  assert(is_leaf(term));
  assert(term.type().is_bool() || term.type().is_bv());
  if (d_cur_solver == option::BvSolver::BITBLAST)
  {
    return d_bitblast_solver.value(term);
  }
  assert(d_cur_solver == option::BvSolver::PROP);
  return d_prop_solver.value(term);
}

void
BvSolver::unsat_core(std::vector<Node>& core) const
{
  if (d_cur_solver == option::BvSolver::BITBLAST)
  {
    return d_bitblast_solver.unsat_core(core);
  }
  assert(d_cur_solver == option::BvSolver::PROP);
  return d_prop_solver.unsat_core(core);
}

/* --- BvBitblastSolver private --------------------------------------------- */

BvSolver::Statistics::Statistics(util::Statistics& stats)
    : num_checks(stats.new_stat<uint64_t>("solver::bv::num_checks")),
      num_assertions(stats.new_stat<uint64_t>("solver::bv::num_assertions")),
      time_check(stats.new_stat<util::TimerStatistic>("solver::bv::time_check"))
{
}

}  // namespace bzla::bv
