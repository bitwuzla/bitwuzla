/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/fp_solver.h"

#include "env.h"
#include "node/node_kind.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "rewrite/rewriter.h"
#include "solver/array/array_solver.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "solver/fun/fun_solver.h"
#include "solver/quant/quant_solver.h"

namespace bzla::fp {

using namespace bzla::node;

bool
FpSolver::is_theory_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORMAL || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORMAL || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LEQ || k == Kind::FP_LT
         || k == Kind::FP_TO_SBV || k == Kind::FP_TO_UBV
         || (k == Kind::EQUAL
             && (term[0].type().is_fp() || term[0].type().is_rm()));
}

FpSolver::FpSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_word_blaster(state),
      d_word_blast_queue(state.backtrack_mgr()),
      d_word_blast_index(state.backtrack_mgr())
{
}

FpSolver::~FpSolver() {}

bool
FpSolver::check()
{
  Log(1);
  Log(1) << "*** check fp";

  reset_cached_values();
  NodeManager& nm = NodeManager::get();
  for (size_t i = d_word_blast_index.get(), size = d_word_blast_queue.size();
       i < size;
       ++i)
  {
    const Node& node = d_word_blast_queue[i];
    Node wb = d_word_blaster.word_blast(node);

    if (wb == node) continue;

    if (node.type().is_bool())
    {
      assert(wb.type().is_bv() && wb.type().bv_size() == 1);
      d_solver_state.lemma(
          nm.mk_node(Kind::EQUAL, {node, node::utils::bv1_to_bool(wb)}));
    }
    else
    {
      assert(node.type().is_bv() && node.type() == wb.type());
      d_solver_state.lemma(nm.mk_node(Kind::EQUAL, {node, wb}));
    }
  }
  d_word_blast_index = d_word_blast_queue.size();
  return true;
}

Node
FpSolver::value(const Node& term)
{
  assert(term.kind() == Kind::CONSTANT || term.kind() == Kind::APPLY
         || term.kind() == Kind::SELECT || term.kind() == Kind::FP_TO_SBV
         || term.kind() == Kind::FP_TO_UBV || term.kind() == Kind::FP_MIN
         || term.kind() == Kind::FP_MAX);

  // We only have to word-blast partial operators to compute a value. If a
  // constant, select or function application was already word-blasted, we
  // compute the value based on the word-blasted bit-vector structure.
  if (d_word_blaster.is_word_blasted(term)
      || term.kind() == node::Kind::FP_TO_SBV
      || term.kind() == node::Kind::FP_TO_UBV
      || term.kind() == node::Kind::FP_MIN || term.kind() == node::Kind::FP_MAX)
  {
    NodeManager& nm = NodeManager::get();
    Node wb         = d_env.rewriter().rewrite(d_word_blaster.word_blast(term));
    Node value      = d_solver_state.value(wb);
    assert(value.type().is_bv());
    if (term.type().is_bv())
    {
      return value;
    }
    const BitVector& bv = value.value<BitVector>();
    if (term.type().is_rm())
    {
      uint64_t rm = bv.to_uint64();
      return nm.mk_value(static_cast<RoundingMode>(rm));
    }
    assert(term.type().is_fp());
    return nm.mk_value(FloatingPoint(term.type(), bv));
  }
  return node::utils::mk_default_value(term.type());
}

void
FpSolver::register_term(const Node& term)
{
  d_word_blast_queue.push_back(term);
}

}  // namespace bzla::fp
