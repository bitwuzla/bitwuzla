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
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

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
         || k == Kind::FP_SYMFPU_EXP || k == Kind::FP_SYMFPU_SIG
         || k == Kind::FP_SYMFPU_SIGN || k == Kind::FP_SYMFPU_INF
         || k == Kind::FP_SYMFPU_NAN || k == Kind::FP_SYMFPU_ZERO
         || (k == Kind::EQUAL
             && (term[0].type().is_fp() || term[0].type().is_rm()));
}

FpSolver::FpSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_word_blaster(env, state),
      d_word_blast_queue(state.backtrack_mgr()),
      d_word_blast_index(state.backtrack_mgr()),
      d_valid_constraints_cache(state.backtrack_mgr())
{
}

FpSolver::~FpSolver() {}

bool
FpSolver::check()
{
  Log(1);
  Log(1) << "*** check fp";

  reset_cached_values();
  NodeManager& nm = d_env.nm();

  // In the incremental case, it can happen that validity constraints (added as
  // lemmas) for FP/RM consts and leafs were registered in the bit-blast solver
  // but never bit-blasted.
  //
  // This only happens if a BV engine other than the bit-blast engine solves an
  // incremental query where an RM/FP const/leaf is word-blasted for the first
  // time, and the corresponding assertions are popped before the next query.
  // This results in the validity lemmas for the const/leaf being registered
  // in the bit-blast solver but never bit-blasted, since the bit-blast solver
  // maintains registered assertions in a backtrackable queue (to be
  // bit-blasted), and thus lemmas get popped before they are bit-blasted.
  //
  // Thus, we have to keep track of which RM/FP consts/leafs are currently
  // "active", and which of them we currently have added validity constraints
  // for. That is, we maintain a backtrackable cache to keep track of which
  // nodes we have seen on the current assertion level, and if we encounter
  // an RM/FP const/leaf that has been word-blasted previously but is not
  // cached, we add the corresponding validity constraints.
  //
  // Note that this will not result in duplicate lemmas (on the node level) in
  // the currently active assertion levels, but may result in bit-blasting
  // lemmas more than once.
  for (size_t i = d_word_blast_index.get(), size = d_word_blast_queue.size();
       i < size;
       ++i)
  {
    const Node& node = d_word_blast_queue[i];

    node_ref_vector visit{node};
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      if (!d_valid_constraints_cache.insert(cur).second)
      {
        continue;
      }
      if (cur.is_const() || WordBlaster::is_leaf(cur))
      {
        // If `cur` has been word-blasted but not in any of the currently active
        // assertion levels, we have to readd the validity lemma.
        if (d_word_blaster.is_word_blasted(cur)
            && !d_word_blaster.is_cur_word_blasted_const(cur))
        {
          d_solver_state.lemma(d_word_blaster.valid(cur).first);
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    } while (!visit.empty());
  }

  // Word-blast nodes that have not yet been word-blasted.
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
          nm.mk_node(Kind::EQUAL, {node, node::utils::bv1_to_bool(nm, wb)}));
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

  NodeManager& nm = d_env.nm();
  // We only have to word-blast partial operators to compute a value. If a
  // constant, select or function application was already word-blasted, we
  // compute the value based on the word-blasted bit-vector structure.
  if (d_word_blaster.is_word_blasted(term)
      || term.kind() == node::Kind::FP_TO_SBV
      || term.kind() == node::Kind::FP_TO_UBV
      || term.kind() == node::Kind::FP_MIN || term.kind() == node::Kind::FP_MAX)
  {
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
    return nm.mk_value(FloatingPoint(
        term.type().fp_exp_size(), term.type().fp_sig_size(), bv));
  }
  return node::utils::mk_default_value(nm, term.type());
}

void
FpSolver::register_term(const Node& term)
{
  d_word_blast_queue.push_back(term);
}

}  // namespace bzla::fp
