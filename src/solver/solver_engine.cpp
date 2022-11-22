#include "solver/solver_engine.h"

#include "solving_context.h"

namespace bzla {

using namespace node;

/* --- SolverEngine public -------------------------------------------------- */

SolverEngine::SolverEngine(SolvingContext& context)
    : d_context(context),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_assertions(context.assertions()),
      d_register_assertion_cache(&d_backtrack_mgr),
      d_register_term_cache(&d_backtrack_mgr),
      d_sat_state(Result::UNKNOWN),
      d_in_solving_mode(false),
      d_stats(statistics()),
      d_bv_solver(*this),
      d_fp_solver(*this),
      d_fun_solver(*this),
      d_array_solver(*this)
{
}

Result
SolverEngine::solve()
{
  // Process unprocessed assertions.
  process_assertions();

  d_in_solving_mode = true;
  do
  {
    // Process lemmas generated in previous iteration.
    process_lemmas();

    d_sat_state = d_bv_solver.solve();
    if (d_sat_state == Result::UNSAT)
    {
      break;
    }
    assert(d_sat_state == Result::SAT);
    // TODO: process lemmas after each check()?
    d_fp_solver.check();
    d_array_solver.check();
    d_fun_solver.check();
    // d_quant_solver.check();
  } while (!d_lemmas.empty());
  d_in_solving_mode = false;
  // TODO: still need to check whether all solvers are done or if there are
  //       still checks pending

  return d_sat_state;
}

Node
SolverEngine::value(const Node& term)
{
  assert(d_sat_state == Result::SAT);

  if (d_in_solving_mode)
  {
    process_term(term);
  }

  const Type& type = term.type();
  if (type.is_bool() || type.is_bv())
  {
    return d_bv_solver.value(term);
  }
  else if (type.is_fp() || type.is_rm())
  {
    return d_fp_solver.value(term);
  }
  else if (type.is_array())
  {
    return d_array_solver.value(term);
  }
  else if (type.is_fun())
  {
    return d_fun_solver.value(term);
  }
  assert(false);
  return Node();
}

void
SolverEngine::lemma(const Node& lemma)
{
  assert(lemma.type().is_bool());
  Node rewritten = rewriter().rewrite(lemma);
  // Lemmas should never simplify to true
  assert(!rewritten.is_value() || !rewritten.value<bool>());
  auto [it, inserted] = d_lemma_cache.insert(rewritten);
  // There can be duplicates if we add more than one lemma per round.
  if (inserted)
  {
    ++d_stats.num_lemmas;
    d_lemmas.push_back(rewritten);
  }
}

Rewriter&
SolverEngine::rewriter()
{
  return d_context.rewriter();
}

const option::Options&
SolverEngine::options() const
{
  return d_context.options();
}

backtrack::BacktrackManager*
SolverEngine::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

util::Statistics&
SolverEngine::statistics()
{
  return d_statistics;
}

/* --- SolverEngine private ------------------------------------------------- */

bool
SolverEngine::is_quant_leaf(const Node& term)
{
  return term.kind() == Kind::FORALL;
}

void
SolverEngine::sync_scope(size_t level)
{
  while (d_backtrack_mgr.num_levels() < level)
  {
    d_backtrack_mgr.push();
  }
}

void
SolverEngine::process_assertions()
{
  while (!d_assertions.empty())
  {
    size_t level = d_assertions.level(d_assertions.begin());

    // Sync backtrack manager to level. This is required if there are levels
    // that do not contain any assertions.
    sync_scope(level);

    // Create vector for current level
    preprocess::AssertionVector assertions(d_assertions);
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      process_assertion(assertions[i], level == 0);
    }

    // Advance assertions to next level
    d_assertions.set_index(d_assertions.begin() + assertions.size());
  }
  assert(d_assertions.empty());

  // Sync backtrack manager to level. This is required if there are levels
  // that do not contain any assertions.
  sync_scope(d_context.backtrack_mgr()->num_levels());
}

void
SolverEngine::process_assertion(const Node& assertion, bool top_level)
{
  // Send assertion to bit-vector solver.
  auto [it, inserted] = d_register_assertion_cache.insert(assertion);
  if (inserted)
  {
    d_bv_solver.register_assertion(assertion, top_level);
  }
  process_term(assertion);
}

void
SolverEngine::process_term(const Node& term)
{
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_register_term_cache.insert(cur);
    if (inserted)
    {
      if (fp::FpSolver::is_leaf(cur))
      {
        d_fp_solver.register_term(cur);
      }
      else if (array::ArraySolver::is_leaf(cur))
      {
        d_array_solver.register_term(cur);
      }
      else if (fun::FunSolver::is_leaf(cur))
      {
        d_fun_solver.register_term(cur);
      }
      else if (is_quant_leaf(cur))
      {
        assert(false);
        // d_quant_solver.register_term(cur);
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

void
SolverEngine::process_lemmas()
{
  for (const Node& lemma : d_lemmas)
  {
    // TODO: check if we always want to add lemmas at the top level
    process_assertion(lemma, true);
  }
  d_lemmas.clear();
}

SolverEngine::Statistics::Statistics(util::Statistics& stats)
    : num_lemmas(stats.new_stat<uint64_t>("solver::lemmas"))
{
}

}  // namespace bzla
