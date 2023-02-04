#include "solver/solver_engine.h"

#include "env.h"
#include "solving_context.h"
#include "printer/printer.h"

namespace bzla {

using namespace node;

/* --- SolverEngine public -------------------------------------------------- */

SolverEngine::SolverEngine(SolvingContext& context)
    : d_context(context),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_assertions(context.assertions()),
      d_register_assertion_cache(&d_backtrack_mgr),
      d_register_term_cache(&d_backtrack_mgr),
      d_lemma_cache(&d_backtrack_mgr),
      d_sat_state(Result::UNKNOWN),
      d_in_solving_mode(false),
      d_stats(context.env().statistics()),
      d_env(context.env()),
      d_logger(d_env.logger()),
      d_solver_state(*this),
      d_bv_solver(context.env(), d_solver_state),
      d_fp_solver(context.env(), d_solver_state),
      d_fun_solver(context.env(), d_solver_state),
      d_array_solver(context.env(), d_solver_state),
      d_quant_solver(context.env(), d_solver_state)
{
}

Result
SolverEngine::solve()
{
  util::Timer timer(d_stats.time_solve);

  // Process unprocessed assertions.
  process_assertions();

  d_in_solving_mode = true;
  do
  {
    // Reset term registration flag
    d_new_terms_registered = false;

    // Process lemmas generated in previous iteration.
    process_lemmas();

    d_sat_state = d_bv_solver.solve();
    if (d_sat_state != Result::SAT)
    {
      break;
    }
    d_fp_solver.check();
    if (!d_lemmas.empty())
    {
      continue;
    }
    d_array_solver.check();
    if (!d_lemmas.empty())
    {
      continue;
    }
    d_fun_solver.check();
    if (!d_lemmas.empty())
    {
      continue;
    }
    bool quant_done = d_quant_solver.check();
    if (!quant_done)
    {
      d_sat_state = Result::UNKNOWN;
    }

    // If new terms were registered during the check phase, we have to make sure
    // that all theory solvers are able to check newly registered terms.
  } while (!d_lemmas.empty() || d_new_terms_registered);
  d_in_solving_mode = false;

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
  Log(2) << "lemma: " << lemma;
  Node rewritten = d_env.rewriter().rewrite(lemma);
  // Lemmas should never simplify to true
  assert(!rewritten.is_value() || !rewritten.value<bool>());
  auto [it, inserted] = d_lemma_cache.insert(rewritten);
  // Solvers should not send lemma duplicates.
  assert(inserted);
  // There can be duplicates if we add more than one lemma per round.
  if (inserted)
  {
    ++d_stats.num_lemmas;
    d_lemmas.push_back(rewritten);
  }
}

backtrack::BacktrackManager*
SolverEngine::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

/* --- SolverEngine private ------------------------------------------------- */

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
    d_quant_solver.register_assertion(assertion);
  }
  process_term(assertion);
}

void
SolverEngine::process_term(const Node& term)
{
  util::Timer timer(d_stats.time_register_term);
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_register_term_cache.insert(cur);
    if (inserted)
    {
      if (array::ArraySolver::is_theory_leaf(cur))
      {
        d_array_solver.register_term(cur);
        d_new_terms_registered = true;
      }
      else if (fun::FunSolver::is_theory_leaf(cur))
      {
        d_fun_solver.register_term(cur);
        d_new_terms_registered = true;
      }
      else if (quant::QuantSolver::is_theory_leaf(cur))
      {
        d_quant_solver.register_term(cur);
        d_new_terms_registered = true;
      }
      else
      {
        if (fp::FpSolver::is_theory_leaf(cur))
        {
          d_fp_solver.register_term(cur);
          d_new_terms_registered = true;
        }
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
    : num_lemmas(stats.new_stat<uint64_t>("solver::lemmas")),
      time_register_term(
          stats.new_stat<util::TimerStatistic>("solver::time_register_term")),
      time_solve(stats.new_stat<util::TimerStatistic>("solver::time_solve"))
{
}

}  // namespace bzla
