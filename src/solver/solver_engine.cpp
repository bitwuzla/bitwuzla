#include "solver/solver_engine.h"

#include "solving_context.h"

namespace bzla {

using namespace node;

/* --- SolverEngine public -------------------------------------------------- */

SolverEngine::SolverEngine(SolvingContext& context)
    : d_context(context),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_assertions(context.assertions()),
      d_register_cache(&d_backtrack_mgr),
      d_sat_state(Result::UNKNOWN),
      d_bv_solver(*this),
      d_fun_solver(*this)
{
}

Result
SolverEngine::solve()
{
  // Process unprocessed assertions.
  process_assertions();

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
    // d_fp_solver.check();
    // d_array_solver.check();
    d_fun_solver.check();
    // d_quant_solver.check();
  } while (!d_lemmas.empty());

  return d_sat_state;
}

Node
SolverEngine::value(const Node& term)
{
  assert(d_sat_state == Result::SAT);

  const Type& type = term.type();
  if (type.is_bool() || type.is_bv())
  {
    return d_bv_solver.value(term);
  }
  else if (type.is_fp() || type.is_rm())
  {
    // return d_fp_solver.value(term);
  }
  else if (type.is_array())
  {
    // return d_array_solver.value(term);
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

/* --- SolverEngine private ------------------------------------------------- */

bool
SolverEngine::is_fp_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::FP_IS_INF || k == Kind::FP_IS_NAN || k == Kind::FP_IS_NEG
         || k == Kind::FP_IS_NORM || k == Kind::FP_IS_POS
         || k == Kind::FP_IS_SUBNORM || k == Kind::FP_IS_ZERO
         || k == Kind::FP_EQUAL || k == Kind::FP_LE || k == Kind::FP_LT
         || k == Kind::FP_TO_SBV || k == Kind::FP_TO_UBV
         || (k == Kind::EQUAL
             && (term[0].type().is_fp() || term[0].type().is_rm()));
}

bool
SolverEngine::is_array_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::SELECT || (k == Kind::EQUAL && (term[0].type().is_array()));
}

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
      process_assertion(assertions[i], level);
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
SolverEngine::process_assertion(const Node& assertion, size_t level)
{
  // Send assertion to bit-vector solver.
  if (d_register_cache.find(assertion) == d_register_cache.end())
  {
    d_bv_solver.register_assertion(assertion, level == 0);
  }

  // Send theory leafs to corresponding solvers.
  node::node_ref_vector visit{assertion};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_register_cache.insert(cur);
    if (inserted)
    {
      if (is_fp_leaf(cur))
      {
        assert(false);
        // d_fp_solver.register_term(cur);
      }
      else if (is_array_leaf(cur))
      {
        assert(false);
        // d_array_solver.register_term(cur);
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
    // TODO: check if this is what we want
    process_assertion(lemma, true);
  }
  d_lemmas.clear();
}

}  // namespace bzla
