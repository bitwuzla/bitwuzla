#include "solving_context.h"

#include <cassert>
#include <iostream>

#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
namespace bzla {

using namespace node;

/* --- SolvingContext public ----------------------------------------------- */

SolvingContext::SolvingContext(const option::Options& options)
    : d_env(options),
      d_assertions(&d_backtrack_mgr),
#ifndef NDEBUG
      d_original_assertions(&d_backtrack_mgr),
#endif
      d_preprocessor(*this),
      d_solver_engine(*this)
{
}

Result
SolvingContext::solve()
{
  preprocess();
  d_sat_state = d_solver_engine.solve();
  if (d_env.options().verbosity() > 0)
  {
    d_env.statistics().print();
  }
  return d_sat_state;
}

Result
SolvingContext::preprocess()
{
  return d_preprocessor.preprocess();
}

void
SolvingContext::assert_formula(const Node& formula)
{
  assert(formula.type().is_bool());
  d_assertions.push_back(formula);
#ifndef NDEBUG
  d_original_assertions.insert(formula);
#endif
}

Node
SolvingContext::get_value(const Node& term)
{
  assert(d_sat_state == Result::SAT);
  return d_solver_engine.value(d_preprocessor.process(term));
}

std::vector<Node>
SolvingContext::get_unsat_core()
{
  std::vector<Node> res, core;
  d_solver_engine.unsat_core(core);

  // Get unsat core in terms of original input assertions.
  res = d_preprocessor.original_assertions(core);

#ifndef NDEBUG
  for (const Node& a : res)
  {
    // We should always be able to trace back to the original assertion, if
    // not, some information is not properly tracked in the preprocessor.
    assert(d_original_assertions.find(a) != d_original_assertions.end());
  }
#endif

  return res;
}

void
SolvingContext::push()
{
  d_backtrack_mgr.push();
}

void
SolvingContext::pop()
{
  d_backtrack_mgr.pop();
}

const option::Options&
SolvingContext::options() const
{
  return d_env.options();
}

backtrack::AssertionView&
SolvingContext::assertions()
{
  return d_assertions.view();
}

backtrack::BacktrackManager*
SolvingContext::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

Rewriter&
SolvingContext::rewriter()
{
  return d_env.rewriter();
}

Env&
SolvingContext::env()
{
  return d_env;
}

}  // namespace bzla
