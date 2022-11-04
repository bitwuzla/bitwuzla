#include "solving_context.h"

#include <cassert>

#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"

namespace bzla {

using namespace node;

/* --- SolvingContext public ----------------------------------------------- */

SolvingContext::SolvingContext(const option::Options& options)
    : d_options(options),
      d_assertions(&d_backtrack_mgr),
      d_preprocessor(*this),
      d_rewriter(),
      d_bv_solver(*this)
{
}

Result
SolvingContext::solve()
{
  preprocess();
  d_sat_state = d_bv_solver.check();
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
}

Node
SolvingContext::get_value(const Node& term)
{
  assert(d_sat_state == Result::SAT);

  const Type& type = term.type();
  if (type.is_bool() || type.is_bv())
  {
    return d_bv_solver.value(d_preprocessor.process(term));
  }

  // TODO: Handle more types.
  assert(false);
  return Node();
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
  return d_options;
}

backtrack::AssertionView&
SolvingContext::assertions()
{
  return d_assertions.create_view();
}

backtrack::BacktrackManager*
SolvingContext::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

Rewriter&
SolvingContext::rewriter()
{
  return d_rewriter;
}

}  // namespace bzla
