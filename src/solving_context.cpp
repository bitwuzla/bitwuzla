#include "solving_context.h"

#include <cassert>

#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"

namespace bzla {

using namespace node;

/* --- SolvingContext public ----------------------------------------------- */

SolvingContext::SolvingContext()
    : d_assertions(&d_backtrack_mgr),
      d_preprocessor(*this),
      d_rewriter(),
      d_bv_solver(*this)
{
}

Result
SolvingContext::solve()
{
  d_preprocessor.preprocess();
  d_sat_state = d_bv_solver.check();
  return d_sat_state;
}

void
SolvingContext::assert_formula(const Node& formula)
{
  assert(formula.type().is_bool());
  node_ref_vector visit{formula};
  unordered_node_ref_set cache;

  // Flatten AND
  // TODO: Requires tracking for unsat cores
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::AND)
      {
        visit.insert(visit.end(), cur.rbegin(), cur.rend());
      }
      else
      {
        d_assertions.push_back(cur);
      }
    }
  } while (!visit.empty());
}

Node
SolvingContext::get_value(const Node& term)
{
  assert(d_sat_state == Result::SAT);

  const Type& type = term.type();
  if (type.is_bool() || type.is_bv())
  {
    return d_bv_solver.value(term);
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
