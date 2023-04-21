#include "solving_context.h"

#include <cassert>
#include <iostream>

#include "check/check_model.h"
#include "check/check_unsat_core.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"

namespace bzla {

using namespace node;

/* --- SolvingContext public ----------------------------------------------- */

SolvingContext::SolvingContext(const option::Options& options)
    : d_env(options),
      d_assertions(&d_backtrack_mgr),
      d_original_assertions(&d_backtrack_mgr),
      d_preprocessor(*this),
      d_solver_engine(*this)
{
}

Result
SolvingContext::solve()
{
#ifndef NDEBUG
  check_no_free_variables();
#endif
  preprocess();
  d_sat_state = d_solver_engine.solve();
  if (d_env.options().verbosity() > 0)
  {
    d_env.statistics().print();
  }

#ifndef NDEBUG
  if (d_sat_state == Result::SAT && options().dbg_check_model())
  {
    check::CheckModel cm(*this);
    assert(cm.check());
  }
  else if (d_sat_state == Result::UNSAT && options().dbg_check_unsat_core())
  {
    check::CheckUnsatCore cuc(*this);
    assert(cuc.check());
  }
#endif
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
  if (d_assertions.push_back(formula))
  {
    d_original_assertions.push_back(formula);
  }
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
  res = d_preprocessor.post_process_unsat_core(core);

#ifndef NDEBUG
  std::unordered_set<Node> orig(d_original_assertions.begin(),
                                d_original_assertions.end());
  for (const Node& a : res)
  {
    // We should always be able to trace back to the original assertion, if
    // not, some information is not properly tracked in the preprocessor.
    assert(orig.find(a) != orig.end());
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

const backtrack::vector<Node>&
SolvingContext::original_assertions() const
{
  return d_original_assertions;
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

void
SolvingContext::check_no_free_variables() const
{
  std::vector<Node> visit;
  std::unordered_map<Node, bool> cache;
  std::unordered_map<Node, uint64_t> bound_vars;

  std::unordered_map<Node, std::unordered_set<Node>> free_vars;
  for (size_t i = 0; i < d_assertions.size(); ++i)
  {
    const Node& assertion = d_assertions[i];
    visit.push_back(assertion);
    do
    {
      const Node& cur = visit.back();

      auto [it, inserted] = cache.emplace(cur, false);
      if (inserted)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      else if (!it->second)
      {
        it->second = true;
        if (cur.kind() == Kind::VARIABLE)
        {
          free_vars[cur] = {cur};
        }
        else
        {
          auto& vars = free_vars[cur];
          for (const Node& c : cur)
          {
            auto it = free_vars.find(c);
            if (it != free_vars.end())
            {
              vars.insert(it->second.begin(), it->second.end());
            }
          }
        }
        if (cur.kind() == Kind::FORALL || cur.kind() == Kind::EXISTS
            || cur.kind() == Kind::LAMBDA)
        {
          free_vars[cur].erase(cur[0]);
        }
      }
      visit.pop_back();
    } while (!visit.empty());

    auto it = free_vars.find(assertion);
    if (it != free_vars.end() && !it->second.empty())
    {
      std::cerr << "Found free variable(s) in assertion" << std::endl;
      abort();
    }
  }
}

}  // namespace bzla
