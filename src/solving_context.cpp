/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solving_context.h"

#include <cassert>

#include "check/check_model.h"
#include "check/check_unsat_core.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
#include "resource_terminator.h"
#include "solver/fp/symfpu_nm.h"  // Temporary for setting SymFpuNM
#include "util/resources.h"

namespace bzla {

using namespace node;

/* --- SolvingContext public ----------------------------------------------- */

SolvingContext::SolvingContext(NodeManager& nm,
                               const option::Options& options,
                               const std::string& name,
                               bool subsolver)
    : d_env(nm, options, name),
      d_logger(d_env.logger()),
      d_assertions(&d_backtrack_mgr),
      d_original_assertions(&d_backtrack_mgr),
      d_have_quantifiers(&d_backtrack_mgr),
      d_preprocessor(*this),
      d_solver_engine(*this),
      d_subsolver(subsolver),
      d_stats(d_env.statistics())
{
  d_have_quantifiers = false;
}

SolvingContext::~SolvingContext() {}

Result
SolvingContext::solve()
{
  util::Timer timer(d_stats.time_solve);
  fp::SymFpuNM snm(d_env.nm());
  set_resource_limits();
#ifndef NDEBUG
  check_no_free_variables();
#endif
  d_sat_state = preprocess();

  if (d_sat_state == Result::UNKNOWN)
  {
    try
    {
      d_sat_state = d_solver_engine.solve();
    }
    catch (const UnsupportedException& e)
    {
      Warn(!d_subsolver) << e.msg();
      d_sat_state = Result::UNKNOWN;
    }
  }

  if (d_sat_state == Result::SAT && d_have_quantifiers.get()
      && (options().produce_models() || options().dbg_check_model()))
  {
    ensure_model();
  }

  if (d_sat_state == Result::SAT && options().dbg_check_model())
  {
    check::CheckModel cm(*this);
    auto res = cm.check();
    assert(res);
    Warn(!res) << "model check failed";
  }
  else if (d_sat_state == Result::UNSAT && options().dbg_check_unsat_core())
  {
    check::CheckUnsatCore cuc(*this);
    auto res = cuc.check();
    assert(res);
    Warn(!res) << "unsat core check failed";
  }

  d_stats.max_memory = util::maximum_memory_usage();
  return d_sat_state;
}

Result
SolvingContext::preprocess()
{
  fp::SymFpuNM snm(d_env.nm());
  if (d_env.options().verbosity() > 0)
  {
    compute_formula_statistics(d_stats.formula_kinds_pre);
  }
  auto res = d_preprocessor.preprocess();
  if (d_env.options().verbosity() > 0)
  {
    compute_formula_statistics(d_stats.formula_kinds_post);
  }
  return res;
}

void
SolvingContext::assert_formula(const Node& formula)
{
  assert(formula.type().is_bool());
  if (d_assertions.push_back(formula))
  {
    if (formula.node_info().quantifier)
    {
      d_have_quantifiers = true;
    }
    d_original_assertions.push_back(formula);
  }
}

Node
SolvingContext::get_value(const Node& term)
{
  assert(d_sat_state == Result::SAT);
  fp::SymFpuNM snm(d_env.nm());
  try
  {
    return d_solver_engine.value(d_preprocessor.process(term));
  }
  catch (const ComputeValueException& e)
  {
    // This only happens if we encounter a quantifier that was not registered
    // and therefore cannot we cannot determine its value without calling
    // solve() again. We instead return the original term.
    Log(2) << "encountered unregistered term while computing value: "
           << e.node();
    return term;
  }
}

std::vector<Node>
SolvingContext::get_unsat_core()
{
  fp::SymFpuNM snm(d_env.nm());
  std::vector<Node> res, core;
  if (d_assertions.is_inconsistent())
  {
    core.push_back(d_env.nm().mk_value(false));
  }
  else
  {
    d_solver_engine.unsat_core(core);
  }

  // Get unsat core in terms of original input assertions.
  std::unordered_set<Node> orig(d_original_assertions.begin(),
                                d_original_assertions.end());
  res = d_preprocessor.post_process_unsat_core(core, orig);

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

/* --- SolvingContext private ----------------------------------------------- */

void
SolvingContext::check_no_free_variables() const
{
  std::vector<Node> visit;
  std::unordered_map<Node, bool> cache;
  std::unordered_map<Node, uint64_t> bound_vars;

  for (size_t i = 0; i < d_assertions.size(); ++i)
  {
    std::unordered_map<Node, std::unordered_set<Node>> free_vars;
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
      std::cerr << assertion << std::endl;
      for (const Node& var : it->second)
      {
        std::cerr << "  " << var << std::endl;
      }
      abort();
    }
  }
}

void
SolvingContext::compute_formula_statistics(util::HistogramStatistic& stat)
{
  std::vector<Node> visit;
  for (size_t i = 0, size = d_assertions.size(); i < size; ++i)
  {
    visit.push_back(d_assertions[i]);
  }

  std::unordered_set<Node> cache;
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      stat << cur.kind();
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  }
}

void
SolvingContext::ensure_model()
{
  util::Timer timer(d_stats.time_ensure_model);
  std::unordered_set<Node> cache;
  std::vector<Node> visit, terms;
  bool need_check = false;
  for (const Node& assertion : original_assertions())
  {
    visit.push_back(assertion);
    do
    {
      Node cur = visit.back();
      visit.pop_back();
      if (cache.insert(cur).second)
      {
        if (cur.is_const())
        {
          terms.push_back(d_preprocessor.process(cur));
        }
        else if (cur.kind() == Kind::FORALL || cur.kind() == Kind::EXISTS)
        {
          need_check = true;
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    } while (!visit.empty());
  }

  // We only need an additional check if quantifiers are involved. It can
  // happen that, due to preprocessing, not all quantified formulas required to
  // build a model were checked by the quantifier solver (e.g. if substituted
  // away by substitution preprocessing pass).
  if (need_check)
  {
    d_solver_engine.ensure_model(terms);
  }
}

void
SolvingContext::set_resource_limits()
{
  auto time_limit = d_env.options().time_limit_per();
  auto memory_limit = d_env.options().memory_limit();
  if (time_limit > 0 || memory_limit > 0)
  {
    // Initialize resource terminator
    if (d_resource_terminator == nullptr)
    {
      d_resource_terminator.reset(new ResourceTerminator());
    }

    // Do not overwrite existing user-defined terminator, wrap it with resource
    // terminator.
    auto terminator = d_env.terminator();
    if (terminator != d_resource_terminator.get())
    {
      d_resource_terminator->set_terminator(terminator);
      d_env.configure_terminator(d_resource_terminator.get());
    }
    // Set resource limits.
    d_resource_terminator->set_time_limit(time_limit);
    d_resource_terminator->set_memory_limit(memory_limit);
  }
}

SolvingContext::Statistics::Statistics(util::Statistics& stats)
    : time_solve(
          stats.new_stat<util::TimerStatistic>("solving_context::time_solve")),
      time_ensure_model(stats.new_stat<util::TimerStatistic>(
          "solving_context::time_ensure_model")),
      max_memory(stats.new_stat<uint64_t>("solving_context::max_memory")),
      formula_kinds_pre(
          stats.new_stat<util::HistogramStatistic>("formula::pre::node")),
      formula_kinds_post(
          stats.new_stat<util::HistogramStatistic>("formula::post::node"))
{
}

}  // namespace bzla
