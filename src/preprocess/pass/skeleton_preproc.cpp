/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/skeleton_preproc.h"

#include <iostream>
#include <memory>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
#include "sat/cadical.h"

namespace bzla::preprocess::pass {

using namespace node;

/* --- PassSkeletonPreproc public ------------------------------------------- */

PassSkeletonPreproc::PassSkeletonPreproc(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_sat_solver(nullptr),
      d_assertion_lits(backtrack_mgr),
      d_assertions(backtrack_mgr),
      d_reset(backtrack_mgr),
      d_stats(env.statistics(), "preprocess::skeleton::")
{
}

void
PassSkeletonPreproc::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);

  // Disabled if unsat cores enabled.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }

  std::vector<Node> _assertions;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value())
    {
      continue;
    }
    if (!processed(assertion))
    {
      cache_assertion(assertion);
      _assertions.push_back(assertion);
    }
  }

  // No new assertions encoded
  if (_assertions.empty())
  {
    return;
  }

  // Reset SAT solver if assertions were popped
  if (d_reset())
  {
    d_sat_solver.reset(new sat::Cadical());
    d_encode_cache.clear();
    d_reset = false;
    ++d_stats.num_resets;
  }

  // Encode Boolean skeleton
  {
    util::Timer timer(d_stats.time_encode);
    for (const Node& assertion : _assertions)
    {
      encode(assertion);
      d_assertion_lits.insert(std::abs(lit(assertion)));
      d_assertions.push_back(assertion);
    }
  }

  Result res;
  {
    util::Timer timer(d_stats.time_sat);
    res = d_sat_solver->solve();
  }
  if (res == Result::SAT)
  {
    NodeManager& nm = NodeManager::get();
    util::Timer timer(d_stats.time_fixed);
    for (const auto& [node, _] : d_encode_cache)
    {
      auto l = std::abs(lit(node));
      if (d_assertion_lits.find(l) == d_assertion_lits.end())
      {
        l        = lit(node);
        auto val = d_sat_solver->fixed(l);
        Node null;
        if (val < 0)
        {
          ++d_stats.num_new_assertions;
          assertions.push_back(nm.mk_node(Kind::NOT, {node}), null);
          d_assertion_lits.insert(l);
        }
        else if (val > 0)
        {
          ++d_stats.num_new_assertions;
          assertions.push_back(node, null);
          d_assertion_lits.insert(l);
        }
      }
    }
  }
}

/* --- PassSkeletonPreproc private ------------------------------------------ */

int64_t
PassSkeletonPreproc::lit(const Node& term)
{
  assert(term.type().is_bool());
  return (term.kind() == Kind::NOT) ? -term[0].id() : term.id();
}

void
PassSkeletonPreproc::encode(const Node& assertion)
{
  if (d_encode_cache.find(assertion) != d_encode_cache.end())
  {
    // Already encoded
    return;
  }

  node_ref_vector visit{assertion};
  do
  {
    const Node& cur = visit.back();

    if (!cur.type().is_bool())
    {
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = d_encode_cache.emplace(cur, false);
    if (inserted)
    {
      Kind k = cur.kind();
      if (k == Kind::NOT || k == Kind::AND || k == Kind::ITE
          || k == Kind::EQUAL)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (!it->second)
    {
      it->second = true;
      switch (cur.kind())
      {
        case Kind::AND: {
          // n <=> a /\ b
          auto n = lit(cur);
          auto a = lit(cur[0]);
          auto b = lit(cur[1]);

          d_sat_solver->add(-n);
          d_sat_solver->add(a);
          d_sat_solver->add(0);

          d_sat_solver->add(-n);
          d_sat_solver->add(b);
          d_sat_solver->add(0);

          d_sat_solver->add(n);
          d_sat_solver->add(-a);
          d_sat_solver->add(-b);
          d_sat_solver->add(0);

          d_stats.num_cnf_lits += 7;
          d_stats.num_cnf_clauses += 3;
        }
        break;

        case Kind::EQUAL:
          if (cur[0].type().is_bool())
          {
            // n <=> a = b
            auto n = lit(cur);
            auto a = lit(cur[0]);
            auto b = lit(cur[1]);

            d_sat_solver->add(-n);
            d_sat_solver->add(-a);
            d_sat_solver->add(b);
            d_sat_solver->add(0);

            d_sat_solver->add(-n);
            d_sat_solver->add(a);
            d_sat_solver->add(-b);
            d_sat_solver->add(0);

            d_sat_solver->add(n);
            d_sat_solver->add(a);
            d_sat_solver->add(b);
            d_sat_solver->add(0);

            d_sat_solver->add(n);
            d_sat_solver->add(-a);
            d_sat_solver->add(-b);
            d_sat_solver->add(0);

            d_stats.num_cnf_lits += 12;
            d_stats.num_cnf_clauses += 4;
          }
          break;

        case Kind::ITE: {
          // n <=> c ? a : b
          auto n = lit(cur);
          auto c = lit(cur[0]);
          auto a = lit(cur[1]);
          auto b = lit(cur[2]);

          d_sat_solver->add(-n);
          d_sat_solver->add(-c);
          d_sat_solver->add(-a);
          d_sat_solver->add(0);

          d_sat_solver->add(-n);
          d_sat_solver->add(c);
          d_sat_solver->add(b);
          d_sat_solver->add(0);

          d_sat_solver->add(n);
          d_sat_solver->add(-c);
          d_sat_solver->add(-a);
          d_sat_solver->add(0);

          d_sat_solver->add(n);
          d_sat_solver->add(c);
          d_sat_solver->add(-b);
          d_sat_solver->add(0);

          d_stats.num_cnf_lits += 12;
          d_stats.num_cnf_clauses += 4;
        }
        break;

        default: break;
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  d_sat_solver->add(lit(assertion));
  d_sat_solver->add(0);
  d_stats.num_cnf_lits += 1;
  d_stats.num_cnf_clauses += 1;
}

PassSkeletonPreproc::Statistics::Statistics(util::Statistics& stats,
                                            const std::string& prefix)
    : time_apply(stats.new_stat<util::TimerStatistic>(prefix + "time_apply")),
      time_sat(stats.new_stat<util::TimerStatistic>(prefix + "time_sat")),
      time_fixed(stats.new_stat<util::TimerStatistic>(prefix + "time_fixed")),
      time_encode(stats.new_stat<util::TimerStatistic>(prefix + "time_encode")),
      num_new_assertions(stats.new_stat<uint64_t>(prefix + "new_assertions")),
      num_resets(stats.new_stat<uint64_t>(prefix + "resets")),
      num_cnf_lits(stats.new_stat<uint64_t>(prefix + "cnf::lits")),
      num_cnf_clauses(stats.new_stat<uint64_t>(prefix + "cnf::clauses"))
{
}

}  // namespace bzla::preprocess::pass
