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
      d_assertions(backtrack_mgr),
      d_stats(env.statistics())
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

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value())
    {
      continue;
    }
    d_assertions.push_back(assertion);
  }

  if (d_assertions.empty())
  {
    return;
  }

  d_sat_solver.reset(new sat::Cadical());
  d_encode_cache.clear();

  std::unordered_set<int64_t> assertion_lits;
  for (const Node& assertion : d_assertions)
  {
    encode(assertion);
    assertion_lits.insert(lit(assertion));
  }

  NodeManager& nm = NodeManager::get();
  auto res        = d_sat_solver->solve();
  if (res == Result::SAT)
  {
    for (const auto& [node, _] : d_encode_cache)
    {
      auto l = lit(node);
      if (assertion_lits.find(l) == assertion_lits.end())
      {
        auto val = d_sat_solver->fixed(lit(node));
        Node null;
        if (val < 0)
        {
          ++d_stats.num_new_assertions;
          assertions.push_back(nm.mk_node(Kind::NOT, {node}), null);
        }
        else if (val > 0)
        {
          ++d_stats.num_new_assertions;
          assertions.push_back(node, null);
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
  return (term.kind() == Kind::NOT) ? -term.id() : term.id();
}

void
PassSkeletonPreproc::encode(const Node& assertion)
{
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
      if (k == Kind::AND || k == Kind::ITE || k == Kind::EQUAL)
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
        }
        break;

        default: break;
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  d_sat_solver->add(lit(assertion));
  d_sat_solver->add(0);
}

PassSkeletonPreproc::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::skeleton::time_apply")),
      num_new_assertions(
          stats.new_stat<uint64_t>("preprocess::skeleton::new_assertions"))
{
}

}  // namespace bzla::preprocess::pass
