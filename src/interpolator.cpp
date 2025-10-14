/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "interpolator.h"

#include "node/node_utils.h"
#include "preprocess/pass/variable_substitution.h"

namespace bzla {

using namespace node;

Interpolator::Interpolator(SolvingContext& ctx)
    : d_ctx(ctx),
      d_env(ctx.env()),
      d_logger(d_env.logger()),
      d_original_assertions(ctx.original_assertions()),
      d_pp_assertions(ctx.assertions()),
      d_stats(d_env.statistics())
{
}

Node
Interpolator::get_interpolant(const std::unordered_set<Node>& A)
{
  util::Timer timer(d_stats.time_get_interpolant);

  Log(1);
  Log(1) << "*** interpolant";
  Log(1);
  Log(1) << "expected assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (size_t i = 0, ia = 0, ib = 0, n = d_original_assertions.size(); i < n;
         ++i)
    {
      if (A.find(d_original_assertions[i]) != A.end())
      {
        Log(1) << "A[" << ia++ << "]: " << d_original_assertions[i];
      }
      else
      {
        Log(1) << "B[" << ib++ << "]: " << d_original_assertions[i];
      }
    }
  }
  Log(1);

  Node ipol;
  NodeManager& nm = d_env.nm();

  // Partition preprocessed assertions into A and B
  std::unordered_set<Node> B;
  std::vector<Node> ppA, ppB;
  std::unordered_set<Node> orig_ass{d_original_assertions.begin(),
                                    d_original_assertions.end()};
  for (size_t i = 0, size = d_pp_assertions.size(); i < size; ++i)
  {
    // trace assertion back to original assertion
    Node orig =
        d_ctx.preprocessor().original_assertion(d_pp_assertions[i], orig_ass);
    auto it = A.find(orig);
    if (it != A.end())
    {
      ppA.push_back(d_pp_assertions[i]);
    }
    else
    {
      B.insert(orig);
      ppB.push_back(d_pp_assertions[i]);
    }
  }

  Log(1) << "actual assertion partitioning:";
  if (d_logger.is_log_enabled(1))
  {
    for (const auto& a : A)
    {
      Log(1) << "A: " << a;
    }
    for (const auto& a : B)
    {
      Log(1) << "B: " << a;
    }
    for (size_t i = 0, size = ppA.size(); i < size; ++i)
    {
      Log(1) << "ppA[" << i << "]: " << ppA[i];
    }
    for (size_t i = 0, size = ppB.size(); i < size; ++i)
    {
      Log(1) << "ppB[" << i << "]: " << ppB[i];
    }
  }

  // Preprocessor determined unsat, so we can make a shortcut.
  if (d_ctx.sat_state_pp() == Result::UNSAT)
  {
    for (const auto& a : ppA)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(false);
        break;
      }
    }
    for (const auto& a : ppB)
    {
      if (a.is_value() && !a.value<bool>())
      {
        ipol = nm.mk_value(true);
        break;
      }
    }
  }

  if (ipol.is_null())
  {
    if (d_env.options().interpolants_subst())
    {
      ipol = interpolant_by_substitution(A, B, ppA, ppB);
    }

    // Generate interpolant from bit-level proof.
    if (ipol.is_null())
    {
      ipol = d_ctx.solver_engine().interpolant(ppA, ppB);
      ++d_stats.interpolant_bitlevel;
    }
  }

  return ipol;
}

std::vector<Node>
Interpolator::get_interpolants(
    const std::vector<std::unordered_set<Node>>& partitions)
{
  std::vector<Node> res;
  std::unordered_set<Node> A;

  for (const auto& p : partitions)
  {
    A.insert(p.begin(), p.end());
    res.push_back(get_interpolant(A));
  }
  return res;
}

Node
Interpolator::interpolant_by_substitution(const std::unordered_set<Node>& A,
                                          const std::unordered_set<Node>& B,
                                          const std::vector<Node>& ppA,
                                          const std::vector<Node>& ppB)
{
  std::unordered_set<Node> shared = shared_consts(A, B);

  // Check if all A-local symbols were eliminated and return A as
  // interpolant.
  Node ipol = apply_substs(d_env, ppA, shared);
  if (!ipol.is_null())
  {
    ++d_stats.interpolant_substA;
    return d_env.rewriter().rewrite(ipol);
  }

  // Check if all B-local symbols were eliminated and return ~B as
  // interpolant.
  ipol = apply_substs(d_env, ppB, shared);
  if (!ipol.is_null())
  {
    ++d_stats.interpolant_substB;
    return d_env.rewriter().rewrite(d_env.nm().mk_node(Kind::NOT, {ipol}));
  }

  return Node();
}

std::unordered_set<Node>
Interpolator::get_consts(const std::unordered_set<Node>& nodes)
{
  std::vector<Node> visit;
  std::unordered_set<Node> cache, consts;

  visit.insert(visit.end(), nodes.begin(), nodes.end());
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    if (cache.insert(cur).second)
    {
      if (cur.is_const())
      {
        consts.insert(cur);
      }

      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  }

  return consts;
}

std::unordered_set<Node>
Interpolator::shared_consts(const std::unordered_set<Node>& A,
                            const std::unordered_set<Node>& B)
{
  std::unordered_set<Node> shared;

  auto constsA = get_consts(A);
  auto constsB = get_consts(B);

  for (const auto& c : constsA)
  {
    if (constsB.find(c) != constsB.end())
    {
      shared.insert(c);
    }
  }
  return shared;
}

Node
Interpolator::apply_substs(Env& env,
                           const std::vector<Node>& assertions,
                           const std::unordered_set<Node>& shared)
{
  option::Options opts;
  Env vs_env(env.nm(), env.sat_factory(), opts);
  backtrack::BacktrackManager mgr;
  preprocess::pass::PassVariableSubstitution vs(vs_env, &mgr, shared);
  backtrack::AssertionStack as;
  for (const auto& a : assertions)
  {
    as.push_back(a);
  }

  if (as.size() == 0)
  {
    return Node();
  }

  preprocess::AssertionVector av(as.view());
  vs.apply(av);

  std::unordered_set<Node> subst;
  for (size_t i = 0; i < av.size(); ++i)
  {
    subst.insert(av[i]);
  }

  bool is_itp  = true;
  auto constsA = get_consts(subst);
  for (const auto& c : constsA)
  {
    if (shared.find(c) == shared.end())
    {
      is_itp = false;
      break;
    }
  }
  if (is_itp)
  {
    std::vector<Node> nodes;
    for (size_t i = 0; i < av.size(); ++i)
    {
      nodes.push_back(av[i]);
    }
    return utils::mk_nary(env.nm(), Kind::AND, nodes);
  }
  return Node();
}

Interpolator::Statistics::Statistics(util::Statistics& stats)
    : time_get_interpolant(stats.new_stat<util::TimerStatistic>(
          "interpolator::time_get_interpolant")),
      interpolant_substA(
          stats.new_stat<uint64_t>("interpolator::interpolant_substA")),
      interpolant_substB(
          stats.new_stat<uint64_t>("interpolator::interpolant_substB")),
      interpolant_bitlevel(
          stats.new_stat<uint64_t>("interpolator::interpolant_bitlevel"))
{
}
}  // namespace bzla
