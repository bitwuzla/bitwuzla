/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "check/check_interpolant.h"

#include <unordered_set>

#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_map.h"
#include "sat/interpolants/tracer_kinds.h"

using namespace bzla::node;
using namespace bzla::sat::interpolants;

namespace bzla::check {

CheckInterpolant::CheckInterpolant(SolvingContext& ctx)
    : d_ctx(ctx), d_logger(ctx.env().logger())
{
}

bool
CheckInterpolant::check(const std::unordered_set<Node>& A,
                        const Node& interpolant)
{
  if (!d_ctx.options().dbg_check_interpolant())
  {
    return true;
  }

  Log(1);
  Log(1) << "*** check interpolant";
  Log(1);

  NodeManager& nm = d_ctx.env().nm();
  const auto& assertions = d_ctx.original_assertions();
  std::vector<Node> B;

  // First, check if A implies interpolant.
  {
    option::Options opts;
    opts.dbg_check_interpolant.set(false);
    SolvingContext check_ctx(
        nm, opts, d_ctx.env().sat_factory(), "chkinterpol");
    check_ctx.env().configure_terminator(d_ctx.env().terminator());
    for (size_t i = 0, n = assertions.size(); i < n; ++i)
    {
      if (A.find(assertions[i]) == A.end())
      {
        B.push_back(assertions[i]);
      }
      else
      {
        check_ctx.assert_formula(assertions[i]);
      }
    }
    if (d_logger.is_log_enabled(1))
    {
      size_t i = 0;
      for (const auto& a : A)
      {
        Log(1) << "A[" << i++ << "]: " << a;
      }
      i = 0;
      for (const auto& a : B)
      {
        Log(1) << "B[" << i++ << "]: " << a;
      }
    }
    Log(1) << "I: " << interpolant;
    Log(1);
    check_ctx.assert_formula(nm.mk_node(node::Kind::NOT, {interpolant}));
    Log(1) << "check: (and A (not I))";
    Result res = check_ctx.solve();
    Log(1) << "(and A (not I)): " << res;
    if (res != Result::UNSAT)
    {
      return false;
    }
  }
  Log(1);

  // Then, check if interpolant implies (not B)
  option::Options opts;
  opts.dbg_check_interpolant.set(false);
  SolvingContext check_ctx(nm, opts, d_ctx.env().sat_factory(), "chkinterpol");
  check_ctx.env().configure_terminator(d_ctx.env().terminator());
  check_ctx.assert_formula(interpolant);
  for (const auto& a : B)
  {
    check_ctx.assert_formula(a);
  }
  Log(1) << "check: (and I B)";
  Result res = check_ctx.solve();
  Log(1) << "(and I B): " << res;
  if (res != Result::UNSAT)
  {
    return false;
  }
  Log(1);

  // Finally, check if uninterpreted symbols occurring in I are shared, i.e.,
  // that it contains no symbols that are local to A or C.
  Log(1) << "check: symbols in I";
  std::unordered_map<Node, VariableKind> consts;
  node_ref_vector visit{assertions.begin(), assertions.end()};
  unordered_node_ref_map<bool> cache;
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      if (cur.is_const())
      {
        consts.emplace(cur, VariableKind::A);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  cache.clear();
  for (const auto& a : B)
  {
    visit.push_back(a);
  }
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      if (cur.is_const())
      {
        auto [cit, cinserted] = consts.emplace(cur, VariableKind::B);
        if (!inserted && cit->second == VariableKind::A)
        {
          cit->second = VariableKind::GLOBAL;
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  cache.clear();
  visit.push_back(interpolant);
  for (const auto& a : B)
  {
    visit.push_back(a);
  }
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      if (cur.is_const())
      {
        auto cit = consts.find(cur);
        if (cit == consts.end())
        {
          Log(1) << "check: '" << cur << "': " << std::setw(6) << "(new)"
                 << " : \u2716";
          return false;
        }
        if (cit->second != VariableKind::GLOBAL)
        {
          Log(1) << "check: '" << cur << "': " << std::setw(6) << cit->second
                 << ": \u2716";
          return false;
        }
        Log(1) << "check: '" << cur << "': " << std::setw(6) << cit->second
               << ": \u2713";
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return true;
}
}  // namespace bzla::check
