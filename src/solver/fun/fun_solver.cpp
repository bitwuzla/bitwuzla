/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fun/fun_solver.h"

#include "env.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "util/logger.h"

namespace bzla::fun {

using namespace node;

/* --- FunSolver public ----------------------------------------------------- */

bool
FunSolver::is_theory_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::APPLY
         || (k == Kind::EQUAL
             && (term[0].type().is_fun() || term[0].type().is_uninterpreted()));
}

FunSolver::FunSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_applies(state.backtrack_mgr()),
      d_fun_equalities(state.backtrack_mgr()),
      d_equalities(state.backtrack_mgr()),
      d_stats(env.statistics(), "solver::fun::")
{
}

FunSolver::~FunSolver() {}

bool
FunSolver::check()
{
  Log(1);
  Log(1) << "*** check functions";

  d_fun_models.clear();

  util::Timer timer(d_stats.time_check);
  ++d_stats.num_checks;

  // Do not cache size here since d_applies may grow while iterating.
  for (size_t i = 0; i < d_applies.size(); ++i)
  {
    const Node& apply = d_applies[i];
    const Node& fun = apply[0];
    auto& fun_model = d_fun_models[fun];

    Log(1) << "check: " << apply;
    Apply app(apply, d_solver_state);
    auto [it, inserted] = fun_model.insert(app);
    if (!inserted)
    {
      // Function congruence conflict
      if (it->value() != app.value())
      {
        add_function_congruence_lemma(apply, it->get());
      }
    }
  }
  return true;
}

Node
FunSolver::value(const Node& term)
{
  assert(term.type().is_fun() || term.type().is_uninterpreted()
         || term.kind() == Kind::APPLY);

  NodeManager& nm = d_env.nm();
  if (term.kind() == Kind::LAMBDA)
  {
    return term;
  }
  else if (term.kind() == Kind::CONSTANT && term.type().is_uninterpreted())
  {
    std::stringstream ss;
    ss << "@const_" << term.id();
    return nm.mk_value(term.type(), ss.str());
  }
  else if (term.kind() == Kind::APPLY)
  {
    auto it = d_fun_models.find(term[0]);
    if (it != d_fun_models.end())
    {
      const auto& fun_model = it->second;
      Apply app(term, d_solver_state, false);
      auto itv = fun_model.find(app);
      if (itv != fun_model.end())
      {
        return itv->value();
      }
    }
    if (term[0].kind() == Kind::LAMBDA)
    {
      // This is currently only called when lambda nodes are constructed
      // internally during model construction. The beta reduction step here
      // should be relatively cheap since all the non-function and non-array
      // nodes are values.
      return d_env.rewriter().rewrite(beta_reduce(term));
    }
    if (term.type().is_uninterpreted())
    {
      std::stringstream ss;
      ss << "@const_" << term.id();
      return nm.mk_value(term.type(), ss.str());
    }
    return node::utils::mk_default_value(nm, term.type());
  }

  auto it = d_fun_models.find(term);
  if (it != d_fun_models.end())
  {
    const std::vector<Type>& types = term.type().fun_types();
    std::vector<Node> vars;
    for (size_t i = 0, size = types.size() - 1; i < size; ++i)
    {
      vars.push_back(nm.mk_var(types[i]));
    }

    Node res              = utils::mk_default_value(nm, types.back());
    const auto& fun_model = it->second;

    // Construct nested ITEs for function model
    for (const auto& apply : fun_model)
    {
      const std::vector<Node>& values = apply.values();
      assert(vars.size() == values.size());
      const Node& value = apply.value();

      if (value == res)
      {
        continue;
      }

      std::vector<Node> eqs;
      for (size_t i = 0, size = vars.size(); i < size; ++i)
      {
        eqs.push_back(nm.mk_node(Kind::EQUAL, {vars[i], values[i]}));
      }
      Node cond = utils::mk_nary(nm, Kind::AND, eqs);
      res       = nm.mk_node(Kind::ITE, {cond, value, res});
    }
    vars.push_back(res);
    return utils::mk_binder(nm, Kind::LAMBDA, vars);
  }
  return utils::mk_default_value(nm, term.type());
}

void
FunSolver::register_term(const Node& term)
{
  if (term.kind() == Kind::APPLY)
  {
    assert(term[0].kind() != Kind::LAMBDA);
    d_applies.push_back(term);
  }
  else
  {
    assert(term.kind() == Kind::EQUAL);
    if (term[0].type().is_fun())
    {
      d_solver_state.unsupported(
          "Equalities over functions not yet supported.");
      d_fun_equalities.push_back(term);
    }
    else
    {
      d_solver_state.unsupported(
          "Equalities over uninterpreted sorts not yet supported.");
      d_equalities.push_back(term);
    }
  }
}

/* --- FunSolver private ---------------------------------------------------- */

void
FunSolver::add_function_congruence_lemma(const Node& a, const Node& b)
{
  assert(a.num_children() == b.num_children());
  assert(a.kind() == Kind::APPLY);
  assert(b.kind() == Kind::APPLY);
  assert(a != b);

  NodeManager& nm = d_env.nm();
  std::vector<Node> premise;
  for (size_t i = 1, size = a.num_children(); i < size; ++i)
  {
    premise.emplace_back(nm.mk_node(Kind::EQUAL, {a[i], b[i]}));
  }
  Node conclusion = nm.mk_node(Kind::EQUAL, {a, b});
  Node lemma      = nm.mk_node(Kind::IMPLIES,
                               {utils::mk_nary(nm, Kind::AND, premise), conclusion});
  d_solver_state.lemma(lemma);
}

Node
FunSolver::beta_reduce(const Node& apply)
{
  assert(apply.kind() == Kind::APPLY);
  assert(apply[0].kind() == Kind::LAMBDA);

  std::unordered_map<Node, Node> cache;

  size_t i  = 1;
  Node body = apply[0];
  while (body.kind() == Kind::LAMBDA)
  {
    cache.emplace(body[0], apply[i++]);
    body = body[1];
  }

  node::node_ref_vector visit{body};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());

    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      it->second = utils::rebuild_node(d_env.nm(), cur, cache);
    }

    visit.pop_back();
  } while (!visit.empty());

  return cache.at(body);
}

FunSolver::Statistics::Statistics(util::Statistics& stats,
                                  const std::string& prefix)
    : num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}

/* --- Apply public --------------------------------------------------------- */

FunSolver::Apply::Apply(const Node& apply,
                        SolverState& state,
                        bool cache_apply_value)
    : d_apply(apply), d_hash(0)
{
  // Compute hash value of function applications based on the current function
  // argument model values.
  for (size_t i = 1, size = apply.num_children(); i < size; ++i)
  {
    d_values.emplace_back(state.value(apply[i]));
    d_hash += std::hash<Node>{}(d_values.back());
  }
  if (cache_apply_value)
  {
    // Cache value of function application
    d_value = state.value(apply);
  }
}

const Node&
FunSolver::Apply::get() const
{
  return d_apply;
}

const Node&
FunSolver::Apply::value() const
{
  return d_value;
}

const std::vector<Node>&
FunSolver::Apply::values() const
{
  return d_values;
}

bool
FunSolver::Apply::operator==(const Apply& other) const
{
  assert(d_values.size() == other.d_values.size());
  for (size_t i = 0, size = d_values.size(); i < size; ++i)
  {
    if (d_values[i] != other.d_values[i])
    {
      return false;
    }
  }
  return true;
}

size_t
FunSolver::Apply::hash() const
{
  return d_hash;
}

}  // namespace bzla::fun
