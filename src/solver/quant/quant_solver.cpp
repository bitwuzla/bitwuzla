/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/quant/quant_solver.h"

#include "node/node.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "solving_context.h"
#include "util/logger.h"

namespace bzla::quant {

std::ostream&
operator<<(std::ostream& os, QuantSolver::LemmaKind kind)
{
  switch (kind)
  {
    case QuantSolver::LemmaKind::MBQI_INST: os << "MBQI_INST"; break;
    case QuantSolver::LemmaKind::SKOLEMIZATION: os << "SKOLEMIZATION"; break;
  }
  return os;
}

using namespace node;

/* --- QuantSolver public --------------------------------------------------- */

bool
QuantSolver::is_theory_leaf(const Node& term)
{
  return term.kind() == Kind::FORALL;
}

QuantSolver::QuantSolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_quantifiers(state.backtrack_mgr()),
      d_assertions(state.backtrack_mgr()),
      d_process_cache(state.backtrack_mgr()),
      d_consts(state.backtrack_mgr()),
      d_ground_terms(state.backtrack_mgr()),
      d_skolemization_lemmas(state.backtrack_mgr()),
      d_lemma_cache(state.backtrack_mgr()),
      d_stats(env.statistics(), "solver::quant::")
{
}

QuantSolver::~QuantSolver() {}

bool
QuantSolver::check()
{
  Log(1);
  Log(1) << "*** check quantifiers";

  if (d_quantifiers.empty())
  {
    return true;
  }

  util::Timer timer(d_stats.time_check);
  std::vector<Node> to_check;

  d_added_lemma = false;
  for (const Node& q : d_quantifiers)
  {
    Node value = d_solver_state.value(q);
    if (value.value<bool>())
    {
      Log(2) << "Active forall: " << q;
      to_check.push_back(q);
    }
    else
    {
      Log(2) << "Active exists: " << q;
      if (d_skolemization_lemmas.find(q) == d_skolemization_lemmas.end())
      {
        lemma(skolemization_lemma(q), LemmaKind::SKOLEMIZATION);
      }
    }
  }

  for (const Node& assertion : d_assertions)
  {
    process(assertion);
  }
  bool done = mbqi_check(to_check);
  return done;
}

Node
QuantSolver::value(const Node& term)
{
  (void) term;
  assert(false);
  return Node();
}

void
QuantSolver::register_term(const Node& term)
{
  assert(term.kind() == Kind::FORALL);
  d_quantifiers.push_back(term);
  Log(2) << "Register quantifier: " << term;
}

void
QuantSolver::register_assertion(const Node& assertion)
{
  d_assertions.push_back(assertion);
}

/* --- QuantSolver private -------------------------------------------------- */

void
QuantSolver::lemma(const Node& lemma, LemmaKind kind)
{
  const Node& rewritten = d_env.rewriter().rewrite(lemma);
  auto [it, inserted]   = d_lemma_cache.insert(rewritten);
  if (inserted)
  {
    if (!rewritten.is_value() || !rewritten.value<bool>())
    {
      d_stats.lemmas << kind;
      ++d_stats.num_lemmas;
      d_solver_state.lemma(rewritten);
      d_added_lemma = true;
    }
  }
  else
  {
    Log(2) << "Duplicate lemma: " << rewritten;
  }
}

Node
QuantSolver::instantiate(const Node& q,
                         const std::unordered_map<Node, Node>& substs)
{
  assert(q.kind() == Kind::FORALL);

  Node body = q[1];
  while (body.kind() == Kind::FORALL)
  {
    body = body[1];
  }

  Node result = substitute(body, substs);

  // TODO: instance tracking?

  return result;
}

Node
QuantSolver::substitute(const Node& n,
                        const std::unordered_map<Node, Node>& substs)
{
  node::unordered_node_ref_map<Node> cache;
  node::node_ref_vector visit{n};
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
      auto iit = substs.find(cur);
      if (iit != substs.end())
      {
        assert(cur.kind() == Kind::VARIABLE);
        it->second = iit->second;
      }
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto iit = cache.find(child);
          assert(iit != cache.end());
          children.push_back(iit->second);
        }
        if (cur.kind() == Kind::FORALL && children[0].kind() != Kind::VARIABLE)
        {
          it->second = children[1];
        }
        else
        {
          it->second = utils::rebuild_node(cur, children);
        }
      }
    }

    visit.pop_back();
  } while (!visit.empty());

  return cache.at(n);
}

const Node&
QuantSolver::inst_const(const Node& q)
{
  auto it = d_instantiation_consts.find(q);
  if (it != d_instantiation_consts.end())
  {
    return it->second;
  }

  std::stringstream ss;
  ss << "ic(" << q.id() << ")";

  Node ic              = NodeManager::get().mk_const(q[0].type(), ss.str());
  auto [iit, inserted] = d_instantiation_consts.emplace(q, ic);
  Log(2) << "Inst constant " << ic << " for " << q;
  return iit->second;
}

const Node&
QuantSolver::skolem_const(const Node& q)
{
  auto it = d_skolem_consts.find(q);
  if (it != d_skolem_consts.end())
  {
    return it->second;
  }

  NodeManager& nm = NodeManager::get();
  std::stringstream ss;
  ss << "sk(" << q.id() << ")";

  Node sk              = nm.mk_const(q[0].type(), ss.str());
  auto [iit, inserted] = d_skolem_consts.emplace(q, sk);
  Log(2) << "New skolem " << sk << " for " << q;
  return iit->second;
}

const Node&
QuantSolver::ce_const(const Node& q)
{
  auto it = d_ce_consts.find(q);
  if (it != d_ce_consts.end())
  {
    return it->second;
  }

  NodeManager& nm = NodeManager::get();
  std::stringstream ss;
  ss << "ce(" << q.id() << ")";

  Node ce              = nm.mk_const(q.type(), ss.str());
  auto [iit, inserted] = d_ce_consts.emplace(q, ce);
  Log(2) << "Counterexample literal " << ce << " for " << q;
  return iit->second;
}

Node
QuantSolver::skolemize(const Node& q)
{
  assert(q.kind() == Kind::FORALL);
  Log(2) << "Skolemize " << q;

  std::unordered_map<Node, Node> map;
  Node cur = q;
  while (cur.kind() == Kind::FORALL)
  {
    const Node& sk = skolem_const(cur);
    map.emplace(cur[0], sk);
    Log(2) << "  " << cur[0] << " -> " << sk;
    cur = cur[1];
  }

  Node inst = instantiate(q, map);
  return inst;
}

const Node&
QuantSolver::skolemization_lemma(const Node& q)
{
  assert(q.kind() == Kind::FORALL);

  auto it = d_skolemization_lemmas.find(q);
  if (it != d_skolemization_lemmas.end())
  {
    return it->second;
  }
  Log(2) << "Skolemization lemma: " << q;

  NodeManager& nm = NodeManager::get();
  Rewriter& rw    = d_env.rewriter();
  Node inst       = skolemize(q);
  Node lemma      = rw.rewrite(
      nm.mk_node(Kind::IMPLIES,
                      {nm.mk_node(Kind::NOT, {q}), nm.mk_node(Kind::NOT, {inst})}));
  auto [iit, inserted] = d_skolemization_lemmas.emplace(q, lemma);
  // std::cout << "sk lem: " << lemma << std::endl;
  return iit->second;
}

void
QuantSolver::process(const Node& q)
{
  util::Timer timer(d_stats.time_process);
  node::node_ref_vector visit{q};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_process_cache.insert(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::CONSTANT)
      {
        d_consts.push_back(cur);
      }
      if (cur.kind() != Kind::FORALL)
      {
        d_ground_terms.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

bool
QuantSolver::mbqi_check(const std::vector<Node>& to_check)
{
  util::Timer timer(d_stats.time_mbqi);
  NodeManager& nm = NodeManager::get();

  // Initialize MBQI solver
  option::Options options;
  d_mbqi_solver.reset(new SolvingContext(options, "mbqi"));

  // Assert formula
  for (const Node& c : d_consts)
  {
    Node value = d_solver_state.value(c);
    d_mbqi_solver->assert_formula(nm.mk_node(Kind::EQUAL, {c, value}));
    // std::cout << c << ": " << value << std::endl;
  }

  size_t num_inactive = 0;
  for (const Node& q : to_check)
  {
    ++d_stats.mbqi_checks;
    d_mbqi_solver->push();
    d_mbqi_solver->assert_formula(mbqi_inst(q));
    Log(2) << "mbqi check: " << mbqi_inst(q);
    auto res = d_mbqi_solver->solve();
    // Counterexample
    if (res == Result::SAT)
    {
      Log(2) << "counterexample";
      lemma(mbqi_lemma(q), LemmaKind::MBQI_INST);
    }
    else if (res == Result::UNSAT)
    {
      Log(2) << "unsat";
      ++num_inactive;
    }
    d_mbqi_solver->pop();
  }
  bool done = num_inactive == to_check.size();
  if (done)
  {
    Log(2) << "mbqi: all inactive";
  }
  return done;
}

const Node&
QuantSolver::mbqi_inst(const Node& q)
{
  assert(q.kind() == Kind::FORALL);

  auto it = d_mbqi_inst.find(q);
  if (it != d_mbqi_inst.end())
  {
    return it->second;
  }

  std::unordered_map<Node, Node> map;
  Node cur = q;
  while (cur.kind() == Kind::FORALL)
  {
    const Node& ic = inst_const(cur);
    map.emplace(cur[0], ic);
    assert(!ic.is_null());
    cur = cur[1];
  }

  Node inst = substitute(cur, map);
  auto [iit, inserted] =
      d_mbqi_inst.emplace(q, NodeManager::get().mk_node(Kind::NOT, {inst}));
  return iit->second;
}

Node
QuantSolver::mbqi_lemma(const Node& q)
{
  assert(q.kind() == Kind::FORALL);

  std::unordered_map<Node, Node> map;
  Node cur = q;
  while (cur.kind() == Kind::FORALL)
  {
    const Node& ic = inst_const(cur);
    Node value     = d_mbqi_solver->get_value(ic);
    assert(!value.is_null());
    for (const Node& t : d_ground_terms)
    {
      if (t.type() == ic.type())
      {
        Node tv = d_solver_state.value(t);
        if (tv == value)
        {
          // std::cout << "use t: " << t << std::endl;
          value = t;
          break;
        }
      }
    }
    map.emplace(cur[0], value);
    assert(!ic.is_null());
    cur = cur[1];
  }

  NodeManager& nm = NodeManager::get();
  Node inst       = substitute(cur, map);
  return nm.mk_node(Kind::IMPLIES, {q, inst});
}

QuantSolver::Statistics::Statistics(util::Statistics& stats,
                                    const std::string& prefix)
    : mbqi_checks(stats.new_stat<uint64_t>(prefix + "mbqi_checks")),
      num_lemmas(stats.new_stat<uint64_t>(prefix + "num_lemmas")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check")),
      time_process(
          stats.new_stat<util::TimerStatistic>(prefix + "time_process")),
      time_mbqi(stats.new_stat<util::TimerStatistic>(prefix + "time_mbqi"))

{
}

}  // namespace bzla::quant
