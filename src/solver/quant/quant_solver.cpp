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
    case QuantSolver::LemmaKind::MBQI_INST_INV: os << "MBQI_INST_INV"; break;
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
      d_bv_inverter(env, d_env.options().quant_ic_underdet()),
      d_quantifiers(state.backtrack_mgr()),
      d_assertions(state.backtrack_mgr()),
      d_process_cache(state.backtrack_mgr()),
      d_consts(state.backtrack_mgr()),
      d_ground_terms(state.backtrack_mgr()),
      d_skolemization_lemmas(state.backtrack_mgr()),
      d_lemma_cache(state.backtrack_mgr()),
      d_inv_cache(state.backtrack_mgr()),
      d_opt_quant_ic(env.options().quant_ic()),
      d_opt_quant_ic_bounds(env.options().quant_ic_bounds()),
      d_opt_quant_ic_filter(env.options().quant_ic_filter()),
      d_opt_quant_ic_value_limit(env.options().quant_ic_value_limit()),
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
      // A quantifier that rebinds a substituted variable shadows it. Avoid
      // capturing shadowed variables by recursing with a new scope excluding
      // the shadowed variable.
      if (cur.kind() == Kind::FORALL && substs.find(cur[0]) != substs.end())
      {
        // We need more than one substitution to change the body of cur.
        if (substs.size() > 1)
        {
          std::unordered_map<Node, Node> reduced(substs);
          reduced.erase(cur[0]);
          std::vector<Node> children{cur[0], substitute(cur[1], reduced)};
          it->second = utils::rebuild_node(d_env.nm(), cur, children);
        }
        else
        {
          it->second = cur;
        }
        visit.pop_back();
        continue;
      }
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
        // Quantifiers binding a substituted variable are handled above, the
        // prefix of the instantiated quantifier is stripped by the callers.
        assert(cur.kind() != Kind::FORALL
               || children[0].kind() == Kind::VARIABLE);
        it->second = utils::rebuild_node(d_env.nm(), cur, children);
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

  Node ic              = d_env.nm().mk_const(q[0].type(), ss.str());
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

  NodeManager& nm = d_env.nm();
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

  NodeManager& nm = d_env.nm();
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

  NodeManager& nm = d_env.nm();
  Rewriter& rw    = d_env.rewriter();
  Node inst       = skolemize(q);
  Node lemma      = rw.rewrite(
      nm.mk_node(Kind::IMPLIES,
                      {nm.mk_node(Kind::NOT, {q}), nm.mk_node(Kind::NOT, {inst})}));
  auto [iit, inserted] = d_skolemization_lemmas.emplace(q, lemma);
  return iit->second;
}

void
QuantSolver::process(const Node& q)
{
  util::Timer timer(d_stats.time_process);

  if (d_process_cache.find(q) != d_process_cache.end())
  {
    return;
  }

  node::node_ref_vector visit{q};
  std::unordered_map<Node, bool> cache;
  std::unordered_map<Node, std::unordered_set<Node>> vars_map;
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      if (cur.kind() == Kind::CONSTANT)
      {
        if (d_process_cache.insert(cur).second)
        {
          d_consts.push_back(cur);
          d_ground_terms.push_back(cur);
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (!it->second)
    {
      it->second = true;
      if (cur.is_variable())
      {
        vars_map[cur].insert(cur);
      }
      else
      {
        auto& vars = vars_map[cur];
        for (const auto& c : cur)
        {
          const auto& v = vars_map.at(c);
          vars.insert(v.begin(), v.end());
        }

        if (cur.kind() == Kind::FORALL)
        {
          assert(vars.find(cur[0]) != vars.end());
          vars.erase(cur[0]);
        }

        if (vars.empty() && d_process_cache.insert(cur).second)
        {
          // Do not consider terms for instantiation that contain quantifiers
          if (!cur.node_info().quantifier)
          {
            d_ground_terms.push_back(cur);
          }
        }
      }
    }
    visit.pop_back();
  } while (!visit.empty());
}

bool
QuantSolver::mbqi_check(const std::vector<Node>& to_check)
{
  util::Timer timer(d_stats.time_mbqi);

  // Initialize MBQI solver
  NodeManager& nm = d_env.nm();
  option::Options options;
  options.produce_models.set(true);
  options.abstraction.set(false);
  options.pp_normalize.set(false);
  d_mbqi_solver.reset(new SolvingContext(
      d_env.nm(), options, d_env.sat_factory(), "mbqi", true));
  // Propagate the parent terminator so that a hard ground query in the MBQI
  // sub-solver still honors the user terminator and any configured resource
  // limits (the parent's resource terminator is installed as its terminator).
  d_mbqi_solver->env().configure_terminator(d_env.terminator());

  // Assert formula
  for (const Node& c : d_consts)
  {
    Node value = d_solver_state.value(c);
    d_mbqi_solver->assert_formula(nm.mk_node(Kind::EQUAL, {c, value}));
  }

  std::vector<Node> ce_q;
  std::unordered_map<Node, Node> ic_values;
  size_t num_inactive = 0;
  for (const Node& q : to_check)
  {
    ++d_stats.mbqi_checks;
    d_mbqi_solver->push();
    d_mbqi_solver->assert_formula(mbqi_inst(q));
    Log(2) << "mbqi check: " << mbqi_inst(q);
    auto res = d_mbqi_solver->solve();
    Log(2) << res;
    // Counterexample
    if (res == Result::SAT)
    {
      ce_q.push_back(q);
      // Save model values of instantiation constants
      Node cur = q;
      while (cur.kind() == Kind::FORALL)
      {
        const Node& ic = inst_const(cur);
        Node value     = d_mbqi_solver->get_value(ic);
        assert(!value.is_null());
        ic_values[ic] = value;
        cur           = cur[1];
      }
    }
    else if (res == Result::UNSAT)
    {
      ++num_inactive;
    }
    d_mbqi_solver->pop();
  }
  bool done = num_inactive == to_check.size();
  if (done)
  {
    Log(2) << "mbqi: all inactive";
    return true;
  }

  if (ce_q.empty())
  {
    return done;
  }

  // Construct ground term map
  std::unordered_map<Node, std::vector<Node>> ground_terms;
  for (const Node& t : d_ground_terms)
  {
    Node tv = d_solver_state.value(t);
    assert(!tv.is_null());
    ground_terms[tv].push_back(t);
  }

  // Generate new instantiations for quantified formulas for which we found a
  // counterexample.
  do
  {
    for (auto& [v, terms] : ground_terms)
    {
      // Sort by term counter, tie break with term id.
      std::sort(
          terms.begin(), terms.end(), [this](const auto& n1, const auto& n2) {
            auto id1      = n1.id();
            auto id2      = n2.id();
            auto num_sel1 = d_num_selected[id1];
            auto num_sel2 = d_num_selected[id2];
            return num_sel1 < num_sel2 || (num_sel1 == num_sel2 && id1 < id2);
          });
    }
    d_selected_terms.clear();
    for (const auto& q : ce_q)
    {
      mbqi_lemma(q, ic_values, ground_terms);
    }

    // If we didn't make any progress with new lemmas, increment term counters
    // and try again.
    if (!d_added_lemma)
    {
      for (const auto tid : d_selected_terms)
      {
        ++d_num_selected[tid];
      }
      ++d_stats.num_lemma_iterations;
      Log(2) << "mbqi new lemma iteration";
    }
  } while (!d_added_lemma);

  return false;
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
      d_mbqi_inst.emplace(q, d_env.nm().mk_node(Kind::NOT, {inst}));
  return iit->second;
}

bool
QuantSolver::is_expensive(const Node& node) const
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur);
    visit.pop_back();
    if (inserted)
    {
      Kind kind = cur.kind();
      // Lemmas are considered expensive if they introduce new multipliers or
      // dividers with symbolic operands.
      if ((kind == Kind::BV_MUL || kind == Kind::BV_UREM
           || kind == Kind::BV_UDIV)
          && !cur[0].is_value() && !cur[1].is_value()
          && d_process_cache.find(cur) == d_process_cache.end())
      {
        return true;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

namespace {
/**
 * Collect the free variables of `node` into `fvs`.
 * @param node The node.
 * @param fvs  Output parameter. The free variables of `node`.
 * @return True if the node has free variables.
 */
bool
free_vars(const Node& node, std::unordered_set<Node>* fvs = nullptr)
{
  bool res = false;
  std::unordered_set<Node> quants;
  std::vector<Node> vars;
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.emplace(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::VARIABLE)
      {
        vars.push_back(cur);
      }
      else if (cur.kind() == Kind::FORALL)
      {
        quants.insert(cur[0]);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  for (const auto& v : vars)
  {
    if (quants.find(v) == quants.end())
    {
      if (!fvs)
      {
        return true;
      }
      res = true;
      fvs->insert(v);
    }
  }
  return res;
}
}  // namespace

void
QuantSolver::mbqi_lemma(
    const Node& q,
    const std::unordered_map<Node, Node>& model_values,
    const std::unordered_map<Node, std::vector<Node>>& ground_terms)
{
  assert(q.kind() == Kind::FORALL);

  NodeManager& nm = d_env.nm();
  std::unordered_map<Node, Node> map;
  QuantSolver::LemmaKind lemma_kind = QuantSolver::LemmaKind::MBQI_INST;

  Node body = q;
  if (d_opt_quant_ic)
  {
    // Determine body of quantified formula for BvInverter queries.
    while (body.kind() == Kind::FORALL)
    {
      body = body[1];
    }
    // We are looking for instantions that falsifies the quantifier, thus
    // the literal for the inverter query must be negated.
    body = body.kind() == Kind::NOT ? body[0] : nm.mk_node(Kind::NOT, {body});
  }

  Node cur = q;
  std::vector<Node> conditions;
  // Dependency graph over accepted inverses: maps a variable to the prefix
  // variables its inverse (and conditions) reference.
  std::unordered_map<Node, std::unordered_set<Node>> inv_deps;
  // True if `node` (transitively) references `x` via accepted inverses.
  auto is_cyclic = [&inv_deps](const Node& node, const Node& x) {
    std::vector<Node> visit{node};
    std::unordered_set<Node> visited;
    do
    {
      Node cur = visit.back();
      visit.pop_back();
      if (cur == x)
      {
        return true;
      }
      if (!visited.insert(cur).second)
      {
        continue;
      }
      auto it = inv_deps.find(cur);
      if (it != inv_deps.end())
      {
        visit.insert(visit.end(), it->second.begin(), it->second.end());
      }
    } while (!visit.empty());
    return false;
  };
  while (cur.kind() == Kind::FORALL)
  {
    const Node& ic = inst_const(cur);
    Node value     = symbolic_term(model_values.at(ic), ground_terms);
    if (d_opt_quant_ic)
    {
      // Try to find instantiation via inverse term computation. Conditional
      // logic to actually try to find this inverse is encoded in inverse_term.
      std::unordered_set<Node> deps;
      std::vector<Node> conds;
      Node inv = inverse_term(q, cur, body, value, model_values, deps, conds);
      if (!inv.is_null())
      {
        // Accept the inverse only if closing its references keeps the
        // conditions acyclic over the fresh instantiation constants.
        // That is, no referenced variable may (transitively) reference this
        // variable through an already accepted inverse. A cyclic system of
        // constraints over fresh instantiation constants is potentially
        // unsatisfiable and yields an unsound lemma. Note that a rejected
        // inverse is not cached so that we may retry for the variable later
        // (when the referencing inverse is blocked by the cache and thus
        // no cycling system is produced).
        bool acyclic = true;
        for (const auto& fv : deps)
        {
          if (is_cyclic(fv, cur[0]))
          {
            acyclic = false;
            break;
          }
        }
        if (acyclic)
        {
          d_inv_cache.insert(cur);
          value      = inv;
          lemma_kind = QuantSolver::LemmaKind::MBQI_INST_INV;
          conditions.insert(conditions.end(), conds.begin(), conds.end());
          inv_deps.emplace(cur[0], std::move(deps));
        }
      }
    }
    // Cache the number of value instantations per quantifier.
    if (value.is_value())
    {
      d_value_insts[cur] += 1;
    }
    // Map instantiation.
    map.emplace(cur[0], value);
    assert(!ic.is_null());
    cur = cur[1];
  }
  Node inst = substitute(cur, map);
  Node lem  = nm.mk_node(Kind::IMPLIES, {q, inst});
  // Inverse term instantiations are potentially conditional, we conjunct
  // these conditions to the instantiation lemma.
  if (!conditions.empty())
  {
    Node cond = utils::mk_nary(nm, Kind::AND, conditions);
    cond      = substitute(cond, map);
    lem       = nm.mk_node(Kind::AND, {cond, lem});
  }
  // This is mainly to document that this can never happen since we ensure
  // in inverse_term() that we use an inverse as is only under safe conditions,
  // and else introduce a fresh constant that the variable is mapped to.
  assert(!free_vars(lem));
  lemma(lem, lemma_kind);
}

Node
QuantSolver::symbolic_term(
    const Node& term,
    const std::unordered_map<Node, std::vector<Node>>& ground_terms)
{
  if (ground_terms.empty())
  {
    return term;
  }

  std::vector<Node> visit{term};
  std::unordered_map<Node, Node> cache;

  NodeManager& nm = d_env.nm();
  while (!visit.empty())
  {
    Node cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (cur.is_value())
      {
        auto itt = ground_terms.find(cur);
        if (itt != ground_terms.end())
        {
          assert(!itt->second.empty());
          it->second = itt->second.front();
          d_selected_terms.push_back(it->second.id());
        }
        else
        {
          it->second = cur;
        }
      }
      else
      {
        it->second = utils::rebuild_node(nm, cur, cache);
      }
    }
    visit.pop_back();
  }
  return cache.at(term);
}

std::pair<BitVector, BitVector>
QuantSolver::get_value_for_operands(
    const Node& q,
    const Node& node,
    const std::unordered_map<Node, Node>& model_values)
{
  assert(node.kind() == Kind::EQUAL || node.kind() == Kind::BV_ULT
         || node.kind() == Kind::BV_SLT);
  assert(node[0].type().is_bv());

  std::unordered_map<Node, Node> substs;
  Node cur = q;
  while (cur.kind() == Kind::FORALL)
  {
    auto it = d_instantiation_consts.find(cur);
    assert(it != d_instantiation_consts.end());
    const Node& ic = it->second;
    substs.emplace(cur[0], model_values.at(ic));
    cur = cur[1];
  }

  Node instantiated = substitute(node, substs);
  return {d_solver_state.value(instantiated[0]).value<BitVector>(),
          d_solver_state.value(instantiated[1]).value<BitVector>()};
}

std::pair<Node, std::unordered_map<Node, size_t>>
QuantSolver::project(const Node& q,
                     const Node& node,
                     const Node& var,
                     const std::unordered_map<Node, Node>& model_values)
{
  Node res  = node;
  auto path = d_bv_inverter.compute_path(node, var);

  if (!path.empty() && d_opt_quant_ic_bounds)
  {
    std::vector<Node> work;
    Node cur = node;
    assert(path.find(node) != path.end());
    Kind kind = cur.kind();

    while (cur != var)
    {
      work.push_back(cur);

      if (kind == Kind::BV_ULT || kind == Kind::BV_SLT)
      {
        break;
      }

      cur  = cur[path[cur]];
      kind = cur.kind();
    }
    if (cur != var)
    {
      NodeManager& nm   = d_env.nm();
      auto [val0, val1] = get_value_for_operands(q, cur, model_values);
      int32_t cmp       = cur.kind() == Kind::BV_SLT ? val0.signed_compare(val1)
                                                     : val0.compare(val1);
      Node s, t;
      if (cmp == 0)
      {
        // treat as (cur[0] = cur[1])
        s = cur[0];
        t = cur[1];
      }
      else if (cmp < 0)
      {
        // treat as (cur[0] + 1 = cur[1])
        s = nm.mk_node(
            Kind::BV_ADD,
            {cur[0], nm.mk_value(BitVector::mk_one(cur[1].type().bv_size()))});
        t = cur[1];
      }
      else
      {
        // treat as (cur[0] = cur[1] + 1)
        s = cur[0];
        t = nm.mk_node(
            Kind::BV_ADD,
            {cur[1], nm.mk_value(BitVector::mk_one(cur[1].type().bv_size()))});
      }
      // Rebuild nodes in path.
      assert(work.back() == cur);
      work.pop_back();
      kind = Kind::EQUAL;
      std::vector<Node> children{s, t};
      res = nm.mk_node(kind, children);
      assert(cur != res);
      while (!work.empty())
      {
        cur = work.back();
        work.pop_back();
        children.clear();
        auto idx = path.at(cur);
        for (size_t i = 0, num = cur.num_children(); i < num; ++i)
        {
          if (i == idx)
          {
            children.push_back(res);
          }
          else
          {
            children.push_back(cur[i]);
          }
        }
        res = utils::rebuild_node(nm, cur, children);
      }
      path = d_bv_inverter.compute_path(res, var);
    }
  }

  return {res, path};
}

Node
QuantSolver::inverse_term(const Node& q,
                          const Node& q_cur,
                          const Node& body,
                          const Node& value,
                          const std::unordered_map<Node, Node>& model_values,
                          std::unordered_set<Node>& deps,
                          std::vector<Node>& conditions)
{
  assert(q.kind() == Kind::FORALL);
  assert(q_cur.kind() == Kind::FORALL);
  // The variable to find an instantiation for.
  const Node& var = q_cur[0];
  // Only try to compute IC-based lemma for bit-vector variables, and only
  // if default strategy does not find a symbolic instantiation.
  if (value.is_value() && value.type().is_bv()
      && !body.is_value()
      // Also, only if we have tried d_opt_quant_ic_value_limit value
      // instantiations for this quantifier first.
      && d_value_insts[q_cur] >= d_opt_quant_ic_value_limit)
  {
    // Also, only generate one per quantifier.
    if (d_inv_cache.find(q_cur) != d_inv_cache.end())
    {
      return Node();
    }

    auto [bbody, path]   = project(q, body, var, model_values);
    auto [invert, conds] = d_bv_inverter.invert(bbody, var, path);
    if (!invert.is_null())
    {
      bool filtered = false;
      if (d_opt_quant_ic_filter)
      {
        filtered = is_expensive(invert);
        for (const auto& c : conds)
        {
          if (filtered)
          {
            break;
          }
          filtered |= is_expensive(c);
        }
      }
      // If filtering option is enabled, we do not use potentially
      // expensive IC lemmas for instantiation. Filtered inverses are cached
      // (subsequent inverses for this variable will be as expensive);
      // returned inverses are cached by the caller if accepted.
      if (filtered)
      {
        d_inv_cache.insert(q_cur);
      }
      else
      {
        // Free variables may occur in the inverse and its conditions in case
        // of nested/chained quantifiers. We report them to the caller via
        // `deps`: variables already mapped to an instantiation (earlier in
        // the quantifier prefix) may be referenced symbolically, all others
        // (later in the prefix) are pinned by the caller to their default
        // ground instantiation. This stratifies the conditions over the
        // fresh instantiation constants: each condition only references
        // ground terms or constants introduced for variables processed
        // earlier. Otherwise, the conditions of multiple variables may form
        // a cyclic system of constraints over their fresh instantiation
        // constants, which is potentially unsatisfiable and thus unsound to
        // assert.
        bool has_fvs = free_vars(invert, &deps);
        for (const auto& c : conds)
        {
          free_vars(c, &deps);
        }
        conditions.insert(conditions.end(), conds.begin(), conds.end());
        // We only use an inverse as-is if it does not contain free variables
        // to ensure that instantiation in lemmas does not pull in free
        // variables. In case it does (variables of the quantifier prefix,
        // see above), we introduce a fresh constant that `var` is mapped to.
        if (!has_fvs)
        {
          return invert;
        }
        NodeManager& nm = d_env.nm();
        Node a          = nm.mk_const(var.type());
        conditions.push_back(nm.mk_node(Kind::EQUAL, {a, invert}));
        return a;
      }
    }
  }
  return Node();
}

QuantSolver::Statistics::Statistics(util::Statistics& stats,
                                    const std::string& prefix)
    : mbqi_checks(stats.new_stat<uint64_t>(prefix + "mbqi_checks")),
      num_lemmas(stats.new_stat<uint64_t>(prefix + "num_lemmas")),
      num_lemma_iterations(
          stats.new_stat<uint64_t>(prefix + "num_lemma_iterations")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check")),
      time_process(
          stats.new_stat<util::TimerStatistic>(prefix + "time_process")),
      time_mbqi(stats.new_stat<util::TimerStatistic>(prefix + "time_mbqi"))

{
}

}  // namespace bzla::quant
