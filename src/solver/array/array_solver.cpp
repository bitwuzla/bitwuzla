#include "solver/array/array_solver.h"

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "util/logger.h"

namespace bzla::array {

using namespace node;

/* --- ArraySolver public --------------------------------------------------- */

bool
ArraySolver::is_theory_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::SELECT || (k == Kind::EQUAL && (term[0].type().is_array()));
}

ArraySolver::ArraySolver(Env& env, SolverState& state)
    : Solver(env, state),
      d_selects(state.backtrack_mgr()),
      d_equalities(state.backtrack_mgr()),
      d_stats(env.statistics()),
      d_logger(env.options().log_level(), env.options().verbosity())
{
}

ArraySolver::~ArraySolver() {}

bool
ArraySolver::check()
{
  Log(1) << "\n*** check arrays";
  util::Timer timer(d_stats.time_check);
  d_array_models.clear();
  d_check_access_cache.clear();
  d_lemma_cache.clear();
  ++d_stats.num_checks;

  // Check selects and equalities until fixed-point
  size_t i_sel = 0, i_eq = 0;
  while (i_sel < d_selects.size() || i_eq < d_equalities.size())
  {
    // Do not cache size here since d_selects may grow while iterating.
    while (i_sel < d_selects.size())
    {
      check_access(d_selects[i_sel++]);
    }

    // Do not cache size here since d_selects may grow while iterating.
    while (i_eq < d_equalities.size())
    {
      check_equality(d_equalities[i_eq++]);
    }
    // TODO: in case of equality we also have to propagate constant arrays
    // upwards
  }
  return true;
}

Node
ArraySolver::value(const Node& term)
{
  assert(term.type().is_array());
  // TODO: not fully done, we also need to include stores under term
  Node res = utils::mk_default_value(term.type());
  auto it  = d_array_models.find(term);
  if (it != d_array_models.end())
  {
    NodeManager& nm         = NodeManager::get();
    const auto& array_model = it->second;

    // Construct nested store chains for array model
    for (const auto& select : array_model)
    {
      res = nm.mk_node(Kind::STORE,
                       {res, select.index_value(), select.element_value()});
    }
  }
  return res;
}

void
ArraySolver::register_term(const Node& term)
{
  if (term.kind() == Kind::SELECT)
  {
    d_selects.push_back(term);
  }
  else
  {
    assert(term.kind() == Kind::EQUAL);
    assert(term[0].type().is_array());
    d_equalities.push_back(term);
    compute_parents(term);
  }
}

/* --- ArraySolver private -------------------------------------------------- */

void
ArraySolver::check_access(const Node& access)
{
  auto [it, inserted] = d_check_access_cache.insert(access);
  if (!inserted)
  {
    return;
  }

  Log(1) << "\ncheck: " << access;
  Access acc(access, d_solver_state);
  Log(2) << "index:   " << acc.index_value();
  Log(2) << "element: " << acc.element_value();
  node_ref_vector visit{acc.array()};
  do
  {
    const Node& array = visit.back();
    visit.pop_back();
    Log(2) << "> array: " << array;
    ++d_stats.num_propagations;

    auto& array_model   = d_array_models[array];
    auto [it, inserted] = array_model.insert(acc);
    if (!inserted)
    {
      // Check congruence conflict
      if (acc.element_value() != it->element_value())
      {
        Log(2) << "\u2716 congruence lemma";
        Log(2) << "access1: " << acc.get();
        Log(2) << "access2: " << it->get();
        add_congruence_lemma(array, acc, *it);
        break;
      }
    }
    else
    {
      if (array.kind() == Kind::STORE)
      {
        Node index_value = d_solver_state.value(array[1]);
        Log(2) << "index: " << index_value;
        // Check access-over-write consistency
        if (acc.index_value() == index_value)
        {
          Node element_value = d_solver_state.value(array[2]);
          Log(2) << "value: " << element_value;
          if (acc.element_value() != element_value)
          {
            Log(2) << "\u2716 access store lemma";
            Log(2) << "access: " << acc.get();
            Log(2) << "store: " << array;
            add_access_store_lemma(acc, array);
            break;
          }
        }
        else
        {
          visit.push_back(array[0]);
          ++d_stats.num_propagations_down;
          Log(2) << "D store: " << visit.back();
        }
      }
      else if (array.kind() == Kind::CONST_ARRAY)
      {
        Node element_value = d_solver_state.value(array[1]);
        if (acc.element_value() != element_value)
        {
          add_access_const_array_lemma(acc, array);
          break;
        }
      }
      else if (array.kind() == Kind::ITE)
      {
        Node cond_value = d_solver_state.value(array[0]);
        visit.push_back(cond_value.value<bool>() ? array[1] : array[2]);
        ++d_stats.num_propagations_down;
        Log(2) << "D ite: " << visit.back();
      }
      else
      {
        assert(array.kind() == Kind::CONSTANT || array.kind() == Kind::SELECT
               || array.kind() == Kind::APPLY);
      }

      // Propagate upwards
      if (d_active_parents.find(array) != d_active_parents.end())
      {
        auto itp = d_parents.find(array);
        assert(itp != d_parents.end());
        for (const Node& parent : itp->second)
        {
          if (parent.kind() == Kind::STORE)
          {
            Node index_value = d_solver_state.value(parent[1]);
            if (index_value != acc.index_value())
            {
              visit.push_back(parent);
              ++d_stats.num_propagations_up;
              Log(2) << "U store: " << visit.back();
            }
          }
          else if (parent.kind() == Kind::ITE)
          {
            assert(parent.type().is_array());
            bool cond_value = d_solver_state.value(parent[0]).value<bool>();
            if ((cond_value && array == parent[1])
                || (!cond_value && array == parent[2]))
            {
              visit.push_back(parent);
              ++d_stats.num_propagations_up;
              Log(2) << "U ite: " << visit.back();
            }
          }
          else
          {
            assert(parent.kind() == Kind::EQUAL);
            assert(parent[0].type().is_array());
            bool eq_value = d_solver_state.value(parent).value<bool>();
            if (eq_value)
            {
              if (parent[0] == array)
              {
                visit.push_back(parent[1]);
              }
              else
              {
                assert(parent[1] == array);
                visit.push_back(parent[0]);
              }
              ++d_stats.num_propagations_up;
              Log(2) << "U eq: " << visit.back();
            }
          }
        }
      }
    }
  } while (!visit.empty());
}

void
ArraySolver::check_equality(const Node& eq)
{
  assert(eq.kind() == Kind::EQUAL);
  assert(eq[0].type().is_array());

  if (d_solver_state.value(eq).value<bool>())
  {
    // Check store terms under equality
    unordered_node_ref_set cache;
    node_ref_vector visit{eq[0], eq[1]};
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      auto [it, inserted] = cache.insert(cur);
      if (inserted)
      {
        if (cur.kind() == Kind::STORE)
        {
          check_access(cur);
          visit.push_back(cur[0]);
        }
        else if (cur.kind() == Kind::ITE)
        {
          Node cond_value = d_solver_state.value(cur[0]);
          visit.push_back(cond_value.value<bool>() ? cur[1] : cur[2]);
        }
      }
    } while (!visit.empty());
  }
  else
  {
    auto [sel_a, sel_b] = add_disequality_lemma(eq);
    // TODO: optimization: if sel_a and sel_b are created, we don't have to
    // check them since they very likely have the same values (since
    // unconstrained, and disequality lemma was just sent)
    check_access(sel_a);
    check_access(sel_b);
  }
}

void
ArraySolver::add_access_store_lemma(const Access& acc, const Node& store)
{
  assert(store.kind() == Kind::STORE);

  NodeManager& nm = NodeManager::get();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc.element(), store[2]});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc, store, conjuncts);
  conjuncts.push_back(nm.mk_node(Kind::EQUAL, {acc.index(), store[1]}));
  d_stats.num_lemma_size << conjuncts.size();
  Node lem = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  lemma(lem);
}

void
ArraySolver::add_access_const_array_lemma(const Access& acc, const Node& array)
{
  assert(array.kind() == Kind::CONST_ARRAY);

  NodeManager& nm = NodeManager::get();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc.element(), array[1]});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc, array, conjuncts);
  d_stats.num_lemma_size << conjuncts.size();
  Node lem = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  lemma(lem);
}

void
ArraySolver::add_congruence_lemma(const Node& array,
                                  const Access& acc1,
                                  const Access& acc2)
{
  assert(acc1.get() != acc2.get());

  NodeManager& nm = NodeManager::get();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc1.element(), acc2.element()});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc1, array, conjuncts);
  collect_path_conditions(acc2, array, conjuncts);
  conjuncts.push_back(nm.mk_node(Kind::EQUAL, {acc1.index(), acc2.index()}));
  d_stats.num_lemma_size << conjuncts.size();
  Node lem = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  lemma(lem);
}

void
ArraySolver::collect_path_conditions(const Access& access,
                                     const Node& array,
                                     std::vector<Node>& conditions)
{
  if (access.array() == array)
  {
    return;
  }

  Log(3) << "collect path: " << access.get();
  Log(3) << "start: " << access.array();
  Log(3) << "goal:  " << array;

  // Find shortest path from access to array
  std::vector<std::pair<ConstNodeRef, bool>> visit;
  visit.emplace_back(access.array(), false);
  unordered_node_ref_map<Node> path;
  unordered_node_ref_set cache;
  bool prop_up_to_target = false;
  do
  {
    const auto& p   = visit.front();
    const Node& cur = p.first;
    bool prop_up    = p.second;

    // Found target array
    if (cur == array)
    {
      prop_up_to_target = prop_up;
      break;
    }

    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      // Search downwards
      if (cur.kind() == Kind::STORE)
      {
        if (d_solver_state.value(cur[1]) != access.index_value())
        {
          visit.emplace_back(cur[0], false);
          path.emplace(cur[0], cur);
          Log(3) << "D: " << cur[0] << " -> " << cur;
        }
      }
      else if (cur.kind() == Kind::ITE)
      {
        Node cond_value = d_solver_state.value(cur[0]);
        if (cond_value.value<bool>())
        {
          visit.emplace_back(cur[1], false);
          path.emplace(cur[1], cur);
          Log(3) << "D: " << cur[1] << " -> " << cur;
        }
        else
        {
          visit.emplace_back(cur[2], false);
          path.emplace(cur[2], cur);
          Log(3) << "D: " << cur[2] << " -> " << cur;
        }
      }
      else
      {
        assert(cur.kind() == Kind::CONSTANT || cur.kind() == Kind::CONST_ARRAY
               || cur.kind() == Kind::SELECT || cur.kind() == Kind::APPLY);
      }

      // Search upwards
      if (d_active_parents.find(cur) != d_active_parents.end())
      {
        auto itp = d_parents.find(cur);
        assert(itp != d_parents.end());
        for (const Node& parent : itp->second)
        {
          if (parent.kind() == Kind::STORE)
          {
            Node index_value = d_solver_state.value(parent[1]);
            if (index_value != access.index_value())
            {
              visit.emplace_back(parent, true);
              path.emplace(parent, cur);
              Log(3) << "U: " << parent << " -> " << cur;
            }
          }
          else if (parent.kind() == Kind::ITE)
          {
            assert(parent.type().is_array());
            bool cond_value = d_solver_state.value(parent[0]).value<bool>();
            if ((cond_value && cur == parent[1])
                || (!cond_value && cur == parent[2]))
            {
              visit.emplace_back(parent, true);
              path.emplace(parent, cur);
              Log(3) << "U: " << parent << " -> " << cur;
            }
          }
          else
          {
            assert(parent.kind() == Kind::EQUAL);
            assert(parent[0].type().is_array());
            bool eq_value = d_solver_state.value(parent).value<bool>();
            if (eq_value)
            {
              path.emplace(parent, cur);
              Log(3) << "U: " << parent << " -> " << cur;
              if (parent[0] == cur)
              {
                visit.emplace_back(parent[1], false);
                path.emplace(parent[1], parent);
                Log(3) << "D: " << parent[1] << " -> " << parent;
              }
              else
              {
                assert(parent[1] == cur);
                visit.emplace_back(parent[0], false);
                path.emplace(parent[0], parent);
                Log(3) << "D: " << parent[0] << " -> " << parent;
              }
            }
          }
        }
      }
    }
    visit.erase(visit.begin());
  } while (!visit.empty());

  // TODO: make cache for conditions to filter out duplicates
  // Construct path conditions

  // If access was propagated upwards to target array, we have to include its
  // propagation condition.
  node::unordered_node_ref_set cond_cache;
  if (prop_up_to_target)
  {
    add_path_condition(access, array, conditions, cond_cache);
  }
#ifndef NDEBUG
  unordered_node_ref_set pcache;
#endif
  auto it = path.find(array);
  while (true)
  {
    assert(it != path.end());
    const Node& cur = it->second;
#ifndef NDEBUG
    auto [itc, inserted] = pcache.insert(cur);
    assert(inserted);
#endif
    add_path_condition(access, cur, conditions, cond_cache);
    // Found start array
    if (cur == access.array())
    {
      break;
    }
    it = path.find(cur);
  }
}

void
ArraySolver::add_path_condition(const Access& access,
                                const Node& array,
                                std::vector<Node>& conditions,
                                node::unordered_node_ref_set& cache)
{
  Log(3) << "path: " << array;
  NodeManager& nm = NodeManager::get();
  Node cond;
  if (array.kind() == Kind::STORE)
  {
    // Access got only propagated if store index is different from access index.
    if (access.index_value() != d_solver_state.value(array[1]))
    {
      cond = nm.mk_node(Kind::DISTINCT, {array[1], access.index()});
    }
  }
  else if (array.kind() == Kind::ITE)
  {
    Node cond_value = d_solver_state.value(array[0]);
    if (cond_value.value<bool>())
    {
      cond = array[0];
    }
    else
    {
      cond = nm.mk_node(Kind::NOT, {array[0]});
    }
  }
  else if (array.kind() == Kind::EQUAL)
  {
    cond = array;
  }
  else
  {
    assert(array.kind() == Kind::CONSTANT || array.kind() == Kind::CONST_ARRAY
           || array.kind() == Kind::SELECT || array.kind() == Kind::APPLY);
  }

  if (!cond.is_null())
  {
    auto [it, inserted] = cache.insert(cond);
    if (inserted)
    {
      conditions.push_back(cond);
      Log(3) << "  cond: " << cond;
    }
    else
    {
      Log(3) << "  duplicate";
    }
  }
}

std::pair<Node, Node>
ArraySolver::add_disequality_lemma(const Node& eq)
{
  auto it = d_disequality_lemma_cache.find(eq);
  if (it != d_disequality_lemma_cache.end())
  {
    return it->second;
  }

  NodeManager& nm = NodeManager::get();
  std::stringstream ss;
  ss << "@diseq_wit_" << eq.id();
  const Node& a   = eq[0];
  const Node& b   = eq[1];
  Node k          = nm.mk_const(a.type().array_index(), ss.str());
  Node sel_a      = nm.mk_node(Kind::SELECT, {a, k});
  Node sel_b      = nm.mk_node(Kind::SELECT, {b, k});
  Node lem        = nm.mk_node(Kind::IMPLIES,
                        {nm.mk_node(Kind::NOT, {eq}),
                                nm.mk_node(Kind::DISTINCT, {sel_a, sel_b})});
  lemma(lem);
  auto p = std::make_pair(sel_a, sel_b);
  d_disequality_lemma_cache.emplace(eq, p);
  return p;
}

void
ArraySolver::compute_parents(const Node& term)
{
  assert(term.kind() == Kind::EQUAL);

  node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_active_parents.insert(cur);
    if (!inserted)
    {
      continue;
    }

    if (cur.kind() == Kind::EQUAL)
    {
      d_parents[cur[0]].push_back(cur);
      d_parents[cur[1]].push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (cur.kind() == Kind::STORE)
    {
      d_parents[cur[0]].push_back(cur);
      visit.push_back(cur[0]);
    }
    else if (cur.kind() == Kind::ITE)
    {
      d_parents[cur[1]].push_back(cur);
      d_parents[cur[2]].push_back(cur);
      visit.push_back(cur[1]);
      visit.push_back(cur[2]);
    }
  } while (!visit.empty());
}

void
ArraySolver::lemma(const Node& lemma)
{
  Node lem            = d_env.rewriter().rewrite(lemma);
  auto [it, inserted] = d_lemma_cache.insert(lem);
  // Do not send duplicate lemmas in this check() round.
  if (inserted)
  {
    d_solver_state.lemma(lem);
  }
}

ArraySolver::Statistics::Statistics(util::Statistics& stats)
    : num_checks(stats.new_stat<uint64_t>("array::num_checks")),
      num_propagations(stats.new_stat<uint64_t>("array::propagations")),
      num_propagations_up(stats.new_stat<uint64_t>("array::propagations_up")),
      num_propagations_down(
          stats.new_stat<uint64_t>("array::propagations_down")),
      num_lemma_size(
          stats.new_stat<util::HistogramStatistic>("array::lemma_size")),
      time_check(stats.new_stat<util::TimerStatistic>("array::time_check"))
{
}

/* --- Access public -------------------------------------------------------- */

ArraySolver::Access::Access(const Node& access, SolverState& state)
    : d_access(access), d_hash(0)
{
  assert(access.kind() == Kind::SELECT || access.kind() == Kind::STORE);

  // Compute hash value of function applications based on the current function
  // argument model values.
  d_index_value = state.value(index());
  d_hash += std::hash<Node>{}(d_index_value);

  // Cache value of access
  d_value = state.value(element());
}

const Node&
ArraySolver::Access::get() const
{
  return d_access;
}

const Node&
ArraySolver::Access::element() const
{
  if (d_access.kind() == Kind::SELECT)
  {
    return d_access;
  }
  return d_access[2];
}

const Node&
ArraySolver::Access::index() const
{
  return d_access[1];
}

const Node&
ArraySolver::Access::array() const
{
  if (d_access.kind() == Kind::SELECT)
  {
    return d_access[0];
  }
  return d_access;
}

const Node&
ArraySolver::Access::element_value() const
{
  return d_value;
}

const Node&
ArraySolver::Access::index_value() const
{
  return d_index_value;
}

bool
ArraySolver::Access::operator==(const Access& other) const
{
  return d_index_value == other.d_index_value;
}

size_t
ArraySolver::Access::hash() const
{
  return d_hash;
}

}  // namespace bzla::array
