/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/array/array_solver.h"

#include <algorithm>
#include <deque>
#include <map>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "type/card.h"
#include "util/integer.h"
#include "util/logger.h"

namespace bzla::array {

using namespace node;

/* --- LemmaId public --------------------------------------------------- */

std::ostream&
operator<<(std::ostream& os, const LemmaId& lid)
{
  switch (lid)
  {
    case LemmaId::ACCESS_CONST_ARRAY: os << "ACCESS_CONST_ARRAY"; break;
    case LemmaId::CONST_ARRAY_DIFF: os << "CONST_ARRAY_DIFF"; break;
    case LemmaId::ACCESS_STORE: os << "ACCESS_STORE"; break;
    case LemmaId::CONGRUENCE: os << "CONGRUENCE"; break;
    case LemmaId::DISEQUALITY: os << "DISEQUALITY"; break;
  }
  return os;
}

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
      d_parents(state.backtrack_mgr()),
      d_active_parents(state.backtrack_mgr()),
      d_disequality_lemma_cache(state.backtrack_mgr()),
      d_const_array_eq_lemma_cache(state.backtrack_mgr()),
      d_stats(env.statistics(), "solver::array::"),
      d_logger(env.logger())
{
}

ArraySolver::~ArraySolver() {}

bool
ArraySolver::check()
{
  Log(1);
  Log(1) << "*** check arrays";

  d_array_models.clear();
  d_updated_indices.clear();
  d_accesses.clear();

  // Nothing to check
  if (d_equalities.empty() && d_selects.empty())
  {
    return true;
  }

  d_in_check = true;

  util::Timer timer(d_stats.time_check);
  d_check_access_cache.clear();
  d_lemma_cache.clear();
  ++d_stats.num_checks;
  d_active_equalities.clear();
  d_eq_const_arrays.clear();

  // Get current assignment for register equalities and populate
  // d_active_equalities.
  Log(2) << "active equalities:";
  for (const Node& eq : d_equalities)
  {
    bool val = d_solver_state.value(eq).value<bool>();
    Log(2) << "  " << (val ? "true" : "false") << ": " << eq;
    d_active_equalities.emplace(eq, val);
    compute_parents(eq);
  }

  // Check selects and equalities until fixed-point
  size_t i_sel = 0, i_eq = 0, i_ca = 0;
  while (i_sel < d_selects.size() || i_eq < d_equalities.size()
         || i_ca < d_eq_const_arrays.size())
  {
    // Do not cache size here since d_selects may grow while iterating.
    while (i_sel < d_selects.size())
    {
      Node sel = d_selects[i_sel++];
      check_access(sel);
    }

    // Do not cache size here since d_equalities may grow while iterating.
    while (i_eq < d_equalities.size())
    {
      Node eq = d_equalities[i_eq++];
      check_equality(eq);
    }

    // Do not cache size here since d_eq_const_arrays may grow while iterating.
    while (i_ca < d_eq_const_arrays.size())
    {
      Node ca = d_eq_const_arrays[i_ca++];
      check_default_value(ca);
    }
  }
  d_in_check = false;
  return true;
}

Node
ArraySolver::value(const Node& term)
{
  assert(term.type().is_array() || is_theory_leaf(term));
  assert(!d_in_check);

  Kind k = term.kind();
  if (k == Kind::EQUAL)
  {
    // Only not registered equalities should be queried, for all others we can
    // use the value in the bit-vector abstraction. This should only happen
    // when values are queried for equalities that are not part of the
    // bit-vector abstraction.
    assert(std::find(d_equalities.begin(), d_equalities.end(), term)
           == std::end(d_equalities));
    std::unordered_map<Node, Node> cache;
    Node a1 = construct_model_value(term[0], cache);
    Node a2 = construct_model_value(term[1], cache);
    return d_env.nm().mk_value(a1 == a2);
  }
  else if (k == Kind::SELECT)
  {
    // Select index from constructed normalized array value.
    std::unordered_map<Node, Node> cache;
    return construct_model_value(term[0], cache, d_solver_state.value(term[1]));
  }

  // Construct normalized array value, i.e., ordered by index
  std::unordered_map<Node, Node> cache;
  return construct_model_value(term, cache);
}

void
ArraySolver::register_term(const Node& term)
{
  if (term.kind() == Kind::SELECT)
  {
    d_selects.push_back(term);
    ++d_stats.num_selects;
  }
  else if (term.kind() == Kind::EQUAL)
  {
    assert(term[0].type().is_array());
    d_equalities.push_back(term);
    ++d_stats.num_equalities;
  }
  else
  {
    // nothing to do here
    assert(term.kind() == Kind::STORE);
  }
}

/* --- ArraySolver private -------------------------------------------------- */

const ArraySolver::Access*
ArraySolver::get_access(const Node& acc)
{
  if (acc.kind() == Kind::CONST_ARRAY)
  {
    auto it = d_accesses.try_emplace(
        acc, acc, const_array_index(acc), d_solver_state);
    return &it.first->second;
  }
  auto it = d_accesses.try_emplace(acc, acc, d_solver_state);
  return &it.first->second;
}

void
ArraySolver::check_access(const Node& access)
{
  auto [it, inserted] = d_check_access_cache.insert(access);
  if (!inserted)
  {
    return;
  }

  Log(2);
  Log(1) << "check: " << access;
  const Access* acc = get_access(access);
  Log(2) << "index:   " << acc->index_value();
  Log(2) << "element: " << acc->element_value();
  node_ref_vector visit{acc->array()};
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
      if (!is_equal(acc, *it))
      {
        Log(2) << "\u2716 congruence lemma";
        Log(2) << "access1: " << acc->get();
        Log(2) << "access2: " << (*it)->get();
        add_congruence_lemma(array, *acc, **it);
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
        if (acc->index_value() == index_value)
        {
          if (!is_equal(acc, array[2]))
          {
            Log(2) << "\u2716 access store lemma";
            Log(2) << "access: " << acc->get();
            Log(2) << "store: " << array;
            add_access_store_lemma(*acc, array);
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
        if (!is_equal(acc, array[0]))
        {
          // check_access only propagates non-constant-array accesses; constant
          // array default-value propagation (and the const-array equality
          // lemma) is handled by check_default_value.
          assert(acc->get().kind() != Kind::CONST_ARRAY);
          Log(2) << "\u2716 const array lemma";
          Log(2) << "access: " << acc->get();
          Log(2) << "array: " << array;
          add_access_const_array_lemma(*acc, array);
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
            if (index_value != acc->index_value())
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

namespace {

// Look-ahead: would adding `index` to the covered set still leave at least one
// index of the range uncovered, i.e., should the default value keep being
// propagated?
bool
propagate_dv(const std::unordered_map<Node, uint64_t>& indices,
             const Node& index)
{
  size_t size = indices.size() + (indices.count(index) ? 0 : 1);
  return type::cardinality_gt(index.type(), size);
}

// Index coverage for default-value propagation in check_default_value: the
// intersection of the store indices overwritten along every propagation path
// expanded so far. An index loses the constant array's default value only if
// overwritten on all paths, so a node is re-expanded whenever a new path
// shrinks the set. For base arrays the result is recorded in d_updated_indices
// and consumed by construct_model_value.
struct Coverage
{
  // Initialize the coverage from the current path on the node's first visit.
  void update(const std::unordered_map<Node, uint64_t>& indices)
  {
    for (const auto& [idx, cnt] : indices)
    {
      d_cov.insert(idx);
    }
  }

  // Intersect the coverage with the current path indices (`indices` plus
  // `upd_index`, not yet added to `indices`). Returns true and stores the
  // smaller set if it shrinks (re-expand the node); returns false unchanged
  // otherwise (stop).
  bool intersect(const Node& upd_index,
                 const std::unordered_map<Node, uint64_t>& indices)
  {
    std::unordered_set<Node> isect;
    for (const Node& idx : d_cov)
    {
      if (idx == upd_index || indices.find(idx) != indices.end())
      {
        isect.insert(idx);
      }
    }
    if (isect.size() == d_cov.size())
    {
      return false;
    }
    d_cov = std::move(isect);
    return true;
  }

  auto size() const { return d_cov.size(); }
  auto begin() { return d_cov.begin(); }
  auto end() { return d_cov.end(); }

 private:
  std::unordered_set<Node> d_cov;
};

}  // namespace

void
ArraySolver::check_default_value(const Node& const_array)
{
  assert(const_array.kind() == Kind::CONST_ARRAY);

  auto [it, inserted] = d_check_access_cache.insert(const_array);
  if (!inserted)
  {
    return;
  }

  Log(2);
  Log(1) << "check dv: " << const_array;
  const Access* acc = get_access(const_array);
  Log(2) << "element: " << acc->element_value();

  // Worklist of default value propagation steps. Each step records the node
  // `reason` that reached `array` while propagating the default value:
  //  - `index` is the store index value for store reasons (null otherwise)
  //  - `reason` is the store/ite/equality node that contributes the reason
  //  (and, for stores, the updated index) for propagating a default value
  struct PropStep
  {
    Node array;             // Node we reached via `reason`
    Node index;             // Overwritten store index value (null non-store)
    Node reason;            // Store/ite/equality node that reached `array`
    bool expanded = false;  // Was this step expanded (pre-order)?
  };

  // Maps visited array to computed index coverage.
  std::unordered_map<Node, Coverage> coverage_map;
  // Nodes currently on active propagation path, subset of arrays on visit stack
  std::unordered_set<Node> active_path;
  // Propagation worklist
  std::vector<PropStep> visit{{acc->array(), Node(), Node()}};
  // Accumulates the updated indices along the current propagation path. Maps
  // index value to number of index occurrences.
  std::unordered_map<Node, uint64_t> indices;
  do
  {
    // Post-order traversal
    if (visit.back().expanded)
    {
      // Unwind expanded step: remove the index overwritten by the reason store
      // that reached `array`.
      const PropStep& step = visit.back();
      if (!step.index.is_null())
      {
        auto itt = indices.find(step.index);
        assert(itt != indices.end());
        assert(itt->second > 0);
        if (--itt->second == 0)
        {
          Log(2) << "remove index: " << step.index;
          indices.erase(itt);
        }
      }
      active_path.erase(step.array);
      visit.pop_back();
      continue;
    }

    const Node array     = visit.back().array;
    const Node upd_index = visit.back().index;
    const Node reason    = visit.back().reason;
    Log(2) << "> array: " << array;
    ++d_stats.num_propagations;

    // Avoid propagation cycles: `array` is already on the active path.
    if (active_path.find(array) != active_path.end())
    {
      visit.pop_back();
      continue;
    }

    auto [itv, first_visit] = coverage_map.try_emplace(array);
    auto& cov               = itv->second;
    if (!first_visit && !cov.intersect(upd_index, indices))
    {
      // Already propagated to this array with smaller or equal coverage.
      visit.pop_back();
      continue;
    }

    // Expand step.
    visit.back().expanded = true;
    active_path.insert(array);
    d_array_models[array].insert(acc);

    // Collect index along the propagation path to `array`.
    if (!upd_index.is_null())
    {
      assert(!reason.is_null());
      assert(reason.kind() == Kind::STORE);
      ++indices[upd_index];
    }
    if (first_visit)
    {
      // Initialize the running coverage with the current path's coverage.
      cov.update(indices);
    }

    if (array.kind() == Kind::STORE)
    {
      Node index_value = d_solver_state.value(array[1]);
      Log(2) << "index: " << index_value;

      // Propagate down only if not all indices are covered.
      if (propagate_dv(indices, index_value)
          && active_path.find(array[0]) == active_path.end())
      {
        visit.push_back({array[0], index_value, array});
        ++d_stats.num_propagations_down;
        Log(2) << "D store: " << array[0] << ", indices=" << indices.size();
      }
    }
    else if (array.kind() == Kind::ITE)
    {
      Node cond_value  = d_solver_state.value(array[0]);
      const Node& next = cond_value.value<bool>() ? array[1] : array[2];
      if (active_path.find(next) == active_path.end())
      {
        visit.push_back({next, Node(), array});
        ++d_stats.num_propagations_down;
        Log(2) << "D ite: " << next;
      }
    }
    else if (array.kind() == Kind::CONST_ARRAY)
    {
      if (!is_equal(acc, array[0]))
      {
        assert(acc->get().kind() == Kind::CONST_ARRAY);
        // Collect current propagation path from visit worklist.
        std::vector<std::pair<Node, bool>> prop_path;
        for (const auto& step : visit)
        {
          if (!step.expanded)
          {
            continue;
          }
          // Did we reach array via downward store propagation?
          bool down = !step.index.is_null() && step.array == step.reason[0];
          prop_path.emplace_back(step.reason, down);
        }

        if (add_const_array_equality_lemma(*acc, array, prop_path))
        {
          return;
        }
      }
    }
    else
    {
      assert(array.kind() == Kind::CONSTANT || array.kind() == Kind::SELECT
             || array.kind() == Kind::APPLY);
      // Record the indices overwritten along the propagation path(s) to this
      // base array for use in model construction. `cov` is already the
      // intersection over all paths expanded so far (always < cardinality): an
      // index only loses the default value if it is overwritten on every
      // propagation path.
      assert(type::cardinality_gt(array.type().array_index(), cov.size()));
      d_updated_indices[{array.id(), const_array.id()}] =
          std::vector<Node>(cov.begin(), cov.end());
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
          if (active_path.find(parent) != active_path.end())
          {
            continue;
          }
          Node index_value = d_solver_state.value(parent[1]);
          // The upward propagation overwrites the parent store's index.
          if (propagate_dv(indices, index_value))
          {
            visit.push_back({parent, index_value, parent});
            ++d_stats.num_propagations_up;
            Log(2) << "U store: " << parent << ", indices=" << indices.size();
          }
        }
        else if (parent.kind() == Kind::ITE)
        {
          if (active_path.find(parent) != active_path.end())
          {
            continue;
          }
          assert(parent.type().is_array());
          bool cond_value = d_solver_state.value(parent[0]).value<bool>();
          if ((cond_value && array == parent[1])
              || (!cond_value && array == parent[2]))
          {
            visit.push_back({parent, Node(), parent});
            ++d_stats.num_propagations_up;
            Log(2) << "U ite: " << parent;
          }
        }
        else
        {
          assert(parent.kind() == Kind::EQUAL);
          assert(parent[0].type().is_array());
          bool eq_value = d_solver_state.value(parent).value<bool>();
          if (eq_value)
          {
            assert(parent[0] == array || parent[1] == array);
            const Node& next = parent[0] == array ? parent[1] : parent[0];
            if (active_path.find(next) == active_path.end())
            {
              visit.push_back({next, Node(), parent});
              ++d_stats.num_propagations_up;
              Log(2) << "U eq: " << next;
            }
          }
        }
      }
    }
  } while (!visit.empty());
  assert(indices.empty());
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
        // Only when we have nested arrays
        else if (cur.kind() == Kind::SELECT)
        {
          assert(cur.type().is_array());
          check_access(cur);
        }
        else if (cur.kind() == Kind::CONST_ARRAY)
        {
          d_eq_const_arrays.push_back(cur);
        }
      }
    } while (!visit.empty());
  }
  else
  {
    auto [sel_a, sel_b] = add_disequality_lemma(eq);
    check_access(sel_a);
    check_access(sel_b);
  }
}

void
ArraySolver::add_access_store_lemma(const Access& acc, const Node& store)
{
  assert(store.kind() == Kind::STORE);

  NodeManager& nm = d_env.nm();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc.element(), store[2]});

  std::vector<Node> conjuncts;
  collect_path_conditions(acc, store, conjuncts);
  conjuncts.push_back(nm.mk_node(Kind::EQUAL, {acc.index(), store[1]}));
  d_stats.num_lemma_size << conjuncts.size();
  Node lem =
      nm.mk_node(Kind::IMPLIES,
                 {node::utils::mk_nary(nm, Kind::AND, conjuncts), conclusion});
  lemma(lem, LemmaId::ACCESS_STORE);
}

void
ArraySolver::add_access_const_array_lemma(const Access& acc, const Node& array)
{
  assert(array.kind() == Kind::CONST_ARRAY);

  NodeManager& nm = d_env.nm();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc.element(), array[0]});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc, array, conjuncts);
  d_stats.num_lemma_size << conjuncts.size();
  Node lem;

  // Direct access on constant array
  if (conjuncts.empty())
  {
    lem = conclusion;
  }
  else
  {
    lem = nm.mk_node(
        Kind::IMPLIES,
        {node::utils::mk_nary(nm, Kind::AND, conjuncts), conclusion});
  }
  lemma(lem, LemmaId::ACCESS_CONST_ARRAY);
}

bool
ArraySolver::add_const_array_equality_lemma(
    const Access& acc,
    const Node& array,
    const std::vector<std::pair<Node, bool>>& prop_path)
{
  assert(acc.get().kind() == Kind::CONST_ARRAY);
  assert(array.kind() == Kind::CONST_ARRAY);

  NodeManager& nm = d_env.nm();
  std::vector<Node> conditions, indices;

  std::vector<Node> stores_down, stores_up;
  std::unordered_set<Node> cond_cache, index_cache;
  for (const auto& [preason, pdown] : prop_path)
  {
    if (preason.is_null())
    {
      continue;
    }
    if (preason.kind() == Kind::STORE)
    {
      if (index_cache.insert(preason[1]).second)
      {
        indices.push_back(preason[1]);
      }
      (pdown ? stores_down : stores_up).push_back(preason[2]);
    }
    else
    {
      assert(preason.kind() == Kind::EQUAL || preason.kind() == Kind::ITE);
      add_path_condition(acc, preason, conditions, cond_cache);
    }
  }
  assert(!conditions.empty());

  Node conc;
  if (indices.empty())
  {
    conc = nm.mk_node(Kind::EQUAL, {acc.element(), array[0]});
  }
  else
  {
    // The DISTINCT_N(N,...) cardinality argument N is only used relative to the
    // number of index children M: if N exceeds M the constraint is false, so
    // its exact value only matters when N <= M. Clamping N to M + 1 therefore
    // yields identical behavior while avoiding the construction of the
    // (potentially large) precise index-type cardinality.
    util::Integer min_card =
        type::cardinality_min(acc.index().type(), indices.size() + 1);
    BitVector bv_card(min_card.base2_size(), min_card.gmp_value(), false);
    // Move to solver engine
    d_solver_state.register_distinct_heuristic(indices);
    indices.insert(indices.begin(), nm.mk_value(bv_card));
    conc = nm.mk_node(Kind::OR,
                      {nm.mk_node(Kind::DISTINCT_N, indices),
                       nm.mk_node(Kind::EQUAL, {acc.element(), array[0]})});
  }
  Node lem = d_env.rewriter().rewrite(nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(nm, Kind::AND, conditions), conc}));

  // We only add this lemma once per pair of constant arrays
  if (d_const_array_eq_lemma_cache.insert(lem).second)
  {
    lemma(lem, LemmaId::CONST_ARRAY_DIFF);
    if (!stores_down.empty())
    {
      std::vector<Node> elements_acc{acc.element()};
      elements_acc.insert(
          elements_acc.end(), stores_down.begin(), stores_down.end());
      d_solver_state.register_eq_heuristic(elements_acc);
    }
    if (!stores_up.empty())
    {
      std::vector<Node> elements_arr{array[0]};
      elements_arr.insert(
          elements_arr.end(), stores_up.begin(), stores_up.end());
      d_solver_state.register_eq_heuristic(elements_arr);
    }
    return true;
  }
  return false;
}

void
ArraySolver::add_congruence_lemma(const Node& array,
                                  const Access& acc1,
                                  const Access& acc2)
{
  assert(acc1.get() != acc2.get());

  NodeManager& nm = d_env.nm();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc1.element(), acc2.element()});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc1, array, conjuncts);
  collect_path_conditions(acc2, array, conjuncts);
  conjuncts.push_back(nm.mk_node(Kind::EQUAL, {acc1.index(), acc2.index()}));
  d_stats.num_lemma_size << conjuncts.size();
  Node lem =
      nm.mk_node(Kind::IMPLIES,
                 {node::utils::mk_nary(nm, Kind::AND, conjuncts), conclusion});
  lemma(lem, LemmaId::CONGRUENCE);
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

  // Find shortest path from access to array. This is only used for regular
  // (non-constant-array) accesses; constant-array default propagation records
  // its exact path in check_default_value.
  assert(access.get().kind() != Kind::CONST_ARRAY);
  std::deque<std::pair<ConstNodeRef, bool>> visit;
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
                Log(3) << "R: " << parent[1] << " -> " << parent;
              }
              else
              {
                assert(parent[1] == cur);
                visit.emplace_back(parent[0], false);
                path.emplace(parent[0], parent);
                Log(3) << "L: " << parent[0] << " -> " << parent;
              }
            }
          }
        }
      }
    }
    visit.pop_front();
  } while (!visit.empty());

  // Construct path conditions
  // If access was propagated upwards to target array, we have to include its
  // propagation condition.
  std::unordered_set<Node> cond_cache;
  if (prop_up_to_target)
  {
    add_path_condition(access, array, conditions, cond_cache);
  }
#ifndef NDEBUG
  unordered_node_ref_set pcache;
#endif
  Node prev = array;
  auto it = path.find(array);
  while (true)
  {
    assert(it != path.end());
    const Node& cur = it->second;
    prev = cur;
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
                                std::unordered_set<Node>& cache)
{
  Log(3) << "path: " << array;
  NodeManager& nm = d_env.nm();
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
      Log(3) << "  duplicate: " << cond;
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

  NodeManager& nm = d_env.nm();
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
  lemma(lem, LemmaId::DISEQUALITY);
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
      d_parents.add(cur[0], cur);
      d_parents.add(cur[1], cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (cur.kind() == Kind::STORE)
    {
      ++d_stats.num_stores;
      d_parents.add(cur[0], cur);
      visit.push_back(cur[0]);
    }
    else if (cur.kind() == Kind::ITE)
    {
      d_parents.add(cur[1], cur);
      d_parents.add(cur[2], cur);
      visit.push_back(cur[1]);
      visit.push_back(cur[2]);
    }
  } while (!visit.empty());
}

void
ArraySolver::lemma(const Node& lemma, const LemmaId lid)
{
  Node lem            = d_env.rewriter().rewrite(lemma);
  auto [it, inserted] = d_lemma_cache.insert(lem);
  // Do not send duplicate lemmas in this check() round.
  if (inserted)
  {
    d_stats.lemmas << lid;
    d_solver_state.lemma(lem);
  }
}

Node
ArraySolver::construct_model_value(const Node& array,
                                   std::unordered_map<Node, Node>& cache,
                                   const Node& selected_index)
{
  assert(!d_in_check);
  assert(array.type().is_array());

  auto it = cache.find(array);
  if (it != cache.end())
  {
    return it->second;
  }

  std::map<Node, Node> map;
  Node cur = array;
  while (cur.kind() == Kind::STORE || cur.kind() == Kind::ITE)
  {
    Kind k = cur.kind();
    if (k == Kind::STORE)
    {
      Node index          = d_solver_state.value(cur[1]);
      auto [it, inserted] = map.emplace(index, Node());
      if (inserted)
      {
        it->second = construct_element_value(cur[2], cache);
        if (index == selected_index)
        {
          return it->second;
        }
      }
      cur = cur[0];
    }
    else if (k == Kind::ITE)
    {
      cur = d_solver_state.value(cur[0]).value<bool>() ? cur[1] : cur[2];
    }
  }

  NodeManager& nm = d_env.nm();
  Node res;
  if (cur.kind() == Kind::CONST_ARRAY)
  {
    res = nm.mk_const_array(cur.type(), construct_element_value(cur[0], cache));
  }
  else
  {
    assert(cur.kind() == Kind::CONSTANT || cur.kind() == Kind::SELECT
           || cur.kind() == Kind::APPLY);

    Log(2) << "construct model value: " << array;

    auto it = d_array_models.find(cur);
    std::unordered_map<Node, std::unordered_set<Node>> const_arrays;
    if (it != d_array_models.end())
    {
      for (const auto acc : it->second)
      {
        const Node& acc_node = acc->get();
        if (acc_node.kind() == Kind::CONST_ARRAY)
        {
          // Store indices overwritten along the propagation path of this
          // constant array's default value, as recorded by check_default_value.
          // Default value propagation guarantees this set is strictly smaller
          // than the index cardinality, so the default value applies to at
          // least one index of cur.
          assert(d_updated_indices.find({cur.id(), acc_node.id()})
                 != d_updated_indices.end());
          const auto& indices = d_updated_indices.at({cur.id(), acc_node.id()});
          Log(2) << "covered indices: " << indices.size()
                 << ", dv=" << acc_node;
          assert(type::cardinality_gt(acc->index().type(), indices.size()));
          auto [cit, inserted] = const_arrays.try_emplace(
              construct_model_value(acc_node, cache),
              std::unordered_set<Node>(indices.begin(), indices.end()));
          if (!inserted)
          {
            // Multiple equality paths connect `cur` to the same constant-array
            // default value. An index keeps that default unless it is
            // overwritten on *every* such path, so intersect the covered-index
            // sets (the coverage-minimizing combination). Otherwise an index
            // that is free on one path but overwritten on another would be
            // wrongly treated as unconstrained and filled with the generic
            // default value.
            std::unordered_set<Node> intersection;
            for (const Node& idx : indices)
            {
              if (cit->second.count(idx))
              {
                intersection.insert(idx);
              }
            }
            cit->second = std::move(intersection);
          }
          continue;
        }
        Node index           = d_solver_state.value(acc->index());
        auto [itm, inserted] = map.emplace(index, Node());
        if (inserted)
        {
          itm->second = construct_element_value(acc->element(), cache);
          if (index == selected_index)
          {
            return itm->second;
          }
        }
      }
    }

    if (d_logger.is_log_enabled(2))
    {
      for (const auto& [i, v] : map)
      {
        Log(2) << "  " << i << " -> " << v;
      }
    }

    Node default_value;
    // Construct model value from propagated constant arrays.
    if (!const_arrays.empty())
    {
      Node dca;
      size_t min_undefined = 0;
      std::unordered_set<Node> all_indices, overlap_indices;
      std::unordered_map<Node, size_t> index_count;
      for (const auto& [ca, updated_indices] : const_arrays)
      {
        // Pick default value from constant array with the most "missing"
        // indices. That is, the missing indices need to be initialized with
        // the default value of the selected constant array, otherwise, the
        // equality between the constant array and this array does not hold.
        // The indices that are overwritten can have different values,
        // that are determined by other constant arrays if present.
        if (dca.is_null() || min_undefined > updated_indices.size())
        {
          dca           = ca;
          min_undefined = updated_indices.size();
        }
        for (const auto& i : updated_indices)
        {
          all_indices.insert(i);
          ++index_count[i];
          // Store index that overlaps for all constant arrays. We later store a
          // canonical value on this index.
          if (index_count[i] == const_arrays.size())
          {
            overlap_indices.insert(i);
          }
        }
      }

      // Add default values of each constant array for missing indices,
      // there should not be any overlap of default values, i.e., a
      // missing index has two different default values.
      //
      // Array-typed element defaults are compared by node identity here, which
      // doesn't capture model equality (e.g. a STORE chain vs. an equivalent
      // constant array), so the consistency asserts below only hold for scalar
      // defaults; the constructed model is validated by --check-model anyway.
      // For example, <1>(00->0)(01->0) and <0>(11->1)(10->1) are equal, but
      // not the same nodes.
      default_value = d_solver_state.value(dca[0]);
      for (const auto& [ca, updated_indices] : const_arrays)
      {
        if (ca == dca)
        {
          continue;
        }
        Node dv = d_solver_state.value(ca[0]);
        for (const auto& idx : all_indices)
        {
          if (updated_indices.find(idx) == updated_indices.end())
          {
            assert(array.type().array_element().is_array()
                   || map.find(idx) == map.end()
                   || map.find(idx)->second == dv);
            map.emplace(idx, dv);
          }
        }
      }
#ifndef NDEBUG
      {
        const auto& updated_indices = const_arrays[dca];
        for (const auto& idx : all_indices)
        {
          if (updated_indices.find(idx) == updated_indices.end())
          {
            assert(array.type().array_element().is_array()
                   || map.find(idx) == map.end()
                   || map.find(idx)->second == default_value);
          }
        }
      }
#endif
      // For overlapping indices, we can always pick a default value.
      for (const auto& idx : overlap_indices)
      {
        map.emplace(idx,
                    utils::mk_default_value(nm, array.type().array_element()));
      }
    }

    if (default_value.is_null())
    {
      res = utils::mk_default_value(nm, cur.type());
    }
    else
    {
      // For nested constant arrays (array-typed elements) the default value is
      // the constructed model of the inner array, which may be a non-uniform
      // (STORE-chain) array rather than a value or constant array.
      assert(default_value.is_value() || default_value.type().is_array());
      res = nm.mk_const_array(cur.type(), default_value);
    }
  }
  assert(res.kind() == Kind::CONST_ARRAY);

  if (!selected_index.is_null())
  {
    return res[0];
  }

  const Node& default_value = res[0];
  for (const auto& [index, value] : map)
  {
    if (value != default_value)
    {
      res = nm.mk_node(Kind::STORE, {res, index, value});
    }
  }
  cache.emplace(array, res);
  return res;
}

Node
ArraySolver::construct_element_value(const Node& term,
                                     std::unordered_map<Node, Node>& cache)
{
  if (term.type().is_array())
  {
    return construct_model_value(term, cache);
  }
  return d_solver_state.value(term);
}

bool
ArraySolver::is_equal(const Access* acc1, const Access* acc2)
{
  if (acc1->element().type().is_array())
  {
    return is_equal(acc1, acc2->element());
  }
  return acc1->element_value() == acc2->element_value();
}

bool
ArraySolver::is_equal(const Access* acc, const Node& a)
{
  if (acc->element().type().is_array())
  {
    if (acc->element() == a)
    {
      return true;
    }
    Node eq = d_env.nm().mk_node(Kind::EQUAL, {acc->element(), a});
    Node rw = d_env.rewriter().rewrite(eq);
    auto it = d_active_equalities.find(rw);
    if (it != d_active_equalities.end())
    {
      return it->second;
    }
    return d_solver_state.value(rw).value<bool>();
  }
  return acc->element_value() == d_solver_state.value(a);
}

Node
ArraySolver::const_array_index(const Node& const_array)
{
  auto it = d_const_array_indices.find(const_array);
  if (it == d_const_array_indices.end())
  {
    Node idx = d_env.nm().mk_const(const_array.type().array_index());
    d_const_array_indices.emplace(const_array, idx);
    return idx;
  }
  return it->second;
}

ArraySolver::Statistics::Statistics(util::Statistics& stats,
                                    const std::string& prefix)
    : num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      num_propagations(stats.new_stat<uint64_t>(prefix + "propagations")),
      num_propagations_up(stats.new_stat<uint64_t>(prefix + "propagations_up")),
      num_propagations_down(
          stats.new_stat<uint64_t>(prefix + "propagations_down")),
      num_selects(stats.new_stat<uint64_t>(prefix + "selects")),
      num_stores(stats.new_stat<uint64_t>(prefix + "stores")),
      num_equalities(stats.new_stat<uint64_t>(prefix + "equalities")),
      num_lemma_size(
          stats.new_stat<util::HistogramStatistic>(prefix + "lemma_size")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
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

  if (element().type().is_array())
  {
    // Array values are always considered to be incomplete/partial unless the
    // array solver concludes that everything is consistent. Equality is handled
    // separately for these terms.
    d_value = element();
  }
  else
  {
    // Cache value of access
    d_value = state.value(element());
  }
}

ArraySolver::Access::Access(const Node& ca,
                            const Node& ca_index,
                            SolverState& state)
    : d_access(ca), d_hash(0), d_const_array_index(ca_index)
{
  assert(ca.kind() == Kind::CONST_ARRAY);

  // Compute hash value of function applications based on the current function
  // argument model values.
  d_index_value = index();
  d_hash += std::hash<Node>{}(d_index_value);

  if (element().type().is_array())
  {
    // Array values are always considered to be incomplete/partial unless the
    // array solver concludes that everything is consistent. Equality is handled
    // separately for these terms.
    d_value = element();
  }
  else
  {
    // Cache value of access
    d_value = state.value(element());
  }
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
  else if (d_access.kind() == Kind::CONST_ARRAY)
  {
    return d_access[0];
  }
  return d_access[2];
}

const Node&
ArraySolver::Access::index() const
{
  if (d_access.kind() == Kind::CONST_ARRAY)
  {
    return d_const_array_index;
  }
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

size_t
ArraySolver::Access::hash() const
{
  return d_hash;
}

}  // namespace bzla::array
