#include "solver/array/array_solver.h"

#include "node/node_manager.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "solver/solver_engine.h"
//#include "util/logger.h"

namespace bzla::array {

using namespace node;

/* --- ArraySolver public --------------------------------------------------- */

bool
ArraySolver::is_leaf(const Node& term)
{
  Kind k = term.kind();
  return k == Kind::SELECT || (k == Kind::EQUAL && (term[0].type().is_array()));
}

ArraySolver::ArraySolver(SolverEngine& solver_engine)
    : Solver(solver_engine),
      d_selects(solver_engine.backtrack_mgr()),
      d_equalities(solver_engine.backtrack_mgr()),
      d_stats(solver_engine.statistics())
{
}

ArraySolver::~ArraySolver() {}

void
ArraySolver::check()
{
  d_array_models.clear();
  d_check_access_cache.clear();
  ++d_stats.num_check_calls;

  // Do not cache size here since d_selects may grow while iterating.
  for (size_t i = 0; i < d_selects.size(); ++i)
  {
    check_access(d_selects[i]);
  }

  for (size_t i = 0; i < d_equalities.size(); ++i)
  {
    check_equality(d_equalities[i]);
  }
  // TODO: in case of equality we also have to propagate constant arrays upwards
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

  // Log(1) << "\ncheck: " << access;
  Access acc(access, d_solver_engine);
  // Log(2) << "index:   " << acc.index_value();
  // Log(2) << "element: " << acc.element_value();
  node_ref_vector visit{acc.array()};
  do
  {
    const Node& array = visit.back();
    visit.pop_back();
    // Log(2) << "> array: " << array;
    ++d_stats.num_propagations;

    auto& array_model   = d_array_models[array];
    auto [it, inserted] = array_model.insert(acc);
    if (!inserted)
    {
      // Check congruence conflict
      if (acc.element_value() != it->element_value())
      {
        // Log(2) << "\u2716 congruence lemma";
        // Log(2) << "access1: " << acc.get();
        // Log(2) << "access2: " << it->get();
        add_congruence_lemma(array, acc, *it);
      }
    }
    else
    {
      if (array.kind() == Kind::STORE)
      {
        Node index_value = d_solver_engine.value(array[1]);
        // Check access-over-write consistency
        if (acc.index_value() == index_value)
        {
          Node element_value = d_solver_engine.value(array[2]);
          if (acc.element_value() != element_value)
          {
            // Log(2) << "\u2716 access store lemma";
            // Log(2) << "access: " << acc.get();
            // Log(2) << "store: " << array;
            add_access_store_lemma(acc, array);
          }
        }
        else
        {
          visit.push_back(array[0]);
          ++d_stats.num_propagations_down;
          // Log(2) << "D store: " << visit.back();
        }
      }
      else if (array.kind() == Kind::CONST_ARRAY)
      {
        Node element_value = d_solver_engine.value(array[1]);
        if (acc.element_value() != element_value)
        {
          add_access_const_array_lemma(acc, array);
        }
      }
      else if (array.kind() == Kind::ITE)
      {
        Node cond_value = d_solver_engine.value(array[0]);
        visit.push_back(cond_value.value<bool>() ? array[1] : array[2]);
        ++d_stats.num_propagations_down;
        // Log(2) << "D ite: " << visit.back();
      }
      else
      {
        assert(array.kind() == Kind::CONSTANT);
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
            Node index_value = d_solver_engine.value(parent[1]);
            if (index_value != acc.index_value())
            {
              visit.push_back(parent);
              ++d_stats.num_propagations_up;
              // Log(2) << "U store: " << visit.back();
            }
          }
          else if (parent.kind() == Kind::ITE)
          {
            assert(parent.type().is_array());
            bool cond_value = d_solver_engine.value(parent[0]).value<bool>();
            if ((cond_value && array == parent[1])
                || (!cond_value && array == parent[2]))
            {
              visit.push_back(parent);
              ++d_stats.num_propagations_up;
              // Log(2) << "U ite: " << visit.back();
            }
          }
          else
          {
            assert(parent.kind() == Kind::EQUAL);
            assert(parent[0].type().is_array());
            bool eq_value = d_solver_engine.value(parent).value<bool>();
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
              // Log(2) << "U eq: " << visit.back();
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

  if (d_solver_engine.value(eq).value<bool>())
  {
    // Find and check top-most array stores
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
        }
        else if (cur.kind() == Kind::ITE)
        {
          Node cond_value = d_solver_engine.value(cur[0]);
          visit.push_back(cond_value.value<bool>() ? cur[1] : cur[2]);
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

  NodeManager& nm = NodeManager::get();
  Node conclusion = nm.mk_node(Kind::EQUAL, {acc.element(), store[2]});
  std::vector<Node> conjuncts;
  collect_path_conditions(acc, store, conjuncts);
  conjuncts.push_back(nm.mk_node(Kind::EQUAL, {acc.index(), store[1]}));
  d_stats.num_lemma_size << conjuncts.size();
  Node lemma = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  d_solver_engine.lemma(lemma);
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
  Node lemma = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  d_solver_engine.lemma(lemma);
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
  Node lemma = nm.mk_node(
      Kind::IMPLIES, {node::utils::mk_nary(Kind::AND, conjuncts), conclusion});
  d_solver_engine.lemma(lemma);
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

  node_ref_vector visit{access.array()};
  unordered_node_ref_map<Node> path;
  unordered_node_ref_set cache;

  // Log(3) << "collect path: " << access.get();
  // Log(3) << "start: " << visit.back();
  // Log(3) << "goal:  " << array;

  // Find shortest path from access to array
  do
  {
    const Node& cur = visit.front();
    visit.erase(visit.begin());
    if (cur == array)
    {
      break;
    }

    auto [it, inserted] = cache.insert(cur);
    if (!inserted)
    {
      continue;
    }

    // Search downwards
    if (cur.kind() == Kind::STORE)
    {
      if (d_solver_engine.value(cur[1]) != access.index_value())
      {
        visit.push_back(cur[0]);
        path.emplace(cur[0], cur);
        // Log(3) << "D: " << cur[0] << " -> " << cur;
      }
    }
    else if (cur.kind() == Kind::ITE)
    {
      Node cond_value = d_solver_engine.value(cur[0]);
      if (cond_value.value<bool>())
      {
        visit.push_back(cur[1]);
        path.emplace(cur[1], cur);
        // Log(3) << "D: " << cur[1] << " -> " << cur;
      }
      else
      {
        visit.push_back(cur[2]);
        path.emplace(cur[2], cur);
        // Log(3) << "D: " << cur[2] << " -> " << cur;
      }
    }
    else
    {
      assert(cur.kind() == Kind::CONSTANT || cur.kind() == Kind::CONST_ARRAY);
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
          Node index_value = d_solver_engine.value(parent[1]);
          if (index_value != access.index_value())
          {
            visit.push_back(parent);
            path.emplace(parent, cur);
            // Log(3) << "U: " << parent << " -> " << cur;
          }
        }
        else if (parent.kind() == Kind::ITE)
        {
          assert(parent.type().is_array());
          bool cond_value = d_solver_engine.value(parent[0]).value<bool>();
          if ((cond_value && cur == parent[1])
              || (!cond_value && cur == parent[2]))
          {
            visit.push_back(parent);
            path.emplace(parent, cur);
            // Log(3) << "U: " << parent << " -> " << cur;
          }
        }
        else
        {
          assert(parent.kind() == Kind::EQUAL);
          assert(parent[0].type().is_array());
          bool eq_value = d_solver_engine.value(parent).value<bool>();
          if (eq_value)
          {
            path.emplace(parent, cur);
            // Log(3) << "U: " << parent << " -> " << cur;
            if (parent[0] == cur)
            {
              visit.push_back(parent[1]);
              path.emplace(parent[1], parent);
              // Log(3) << "U: " << parent[1] << " -> " << parent;
            }
            else
            {
              assert(parent[1] == cur);
              visit.push_back(parent[0]);
              path.emplace(parent[0], parent);
              // Log(3) << "U: " << parent[0] << " -> " << parent;
            }
          }
        }
      }
    }
  } while (!visit.empty());

  // TODO: make cache for conditions to filter out duplicates
  // Construct path conditions
#ifndef NDEBUG
  unordered_node_ref_set pcache;
#endif
  NodeManager& nm = NodeManager::get();
  auto it         = path.find(array);
  while (true)
  {
    assert(it != path.end());
    const Node& cur = it->second;
#ifndef NDEBUG
    auto [itc, inserted] = pcache.insert(cur);
    assert(inserted);
#endif
    if (cur.kind() == Kind::STORE)
    {
      // Do not include the access itself
      if (cur != access.get())
      {
        conditions.push_back(
            nm.mk_node(Kind::DISTINCT, {cur[1], access.index()}));
      }
    }
    else if (cur.kind() == Kind::ITE)
    {
      Node cond_value = d_solver_engine.value(cur[0]);
      if (cond_value.value<bool>())
      {
        conditions.push_back(cur[0]);
      }
      else
      {
        conditions.push_back(nm.mk_node(Kind::NOT, {cur[0]}));
      }
    }
    else if (cur.kind() == Kind::EQUAL)
    {
      conditions.push_back(cur);
    }
    else
    {
      assert(cur.kind() == Kind::CONSTANT);
    }
    // Found start array
    if (cur == access.array())
    {
      break;
    }
    it = path.find(cur);
    assert(path.find(cur) != path.end());
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
  const Node& a   = eq[0];
  const Node& b   = eq[1];
  Node k          = nm.mk_const(a.type().array_index());
  Node sel_a      = nm.mk_node(Kind::SELECT, {a, k});
  Node sel_b      = nm.mk_node(Kind::SELECT, {b, k});
  Node lemma      = nm.mk_node(Kind::IMPLIES,
                          {nm.mk_node(Kind::NOT, {eq}),
                                nm.mk_node(Kind::DISTINCT, {sel_a, sel_b})});
  d_solver_engine.lemma(lemma);
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

ArraySolver::Statistics::Statistics(util::Statistics& stats)
    : num_check_calls(stats.new_stat<uint64_t>("array::check_calls")),
      num_propagations(stats.new_stat<uint64_t>("array::propagations")),
      num_propagations_up(stats.new_stat<uint64_t>("array::propagations_up")),
      num_propagations_down(
          stats.new_stat<uint64_t>("array::propagations_down")),
      num_lemma_size(
          stats.new_stat<util::HistogramStatistic>("array::lemma_size"))
{
}

/* --- Access public -------------------------------------------------------- */

ArraySolver::Access::Access(const Node& access, SolverEngine& solver_engine)
    : d_access(access), d_hash(0)
{
  assert(access.kind() == Kind::SELECT || access.kind() == Kind::STORE);

  // Compute hash value of function applications based on the current function
  // argument model values.
  d_index_value = solver_engine.value(index());
  d_hash += std::hash<Node>{}(d_index_value);

  // Cache value of access
  d_value = solver_engine.value(element());
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
