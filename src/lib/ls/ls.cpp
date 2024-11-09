/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "ls.h"

#include <algorithm>
#include <cassert>
#include <iostream>

#include "bv/bitvector.h"
#include "ls/bv/bitvector_node.h"
#include "ls/internal.h"
#include "rng/rng.h"

namespace bzla {
namespace ls {

/* -------------------------------------------------------------------------- */

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream& ostream) { (void) ostream; }
};

/* -------------------------------------------------------------------------- */

std::ostream&
operator<<(std::ostream& out, const NodeKind& kind)
{
  out << std::to_string(kind);
  return out;
}

/* -------------------------------------------------------------------------- */

template <class VALUE>
struct LocalSearchMove
{
  LocalSearchMove() : d_nprops(0), d_nupdates(0), d_input(nullptr) {}

  LocalSearchMove(uint64_t nprops,
                  uint64_t nupdates,
                  Node<VALUE>* input,
                  VALUE assignment)
      : d_nprops(nprops),
        d_nupdates(nupdates),
        d_input(input),
        d_assignment(assignment)
  {
  }

  uint64_t d_nprops;
  uint64_t d_nupdates;
  Node<VALUE>* d_input;
  VALUE d_assignment;
};

template struct LocalSearchMove<BitVector>;

/* -------------------------------------------------------------------------- */

template <class VALUE>
LocalSearch<VALUE>::LocalSearch(uint64_t max_nprops,
                                uint64_t max_nupdates,
                                uint32_t seed,
                                uint32_t log_level,
                                uint32_t verbosity_level,
                                const std::string& stats_prefix,
                                const std::string& log_prefix,
                                util::Statistics* statistics)
    : d_max_nprops(max_nprops),
      d_max_nupdates(max_nupdates),
      d_seed(seed),
      d_stats(statistics ? statistics : new util::Statistics()),
      d_stats_needs_free(statistics == nullptr),
      d_internal(new Internal(
          *d_stats, stats_prefix, log_level, verbosity_level, log_prefix)),
      d_logger(d_internal->d_logger)

{
  d_rng.reset(new RNG(d_seed));
}

template <class VALUE>
LocalSearch<VALUE>::~LocalSearch()
{
  if (d_stats_needs_free)
  {
    delete d_stats;
  }
}

template <class VALUE>
typename LocalSearch<VALUE>::Statistics
LocalSearch<VALUE>::statistics() const
{
  const auto& stats = d_internal->d_stats;
#ifndef NDEBUG
  std::unordered_map<std::string, uint64_t> num_inv_values;
  {
    const auto& keys   = stats.num_inv_values.names();
    const auto& values = stats.num_inv_values.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_inv_values.emplace(keys[i], values[i]);
    }
  }
  std::unordered_map<std::string, uint64_t> num_cons_values;
  {
    const auto& keys   = stats.num_cons_values.names();
    const auto& values = stats.num_cons_values.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_cons_values.emplace(keys[i], values[i]);
    }
  }
  std::unordered_map<std::string, uint64_t> num_conflicts_per_kind;
  {
    const auto& keys   = stats.num_conflicts_per_kind.names();
    const auto& values = stats.num_conflicts_per_kind.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_conflicts_per_kind.emplace(keys[i], values[i]);
    }
  }
#endif
  return {stats.num_roots,
          stats.num_roots_ineq,
          stats.num_props,
          stats.num_updates,
          stats.num_moves,
          stats.num_props_inv,
          stats.num_props_cons,
          stats.num_conflicts,
#ifndef NDEBUG
          num_inv_values,
          num_cons_values,
          num_conflicts_per_kind
#endif
  };
}

template <class VALUE>
void
LocalSearch<VALUE>::init()
{
  Node<VALUE>::s_path_sel_essential  = d_options.use_path_sel_essential;
  Node<VALUE>::s_prob_pick_ess_input = d_options.prob_pick_ess_input;
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::num_moves() const
{
  return d_internal->d_stats.num_moves;
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::num_props() const
{
  return d_internal->d_stats.num_props;
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::num_updates() const
{
  return d_internal->d_stats.num_updates;
}

template <class VALUE>
void
LocalSearch<VALUE>::push()
{
  Log(1) << "push";
  d_roots_control.push_back(d_roots.size());
}

template <class VALUE>
void
LocalSearch<VALUE>::pop()
{
  Log(1) << "pop";
  if (d_roots_control.size())
  {
    size_t nroots = d_roots.size() - d_roots_control.back();
    d_roots_control.pop_back();
    for (size_t i = 0; i < nroots; ++i)
    {
      uint64_t id       = d_roots.back();
      Node<VALUE>* root = get_node(id);
      d_roots.pop_back();
      auto it = d_roots_cnt.find(id);
      assert(it != d_roots_cnt.end());
      if (it->second == 1)
      {
        d_roots_unsat.erase(id);
        d_roots_ineq.erase(root);
        root->set_is_root(false);
        d_roots_cnt.erase(it);
      }
      else
      {
        it->second -= 1;
      }
    }
  }
}

template <class VALUE>
const VALUE&
LocalSearch<VALUE>::get_assignment(uint64_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->assignment();
}

template <class VALUE>
void
LocalSearch<VALUE>::set_assignment(uint64_t id, const VALUE& assignment)
{
  assert(id < d_nodes.size());  // API check
  get_node(id)->set_assignment(assignment);
}

template <class VALUE>
void
LocalSearch<VALUE>::register_root(uint64_t id, bool fixed)
{
  assert(id < d_nodes.size());  // API check

  // register root
  if (fixed && d_roots_control.size())
  {
    d_roots.insert(d_roots.begin(), id);  // insert at level 0
    // update assertion level indices (shift by 1)
    for (size_t i = 0, n = d_roots_control.size(); i < n; ++i)
    {
      d_roots_control[i] += 1;
    }
  }
  else
  {
    d_roots.push_back(id);
  }
  // mark node as root node
  Node<VALUE>* root = get_node(id);
  root->set_is_root(true);
  // update root cnt (to safe guard against duplicates)
  auto [it, inserted] = d_roots_cnt.emplace(id, 1);
  if (!inserted)
  {
    it->second += 1;
  }
  // register inequality root
  if (root->is_inequality())
  {
    d_roots_ineq.insert({root, true});
  }
  if (root->is_not() && (*root)[0]->is_inequality())
  {
    d_roots_ineq.insert({(*root)[0], false});
  }
  // update set of unsat roots
  update_unsat_roots(root);
}

template <class VALUE>
uint32_t
LocalSearch<VALUE>::get_arity(uint64_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->arity();
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::get_child(uint64_t id, uint32_t idx) const
{
  assert(id < d_nodes.size());  // API check
  assert(idx < get_arity(id));  // API check
  return (*get_node(id))[idx]->id();
}

/* -------------------------------------------------------------------------- */

template <class VALUE>
Node<VALUE>*
LocalSearch<VALUE>::get_node(uint64_t id) const
{
  assert(id < d_nodes.size());
  assert(d_nodes[id]->id() == id);
  return d_nodes[id].get();
}

template <class VALUE>
bool
LocalSearch<VALUE>::is_leaf_node(const Node<VALUE>* node) const
{
  assert(node);
  return node->arity() == 0;
}

template <class VALUE>
bool
LocalSearch<VALUE>::is_ineq_root(const Node<VALUE>* node) const
{
  return d_roots_ineq.find(node) != d_roots_ineq.end();
}

template <class VALUE>
LocalSearchMove<VALUE>
LocalSearch<VALUE>::select_move(Node<VALUE>* root, const VALUE& t_root)
{
  assert(root);

  StatisticsInternal& stats = d_internal->d_stats;

  uint64_t nprops   = 0;
  uint64_t nupdates = 0;
  Node<VALUE>* cur  = root;
  VALUE t           = t_root;
  std::vector<uint64_t> ess_inputs;

  for (;;)
  {
    uint32_t arity = cur->arity();

    Log(1);
    Log(1) << " ** propagate:";
    Log(1) << "    * node: " << *cur << (cur->is_root() ? " (root)" : "");

    if (arity == 0)
    {
      Log(1) << "    *> target value: " << t;
      return LocalSearchMove(nprops, nupdates, cur, t);
    }
    if (cur->is_value() || cur->all_value())
    {
      Log(1) << "    *> target value: " << t;
      break;
    }
    else
    {
      assert(!cur->is_value());

      /* Compute min/max bounds of current node wrt. current assignment. */
      if (d_options.use_ineq_bounds)
      {
        compute_bounds(cur);
      }

      if (d_logger.is_log_enabled(1))
      {
        for (const auto& s : cur->log())
        {
          Log(1) << s;
        }
      }
      Log(1) << "    *> target value: " << t;

      /* Select path */
      auto [pos_x, all_but_one_const, checked_essential] =
          cur->select_path(t, ess_inputs);
      assert(pos_x < arity);

      Log(1) << "    *> select path: node[" << pos_x << "]";
      if (d_logger.is_log_enabled(1))
      {
        // check if checked_essential is false due to a) all but one input
        // being values or b) random path selection. In case of a), we don't
        // want to print '-', but identify the input that is not a value as
        // essential. In case of b), we print '-' to indicate that we didn't
        // check if the inputs are essential (and do not call is_essential()
        // for logging purpose in order to guarantee that a run behaves the
        // same with and without logging).
        if (!checked_essential)
        {
          uint32_t not_value = 0;
          for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
          {
            if (!(*cur)[i]->is_value())
            {
              not_value += 1;
            }
          }
          if (not_value == 1)
          {
            checked_essential = true;
            assert(ess_inputs.empty());
            ess_inputs.push_back(pos_x);
          }
        }

        for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
        {
          Log(1) << "          |- is_essential[" << i << "]: "
                 << (checked_essential
                         ? (std::find(ess_inputs.begin(), ess_inputs.end(), i)
                                    == ess_inputs.end()
                                ? "false"
                                : "true")
                         : "-");
        }
      }

      /** Select value
       *
       * 0) if all but one input are const and there exists an inverse value,
       *    pick inverse value
       * 1) else randomly choose to compute inverse over consistent value
       *    with probability BZLALS_PROB_USE_INV_VALUE
       * 2) if inverse value selected and no inverse value exists,
       *    fall back to consistent value
       * 3) if consistent value selected and no consistent value exists,
       *    conflict
       */

      if ((all_but_one_const
           || d_rng->pick_with_prob(d_options.prob_pick_inv_value))
          && cur->is_invertible(t, pos_x))
      {
        t = cur->inverse_value(t, pos_x);
        Log(1) << "    *> select inverse value: " << t;
        stats.num_props_inv += 1;
#ifndef NDEBUG
        stats.num_inv_values << cur->kind();
#endif
      }
      else if (cur->is_consistent(t, pos_x))
      {
        t = cur->consistent_value(t, pos_x);
        Log(1) << "    *> select consistent value: " << t;
        stats.num_props_cons += 1;
#ifndef NDEBUG
        stats.num_cons_values << cur->kind();
#endif
      }
      else
      {
#ifndef NDEBUG
        stats.num_conflicts_per_kind << cur->kind();
#endif
        stats.num_conflicts += 1;
        break;
      }

      // TODO skip when no progress?

      /* Propagate down */
      cur = (*cur)[pos_x];
      nprops += 1;
    }
  }

  Log(1) << "*** conflict";

  /* Conflict case */
  return LocalSearchMove<VALUE>(nprops, nupdates, nullptr, VALUE());
}

template <class VALUE>
void
LocalSearch<VALUE>::update_unsat_roots(Node<VALUE>* root)
{
  assert(root->is_root());

  uint64_t id = root->id();
  auto it     = d_roots_unsat.find(id);
  if (it != d_roots_unsat.end())
  {
    if (root->assignment().is_true())
    {
      /* remove from unsatisfied roots list */
      d_roots_unsat.erase(it);
    }
  }
  else if (root->assignment().is_false())
  {
    /* add to unsatisfied roots list */
    d_roots_unsat.insert(id);
  }
}

template <class VALUE>
void
LocalSearch<VALUE>::normalize_ids()
{
  if (d_roots.empty()) return;

  uint64_t id = 0;
  std::unordered_map<Node<VALUE>*, bool> cache;

  std::vector<Node<VALUE>*> visit;
  for (auto root : d_roots)
  {
    visit.push_back(get_node(root));
  }

  do
  {
    Node<VALUE>* cur    = visit.back();
    auto [it, inserted] = cache.emplace(cur, true);
    if (inserted)
    {
      for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
      {
        visit.push_back((*cur)[i]);
      }
      continue;
    }
    else if (it->second)
    {
      it->second = false;
      cur->set_normalized_id(id++);
    }
    visit.pop_back();
  } while (!visit.empty());
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::update_cone(Node<VALUE>* node, const VALUE& assignment)
{
  util::Timer timer(d_internal->d_stats.time_update_cone);

  assert(node);
  assert(is_leaf_node(node));

  Log(1) << "*** update cone: " << *node << " with: " << assignment;
  Log(1);
#ifndef NDEBUG
  for (uint64_t id : d_roots_unsat)
  {
    assert(get_node(id)->assignment().is_false());
  }
#endif

  /* nothing to do if node already has given assignment */
  if (node->assignment().compare(assignment) == 0) return 0;

  /* update assignment of given node */
  node->set_assignment(assignment);
  uint64_t nupdates = 1;

  std::vector<Node<VALUE>*> cone;
  std::vector<Node<VALUE>*> to_visit;
  std::unordered_set<Node<VALUE>*> visited;

  /* reset cone */
  const std::unordered_set<uint64_t>& parents = d_parents.at(node->id());
  for (uint64_t p : parents)
  {
    to_visit.push_back(get_node(p));
  }

  while (!to_visit.empty())
  {
    Node<VALUE>* cur = to_visit.back();
    to_visit.pop_back();

    if (visited.find(cur) != visited.end()) continue;
    visited.insert(cur);
    cone.push_back(cur);

    const std::unordered_set<uint64_t>& parents = d_parents.at(cur->id());
    for (uint64_t p : parents)
    {
      to_visit.push_back(get_node(p));
    }
  }

  /* update assignments of cone */
  if (node->is_root())
  {
    update_unsat_roots(node);
  }

  std::sort(
      cone.begin(), cone.end(), [](const Node<VALUE>* a, const Node<VALUE>* b) {
        return a->normalized_id() < b->normalized_id();
      });

  for (Node<VALUE>* cur : cone)
  {
    Log(2) << "  node: " << *cur;
    cur->evaluate();
    Log(2) << "      -> new assignment: " << cur->assignment();
    nupdates += 1;
    if (d_logger.is_log_enabled(2))
    {
      for (const auto& s : cur->log())
      {
        Log(2) << s;
      }
    }
    Log(2);

    if (cur->is_root())
    {
      update_unsat_roots(cur);
    }
  }
#ifndef NDEBUG
  for (uint64_t id : d_roots_unsat)
  {
    assert(get_node(id)->assignment().is_false());
  }
#endif
  return nupdates;
}

template <class VALUE>
Result
LocalSearch<VALUE>::move()
{
  StatisticsInternal& stats = d_internal->d_stats;

  util::Timer timer(stats.time_move);

  Log(1) << "----------------------------------------------------------------";
  Log(1) << "*** move: " << stats.num_moves + 1;
  Log(1) << "----------------------------------------------------------------";

  if (d_logger.is_log_enabled(1))
  {
    Log(1) << "    unsatisfied roots:";
    for (uint64_t id : d_roots_unsat)
    {
      Log(1) << "      - " << *get_node(id);
    }
    Log(1);
    Log(1) << "    satisfied roots:";
    for (uint64_t id : d_roots)
    {
      if (d_roots_unsat.find(id) != d_roots_unsat.end()) continue;
      Log(1) << "      + " << *get_node(id);
    }
  }

  if (d_roots_unsat.empty()) return Result::SAT;

  LocalSearchMove<VALUE> m;
  do
  {
    if (d_max_nprops > 0 && stats.num_props >= d_max_nprops)
    {
      return Result::UNKNOWN;
    }
    if (d_max_nupdates > 0 && stats.num_updates >= d_max_nupdates)
    {
      return Result::UNKNOWN;
    }

    Node<VALUE>* root =
        get_node(d_rng->pick_from_set<std::unordered_set<uint64_t>, uint64_t>(
            d_roots_unsat));

    if (root->is_value_false())
    {
      // Store root responsible for unsat result.
      d_false_root = root->id();
      return Result::UNSAT;
    }

    Log(1);
    Log(1) << " ** select constraint: " << *root;

    m = select_move(root, *d_true);
    stats.num_props += m.d_nprops;
    stats.num_updates += m.d_nupdates;
  } while (m.d_input == nullptr);

  assert(!m.d_assignment.is_null());

  Log(1);
  Log(1) << " >> move";
  Log(1) << "  | input: " << *m.d_input;
  Log(1) << "  | prev. assignment: " << m.d_input->assignment();
  Log(1) << "  | new   assignment: " << m.d_assignment;
  Log(1);

  stats.num_moves += 1;
  stats.num_updates += update_cone(m.d_input, m.d_assignment);
  stats.num_roots       = d_roots.size();
  stats.num_roots_ineq  = d_roots_ineq.size();
  stats.num_roots_unsat = d_roots_unsat.size();
  stats.num_roots_sat   = d_roots.size() - stats.num_roots_unsat;

  Log(1) << "*** number of propagations: " << stats.num_props;
  Log(1) << "*** number of updates: " << stats.num_updates;
  Log(1);
  if (d_roots_unsat.empty())
  {
    Log(1) << " all roots satisfied";
    return Result::SAT;
  }
  return Result::UNKNOWN;
}

template class LocalSearch<BitVector>;

/* -------------------------------------------------------------------------- */

}  // namespace ls
}  // namespace bzla

namespace std {
std::string
to_string(bzla::ls::NodeKind kind)
{
  switch (kind)
  {
    case bzla::ls::NodeKind::AND: return "and";
    case bzla::ls::NodeKind::CONST: return "const";
    case bzla::ls::NodeKind::EQ: return "eq";
    case bzla::ls::NodeKind::ITE: return "ite";
    case bzla::ls::NodeKind::NOT: return "not";
    case bzla::ls::NodeKind::XOR: return "xor";
    case bzla::ls::NodeKind::BV_ADD: return "bvadd";
    case bzla::ls::NodeKind::BV_AND: return "bvand";
    case bzla::ls::NodeKind::BV_ASHR: return "bvashr";
    case bzla::ls::NodeKind::BV_CONCAT: return "bvconcat";
    case bzla::ls::NodeKind::BV_EXTRACT: return "bvextract";
    case bzla::ls::NodeKind::BV_MUL: return "bvmul";
    case bzla::ls::NodeKind::BV_NOT: return "bvnot";
    case bzla::ls::NodeKind::BV_SEXT: return "bvsext";
    case bzla::ls::NodeKind::BV_SHL: return "bvshl";
    case bzla::ls::NodeKind::BV_SHR: return "bvshr";
    case bzla::ls::NodeKind::BV_SLT: return "bvslt";
    case bzla::ls::NodeKind::BV_UDIV: return "bvudiv";
    case bzla::ls::NodeKind::BV_ULT: return "bvult";
    case bzla::ls::NodeKind::BV_UREM: return "bvurem";
    case bzla::ls::NodeKind::BV_XOR: return "bvxor";
    default: assert(false);
  }
  return "";
}
}  // namespace std
