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

#include "util/statistics.h"
#include "bv/bitvector.h"
#include "ls/bv/bitvector_node.h"
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

#define BZLALSLOG_ENABLED(level) (d_log_level >= (level))
#define BZLALSLOGSTREAM(level) \
  !(BZLALSLOG_ENABLED(level)) ? (void) 0 : OstreamVoider() & std::cout
#define BZLALSLOG(level) BZLALSLOGSTREAM(level) << "[bzla-ls]"

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
struct LocalSearch<VALUE>::StatisticsInternal
{
  StatisticsInternal(util::Statistics& stats, const std::string& prefix);
  uint64_t& num_props;
  uint64_t& num_updates;
  uint64_t& num_moves;

  uint64_t& num_props_inv;
  uint64_t& num_props_cons;

  uint64_t& num_conflicts;

#ifndef NDEBUG
  util::HistogramStatistic& num_inv_values;
  util::HistogramStatistic& num_cons_values;
  util::HistogramStatistic& num_conflicts_per_kind;
#endif
  util::TimerStatistic& time_move;
};

template <class VALUE>
LocalSearch<VALUE>::StatisticsInternal::StatisticsInternal(
    util::Statistics& stats, const std::string& prefix)
    : num_props(stats.new_stat<uint64_t>(prefix + "num_props")),
      num_updates(stats.new_stat<uint64_t>(prefix + "num_updates")),
      num_moves(stats.new_stat<uint64_t>(prefix + "num_moves")),
      num_props_inv(stats.new_stat<uint64_t>(prefix + "num_props_inv")),
      num_props_cons(stats.new_stat<uint64_t>(prefix + "num_props_cons")),
      num_conflicts(stats.new_stat<uint64_t>(prefix + "num_conflicts")),
#ifndef NDEBUG
      num_inv_values(
          stats.new_stat<util::HistogramStatistic>(prefix + "num_inv_values")),
      num_cons_values(
          stats.new_stat<util::HistogramStatistic>(prefix + "num_cons_values")),
      num_conflicts_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_conflicts_per_kind")),
#endif
      time_move(stats.new_stat<util::TimerStatistic>(prefix + "time_move"))
{
}

/* -------------------------------------------------------------------------- */

template <class VALUE>
LocalSearch<VALUE>::LocalSearch(uint64_t max_nprops,
                                uint64_t max_nupdates,
                                uint32_t seed,
                                const std::string& stats_prefix,
                                util::Statistics* statistics)
    : d_max_nprops(max_nprops), d_max_nupdates(max_nupdates), d_seed(seed)
{
  d_rng.reset(new RNG(d_seed));
  d_stats            = statistics ? statistics : new util::Statistics();
  d_stats_needs_free = statistics == nullptr;
  d_stats_internal.reset(new StatisticsInternal(*d_stats, stats_prefix));
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
#ifndef NDEBUG
  std::unordered_map<std::string, uint64_t> num_inv_values;
  {
    const auto& keys   = d_stats_internal->num_inv_values.names();
    const auto& values = d_stats_internal->num_inv_values.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_inv_values.emplace(keys[i], values[i]);
    }
  }
  std::unordered_map<std::string, uint64_t> num_cons_values;
  {
    const auto& keys   = d_stats_internal->num_cons_values.names();
    const auto& values = d_stats_internal->num_cons_values.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_cons_values.emplace(keys[i], values[i]);
    }
  }
  std::unordered_map<std::string, uint64_t> num_conflicts_per_kind;
  {
    const auto& keys   = d_stats_internal->num_conflicts_per_kind.names();
    const auto& values = d_stats_internal->num_conflicts_per_kind.values();
    assert(keys.size() == values.size());
    for (size_t i = 0, n = keys.size(); i < n; ++i)
    {
      num_conflicts_per_kind.emplace(keys[i], values[i]);
    }
  }
#endif
  return {d_stats_internal->num_props,
          d_stats_internal->num_updates,
          d_stats_internal->num_moves,
          d_stats_internal->num_props_inv,
          d_stats_internal->num_props_cons,
          d_stats_internal->num_conflicts,
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
  return d_stats_internal->num_moves;
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::num_props() const
{
  return d_stats_internal->num_props;
}

template <class VALUE>
uint64_t
LocalSearch<VALUE>::num_updates() const
{
  return d_stats_internal->num_updates;
}

template <class VALUE>
void
LocalSearch<VALUE>::push()
{
  BZLALSLOG(1) << " push" << std::endl;
  d_roots_control.push_back(d_roots.size());
}

template <class VALUE>
void
LocalSearch<VALUE>::pop()
{
  BZLALSLOG(1) << " pop" << std::endl;
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

  StatisticsInternal& stats = *d_stats_internal;

  uint64_t nprops   = 0;
  uint64_t nupdates = 0;
  Node<VALUE>* cur  = root;
  VALUE t           = t_root;
  std::vector<uint64_t> ess_inputs;

  for (;;)
  {
    uint32_t arity = cur->arity();

    BZLALSLOG(1) << std::endl;
    BZLALSLOG(1) << "  propagate:" << std::endl;
    BZLALSLOG(1) << "    node: " << *cur << (cur->is_root() ? " (root)" : "")
                 << std::endl;

    if (arity == 0)
    {
      BZLALSLOG(1) << "    target value: " << t << std::endl;
      return LocalSearchMove(nprops, nupdates, cur, t);
    }
    if (cur->is_value() || cur->all_value())
    {
      BZLALSLOG(1) << "    target value: " << t << std::endl;
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

      if (BZLALSLOG_ENABLED(1))
      {
        for (const auto& s : cur->log())
        {
          BZLALSLOG(1) << s;
        }
      }
      BZLALSLOG(1) << "    -> target value: " << t << std::endl;

      /* Select path */
      auto [pos_x, all_but_one_const, checked_essential] =
          cur->select_path(t, ess_inputs);
      assert(pos_x < arity);

      BZLALSLOG(1) << "    -> select path: node[" << pos_x << "]" << std::endl;
      if (BZLALSLOG_ENABLED(1))
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
          BZLALSLOG(1) << "        |- is_essential[" << i << "]: "
                       << (checked_essential
                               ? (std::find(
                                      ess_inputs.begin(), ess_inputs.end(), i)
                                          == ess_inputs.end()
                                      ? "false"
                                      : "true")
                               : "-")
                       << std::endl;
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
        BZLALSLOG(1) << "    -> inverse value: " << t << std::endl;
        stats.num_props_inv += 1;
#ifndef NDEBUG
        stats.num_inv_values << cur->kind();
#endif
      }
      else if (cur->is_consistent(t, pos_x))
      {
        t = cur->consistent_value(t, pos_x);
        BZLALSLOG(1) << "    -> consistent value: " << t << std::endl;
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

  BZLALSLOG(1) << "*** conflict" << std::endl;

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
  assert(node);
  assert(is_leaf_node(node));

  BZLALSLOG(1) << "*** update cone: " << *node << " with: " << assignment
               << std::endl;
  BZLALSLOG(1) << std::endl;
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
    BZLALSLOG(2) << "  node: " << *cur << " -> ";
    cur->evaluate();
    nupdates += 1;
    BZLALSLOGSTREAM(2) << cur->assignment() << std::endl;
    if (BZLALSLOG_ENABLED(2))
    {
      for (const auto& s : cur->log())
      {
        BZLALSLOG(2) << s;
      }
    }
    BZLALSLOG(2) << std::endl;

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
  StatisticsInternal& stats = *d_stats_internal;

  util::Timer timer(stats.time_move);

  BZLALSLOG(1) << "*** move: " << stats.num_moves + 1 << std::endl;

  if (BZLALSLOG_ENABLED(1))
  {
    BZLALSLOG(1) << "  unsatisfied roots:" << std::endl;
    for (uint64_t id : d_roots_unsat)
    {
      BZLALSLOG(1) << "    - " << *get_node(id) << std::endl;
    }
    BZLALSLOG(1) << std::endl;
    BZLALSLOG(1) << "  satisfied roots:" << std::endl;
    for (uint64_t id : d_roots)
    {
      if (d_roots_unsat.find(id) != d_roots_unsat.end()) continue;
      BZLALSLOG(1) << "    - " << *get_node(id) << std::endl;
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

    BZLALSLOG(1) << std::endl;
    BZLALSLOG(1) << "  select constraint: " << *root << std::endl;

    m = select_move(root, *d_true);
    stats.num_props += m.d_nprops;
    stats.num_updates += m.d_nupdates;
  } while (m.d_input == nullptr);

  assert(!m.d_assignment.is_null());

  BZLALSLOG(1) << std::endl;
  BZLALSLOG(1) << "  move" << std::endl;
  BZLALSLOG(1) << "  input: " << *m.d_input << std::endl;
  BZLALSLOG(1) << "  prev. assignment: " << m.d_input->assignment()
               << std::endl;
  BZLALSLOG(1) << "  new   assignment: " << m.d_assignment << std::endl;
  BZLALSLOG(1) << std::endl;

  stats.num_moves += 1;
  stats.num_updates += update_cone(m.d_input, m.d_assignment);

  BZLALSLOG(1) << "*** number of propagations: " << stats.num_props
               << std::endl;
  BZLALSLOG(1) << std::endl;
  BZLALSLOG(1) << "*** number of updates: " << stats.num_updates << std::endl;
  BZLALSLOG(1) << std::endl;
  if (d_roots_unsat.empty())
  {
    BZLALSLOG(1) << " all roots satisfied" << std::endl;
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
