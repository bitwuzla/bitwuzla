#include "ls.h"

#include <algorithm>
#include <cassert>
#include <iostream>

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
  switch (kind)
  {
    case NodeKind::AND: out << "and"; break;
    case NodeKind::EQ: out << "eq"; break;
    case NodeKind::ITE: out << "ite"; break;
    case NodeKind::NOT: out << "not"; break;
    case NodeKind::XOR: out << "xor"; break;
    case NodeKind::BV_ADD: out << "bvadd"; break;
    case NodeKind::BV_AND: out << "bvand"; break;
    case NodeKind::BV_ASHR: out << "bvashr"; break;
    case NodeKind::BV_CONCAT: out << "bvconcat"; break;
    case NodeKind::BV_EXTRACT: out << "bvextract"; break;
    case NodeKind::BV_MUL: out << "bvmul"; break;
    case NodeKind::BV_NOT: out << "bvnot"; break;
    case NodeKind::BV_SEXT: out << "bvsext"; break;
    case NodeKind::BV_SHL: out << "bvshl"; break;
    case NodeKind::BV_SHR: out << "bvshr"; break;
    case NodeKind::BV_SLT: out << "bvslt"; break;
    case NodeKind::BV_UDIV: out << "bvudiv"; break;
    case NodeKind::BV_ULT: out << "bvult"; break;
    case NodeKind::BV_UREM: out << "bvurem"; break;
    case NodeKind::BV_XOR: out << "bvxor"; break;
    default: assert(false);
  }
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
                                uint32_t seed)
    : d_max_nprops(max_nprops), d_max_nupdates(max_nupdates), d_seed(seed)

{
  d_rng.reset(new RNG(d_seed));
}

template <class VALUE>
LocalSearch<VALUE>::~LocalSearch()
{
}

template <class VALUE>
void
LocalSearch<VALUE>::init()
{
  Node<VALUE>::s_path_sel_essential  = d_options.use_path_sel_essential;
  Node<VALUE>::s_prob_pick_ess_input = d_options.prob_pick_ess_input;
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
LocalSearch<VALUE>::register_root(uint64_t id)
{
  assert(id < d_nodes.size());  // API check
  Node<VALUE>* root = get_node(id);
  d_roots.push_back(root);
  if (root->is_inequality())
  {
    d_roots_ineq.insert({root, true});
  }
  if (root->is_not() && (*root)[0]->is_inequality())
  {
    d_roots_ineq.insert({(*root)[0], false});
  }
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
LocalSearch<VALUE>::is_root_node(const Node<VALUE>* node) const
{
  assert(node);
  assert(d_parents.find(node->id()) != d_parents.end());
  return d_parents.at(node->id()).empty();
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

  uint64_t nprops = 0, nupdates = 0;
  Node<VALUE>* cur = root;
  VALUE t   = t_root;

  for (;;)
  {
    uint32_t arity = cur->arity();

    BZLALSLOG(1) << std::endl;
    BZLALSLOG(1) << "  propagate:" << std::endl;
    BZLALSLOG(1) << "    node: " << *cur << (is_root_node(cur) ? " (root)" : "")
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
      BZLALSLOG(1) << "    target value: " << t << std::endl;

      /* Select path */
      uint64_t pos_x = cur->select_path(t);
      assert(pos_x < arity);

      BZLALSLOG(1) << "      select path: node[" << pos_x << "]" << std::endl;
      if (BZLALSLOG_ENABLED(1))
      {
        for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
        {
          BZLALSLOG(1) << "        |- is_essential[" << i
                       << "]: " << (cur->is_essential(t, i) ? "true" : "false")
                       << std::endl;
        }
      }

      /** Select value
       *
       * 1) randomly choose to compute inverse over consistent value
       *    with probability BZLALS_PROB_USE_INV_VALUE
       * 2) if inverse value selected and no inverse value exists,
       *    fall back to consistent value
       * 3) if consistent value selected and no consistent value exists,
       *    conflict
       */

      if (d_rng->pick_with_prob(d_options.prob_pick_inv_value)
          && cur->is_invertible(t, pos_x))
      {
        t = cur->inverse_value(t, pos_x);
        BZLALSLOG(1) << "      inverse value: " << t << std::endl;
        d_statistics.d_nprops_inv += 1;
#ifndef NDEBUG
        d_statistics.d_ninv[cur->kind()] += 1;
#endif
      }
      else if (cur->is_consistent(t, pos_x))
      {
        t = cur->consistent_value(t, pos_x);
        BZLALSLOG(1) << "      consistent value: " << t << std::endl;
        d_statistics.d_nprops_cons += 1;
#ifndef NDEBUG
        d_statistics.d_ncons[cur->kind()] += 1;
#endif
      }
      else
      {
#ifndef NDEBUG
        d_statistics.d_nconf[cur->kind()] += 1;
#endif
        d_statistics.d_nconf_total += 1;
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
  assert(is_root_node(root));

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

  std::vector<uint64_t> cone;
  std::vector<Node<VALUE>*> to_visit;
  std::unordered_set<uint64_t> visited;

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

    if (visited.find(cur->id()) != visited.end()) continue;
    visited.insert(cur->id());
    cone.push_back(cur->id());

    const std::unordered_set<uint64_t>& parents = d_parents.at(cur->id());
    for (uint64_t p : parents)
    {
      to_visit.push_back(get_node(p));
    }
  }

  /* update assignments of cone */
  if (is_root_node(node))
  {
    update_unsat_roots(node);
  }

  std::sort(cone.begin(), cone.end());

  for (uint64_t id : cone)
  {
    Node<VALUE>* cur = get_node(id);
    BZLALSLOG(2) << "  node: " << *cur << " -> ";
    cur->evaluate();
    nupdates += 1;
    BZLALSLOGSTREAM(2) << cur->assignment() << std::endl;
    if (BZLALSLOG_ENABLED(2))
    {
      for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
      {
        BZLALSLOG(2) << "    |- node[" << i << "]: " << *(*cur)[i] << std::endl;
      }
      BZLALSLOG(2) << std::endl;
    }

    if (is_root_node(cur))
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
  BZLALSLOG(1) << "*** move: " << d_statistics.d_nmoves + 1 << std::endl;
  if (BZLALSLOG_ENABLED(1))
  {
    BZLALSLOG(1) << "  unsatisfied roots:" << std::endl;
    for (uint64_t id : d_roots_unsat)
    {
      BZLALSLOG(1) << "    - " << *(get_node(id)) << std::endl;
    }
    BZLALSLOG(1) << "  satisfied roots:" << std::endl;
    for (const Node<VALUE>* r : d_roots)
    {
      if (d_roots_unsat.find(r->id()) != d_roots_unsat.end()) continue;
      BZLALSLOG(1) << "    - " << *r << std::endl;
    }
  }

  if (d_roots_unsat.empty()) return Result::SAT;

  LocalSearchMove<VALUE> m;
  do
  {
    if (d_max_nprops > 0 && d_statistics.d_nprops >= d_max_nprops)
      return Result::UNKNOWN;
    if (d_max_nupdates > 0 && d_statistics.d_nupdates >= d_max_nupdates)
      return Result::UNKNOWN;

    Node<VALUE>* root =
        get_node(d_rng->pick_from_set<std::unordered_set<uint64_t>, uint64_t>(
            d_roots_unsat));

    if (root->is_value_false())
    {
      return Result::UNSAT;
    }

    BZLALSLOG(1) << std::endl;
    BZLALSLOG(1) << "  select constraint: " << *root << std::endl;

    m = select_move(root, *d_true);
    d_statistics.d_nprops += m.d_nprops;
    d_statistics.d_nupdates += m.d_nupdates;
  } while (m.d_input == nullptr);

  assert(!m.d_assignment.is_null());

  BZLALSLOG(1) << std::endl;
  BZLALSLOG(1) << "  move" << std::endl;
  BZLALSLOG(1) << "  input: " << *m.d_input << std::endl;
  BZLALSLOG(1) << "  prev. assignment: " << m.d_input->assignment()
               << std::endl;
  BZLALSLOG(1) << "  new   assignment: " << m.d_assignment << std::endl;
  BZLALSLOG(1) << std::endl;

  d_statistics.d_nmoves += 1;
  d_statistics.d_nupdates += update_cone(m.d_input, m.d_assignment);

  BZLALSLOG(1) << "*** number of propagations: " << d_statistics.d_nprops
               << std::endl;
  BZLALSLOG(1) << std::endl;
  BZLALSLOG(1) << "*** number of updates: " << d_statistics.d_nupdates
               << std::endl;
  BZLALSLOG(1) << std::endl;

  if (d_roots_unsat.empty()) return Result::SAT;
  return Result::UNKNOWN;
}

template class LocalSearch<BitVector>;

/* -------------------------------------------------------------------------- */

}  // namespace ls
}  // namespace bzla
