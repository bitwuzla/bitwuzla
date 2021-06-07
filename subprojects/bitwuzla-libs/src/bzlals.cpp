#include "bzlals.h"

#include <algorithm>
#include <cassert>
#include <iostream>

#include "bitvector.h"
#include "bitvector_node.h"
#include "rng.h"

#define BZLALS_PROB_USE_INV_VALUE 990

namespace bzlals {

/* -------------------------------------------------------------------------- */

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream& ostream) { (void) ostream; }
};

#define BZLALSLOG_ENABLED (d_log_level != 0)
#define BZLALSLOG !(BZLALSLOG_ENABLED) ? (void) 0 : OstreamVoider() & std::cout

/* -------------------------------------------------------------------------- */

struct BzlaLsMove
{
  BzlaLsMove() : d_nprops(0), d_nupdates(0), d_input(nullptr) {}

  BzlaLsMove(uint64_t nprops,
             uint64_t nupdates,
             BitVectorNode* input,
             BitVector assignment)
      : d_nprops(nprops),
        d_nupdates(nupdates),
        d_input(input),
        d_assignment(assignment)
  {
  }

  uint64_t d_nprops;
  uint64_t d_nupdates;
  BitVectorNode* d_input;
  BitVector d_assignment;
};

/* -------------------------------------------------------------------------- */

BzlaLs::BzlaLs(uint64_t max_nprops, uint64_t max_nupdates, uint32_t seed)
    : d_max_nprops(max_nprops), d_max_nupdates(max_nupdates), d_seed(seed)
{
  d_rng.reset(new RNG(d_seed));
  d_one.reset(new BitVector(BitVector::mk_one(1)));
}

BzlaLs::~BzlaLs() {}

uint32_t
BzlaLs::mk_node(uint32_t size)
{
  return mk_node(BitVector::mk_zero(size), BitVectorDomain(size));
}

uint32_t
BzlaLs::mk_node(OperatorKind kind,
                uint32_t size,
                const std::vector<uint32_t>& children)
{
  return mk_node(kind, BitVectorDomain(size), children);
}

uint32_t
BzlaLs::mk_indexed_node(OperatorKind kind,
                        uint32_t size,
                        uint32_t child0,
                        const std::vector<uint32_t>& indices)
{
  return mk_indexed_node(kind, BitVectorDomain(size), child0, indices);
}

uint32_t
BzlaLs::mk_node(const BitVector& assignment, const BitVectorDomain& domain)
{
  uint32_t id = d_nodes.size();
  assert(assignment.size() == domain.size());  // API check
  std::unique_ptr<BitVectorNode> res(
      new BitVectorNode(d_rng.get(), assignment, domain));
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

uint32_t
BzlaLs::mk_node(OperatorKind kind,
                const BitVectorDomain& domain,
                const std::vector<uint32_t>& children)
{
  uint32_t id = d_nodes.size();
  for (uint32_t c : children)
  {
    assert(c < id);  // API check
    assert(d_parents.find(c) != d_parents.end());
    assert(d_parents.at(c).find(id) == d_parents.at(c).end());
    d_parents.at(c).insert(id);
  }

  std::unique_ptr<BitVectorNode> res;

  switch (kind)
  {
    case ADD:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAdd(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;

    case AND:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAnd(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;
    case ASHR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorAshr(d_rng.get(),
                                  domain,
                                  get_node(children[0]),
                                  get_node(children[1])));
      break;
    case CONCAT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorConcat(d_rng.get(),
                                    domain,
                                    get_node(children[0]),
                                    get_node(children[1])));
      break;
    case EQ:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorEq(d_rng.get(),
                                domain,
                                get_node(children[0]),
                                get_node(children[1])));
      break;
    case ITE:
      assert(children.size() == 3);  // API check
      res.reset(new BitVectorIte(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1]),
                                 get_node(children[2])));
      break;
    case MUL:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorMul(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;
    case NOT:
      assert(children.size() == 1);  // API check
      res.reset(new BitVectorNot(d_rng.get(), domain, get_node(children[0])));
      break;
    case SHL:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorShl(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;
    case SHR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorShr(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;
    case SLT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorSlt(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;
    case UDIV:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUdiv(d_rng.get(),
                                  domain,
                                  get_node(children[0]),
                                  get_node(children[1])));
      break;
    case ULT:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUlt(
          d_rng.get(), domain, get_node(children[0]), get_node(children[1])));
      break;
    case UREM:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorUrem(d_rng.get(),
                                  domain,
                                  get_node(children[0]),
                                  get_node(children[1])));
      break;
    case XOR:
      assert(children.size() == 2);  // API check
      res.reset(new BitVectorXor(d_rng.get(),
                                 domain,
                                 get_node(children[0]),
                                 get_node(children[1])));
      break;

    default: assert(0);  // API check
  }
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};

  return id;
}

uint32_t
BzlaLs::mk_indexed_node(OperatorKind kind,
                        const BitVectorDomain& domain,
                        uint32_t child0,
                        const std::vector<uint32_t>& indices)
{
  assert(kind == EXTRACT || kind == SEXT);              // API check
  assert(kind != EXTRACT || indices.size() == 2);       // API check
  assert(kind != EXTRACT || indices[0] >= indices[1]);  // API check
  assert(kind != EXTRACT
         || indices[0] < get_node(child0)->size());  // API check
  assert(kind != SEXT || indices.size() == 1);       // API check

  uint32_t id = d_nodes.size();
  assert(child0 < id);

  assert(d_parents.find(child0) != d_parents.end());
  assert(d_parents.at(child0).find(id) == d_parents.at(child0).end());
  d_parents.at(child0).insert(id);

  std::unique_ptr<BitVectorNode> res;
  if (kind == EXTRACT)
  {
    res.reset(new BitVectorExtract(d_rng.get(),
                                   domain,
                                   get_node(child0),
                                   indices[0],
                                   indices[1]));
  }
  else
  {
    res.reset(new BitVectorSignExtend(
        d_rng.get(), domain, get_node(child0), indices[0]));
  }
  res->set_id(id);
  d_nodes.push_back(std::move(res));
  assert(get_node(id) == d_nodes.back().get());
  assert(d_parents.find(id) == d_parents.end());
  d_parents[id] = {};
  return id;
}

uint32_t
BzlaLs::invert_node(uint32_t id)
{
  assert(id < d_nodes.size());  // API check
  return mk_node(NOT, get_node(id)->domain().bvnot(), {id});
}

const BitVector&
BzlaLs::get_assignment(uint32_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->assignment();
}

const BitVectorDomain&
BzlaLs::get_domain(uint32_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->domain();
}

void
BzlaLs::set_assignment(uint32_t id, const BitVector& assignment)
{
  assert(id < d_nodes.size());  // API check
  get_node(id)->set_assignment(assignment);
}

void
BzlaLs::fix_bit(uint32_t id, uint32_t idx, bool value)
{
  assert(id < d_nodes.size());  // API check
  BitVectorNode* node = get_node(id);
  assert(idx < node->domain().size());  // API check
  node->fix_bit(idx, value);
}

void
BzlaLs::register_root(uint32_t root)
{
  assert(root < d_nodes.size());  // API check
  d_roots.insert(root);
  update_roots(root);
}

uint32_t
BzlaLs::get_arity(uint32_t id) const
{
  assert(id < d_nodes.size());  // API check
  return get_node(id)->arity();
}

uint32_t
BzlaLs::get_child(uint32_t id, uint32_t idx) const
{
  assert(id < d_nodes.size());  // API check
  assert(idx < get_arity(id));  // API check
  return (*get_node(id))[idx]->id();
}

/* -------------------------------------------------------------------------- */

BitVectorNode*
BzlaLs::get_node(uint32_t id) const
{
  assert(id < d_nodes.size());
  assert(d_nodes[id]->id() == id);
  return d_nodes[id].get();
}

bool
BzlaLs::is_leaf_node(const BitVectorNode* node) const
{
  assert(node);
  return node->arity() == 0;
}

bool
BzlaLs::is_root_node(const BitVectorNode* node) const
{
  assert(node);
  assert(d_parents.find(node->id()) != d_parents.end());
  return d_parents.at(node->id()).empty();
}

BzlaLsMove
BzlaLs::select_move(BitVectorNode* root, const BitVector& t_root)
{
  assert(root);

  uint64_t nprops = 0, nupdates = 0;
  BitVectorNode* cur = root;
  BitVector t        = t_root;

  for (;;)
  {
    uint32_t arity = cur->arity();

    BZLALSLOG << std::endl << "  propagate: " << std::endl;
    BZLALSLOG << "    node: " << *cur << std::endl;
    if (BZLALSLOG_ENABLED)
    {
      for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
      {
        BZLALSLOG << "      |- node[" << i << "]: " << *(*cur)[i] << std::endl;
      }
    }
    BZLALSLOG << "    target value: " << t << std::endl;

    if (arity == 0)
    {
      return BzlaLsMove(nprops, nupdates, cur, t);
    }
    else if (cur->is_const() || cur->all_const())
    {
      break;
    }
    else
    {
      assert(!cur->domain().is_fixed());

      /* Select path */
      uint32_t pos_x = cur->select_path(t);
      assert(pos_x < arity);

      BZLALSLOG << "      select path: node[" << pos_x << "]" << std::endl;
      if (BZLALSLOG_ENABLED)
      {
        for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
        {
          BZLALSLOG << "        |- is_essential[" << i
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

      if (d_rng->pick_with_prob(BZLALS_PROB_USE_INV_VALUE)
          && cur->is_invertible(t, pos_x))
      {
        t = cur->inverse_value(t, pos_x);
        BZLALSLOG << "      inverse value: " << t << std::endl;
      }
      else if (cur->is_consistent(t, pos_x))
      {
        t = cur->consistent_value(t, pos_x);
        BZLALSLOG << "      consistent value: " << t << std::endl;
      }
      else
      {
        break;
      }

      // TODO skip when no progress?

      /* Propagate down */
      cur = (*cur)[pos_x];
      nprops += 1;
    }
  }
  /* Conflict case */
  return BzlaLsMove(nprops, nupdates, nullptr, BitVector());
}

void
BzlaLs::update_roots(uint32_t id)
{
  assert(id < d_nodes.size());

  auto it = d_roots.find(id);
  if (it != d_roots.end())
  {
    if (get_node(id)->assignment().is_true())
    {
      d_roots.erase(it);
    }
  }
  else if (get_node(id)->assignment().is_false())
  {
    d_roots.insert(id);
  }
}

uint64_t
BzlaLs::update_cone(BitVectorNode* node, const BitVector& assignment)
{
  assert(node);
  assert(is_leaf_node(node));

  BZLALSLOG << "*** update cone: " << *node << " with: " << assignment
            << std::endl << std::endl;
#ifndef NDEBUG
  for (uint32_t r : d_roots)
  {
    assert(get_node(r)->assignment().is_false());
  }
#endif

  /* nothing to do if node already has given assignment */
  if (node->assignment().compare(assignment) == 0) return 0;

  /* update assignment of given node */
  node->set_assignment(assignment);
  uint64_t nupdates = 1;

  std::vector<uint32_t> cone;
  std::vector<BitVectorNode*> to_visit;
  std::unordered_set<uint32_t> visited;

  /* reset cone */
  const std::unordered_set<uint32_t>& parents = d_parents.at(node->id());
  for (uint32_t p : parents)
  {
    to_visit.push_back(get_node(p));
  }

  while (!to_visit.empty())
  {
    BitVectorNode* cur = to_visit.back();
    to_visit.pop_back();

    if (visited.find(cur->id()) != visited.end()) continue;
    visited.insert(cur->id());
    cone.push_back(cur->id());

    const std::unordered_set<uint32_t>& parents = d_parents.at(cur->id());
    for (uint32_t p : parents)
    {
      to_visit.push_back(get_node(p));
    }
  }

  /* update assignments of cone */
  if (is_root_node(node))
  {
    update_roots(node->id());
  }

  std::sort(cone.begin(), cone.end());

  for (uint32_t id : cone)
  {
    BitVectorNode* cur = get_node(id);
    BZLALSLOG << "  node: " << *cur << " -> ";
    cur->evaluate();
    nupdates += 1;
    BZLALSLOG << cur->assignment() << std::endl;
    if (BZLALSLOG_ENABLED)
    {
      for (uint32_t i = 0, n = cur->arity(); i < n; ++i)
      {
        BZLALSLOG << "    |- node[" << i << "]: " << *(*cur)[i] << std::endl;
      }
      BZLALSLOG << std::endl;
    }

    if (is_root_node(cur))
    {
      update_roots(cur->id());
    }
  }
#ifndef NDEBUG
  for (uint32_t r : d_roots)
  {
    assert(get_node(r)->assignment().is_false());
  }
#endif
  return nupdates;
}

BzlaLs::Result
BzlaLs::move()
{
  BZLALSLOG << "*** move: " << d_nmoves + 1 << std::endl;
  BZLALSLOG << "  unsatisfied roots: " << std::endl;
  if (BZLALSLOG_ENABLED)
  {
    for (const auto& r : d_roots) BZLALSLOG << "    - " << *get_node(r);
    BZLALSLOG << std::endl;
  }

  if (d_roots.empty()) return SAT;

  BzlaLsMove m;
  do
  {
    if (d_max_nprops > 0 && d_nprops >= d_max_nprops) return UNKNOWN;
    if (d_max_nupdates > 0 && d_nupdates >= d_max_nupdates) return UNKNOWN;

    BitVectorNode* root = get_node(
        d_rng->pick_from_set<std::unordered_set<uint32_t>, uint32_t>(d_roots));

    if (root->is_const() && root->assignment().is_false()) return UNSAT;

    BZLALSLOG << std::endl << "  select constraint: " << *root << std::endl;

    m = select_move(root, *d_one);
    d_nprops += m.d_nprops;
    d_nupdates += m.d_nupdates;
  } while (m.d_input == nullptr);

  assert(!m.d_assignment.is_null());

  BZLALSLOG << std::endl << "  move" << std::endl;
  BZLALSLOG << "  input: " << *m.d_input << std::endl;
  BZLALSLOG << "  prev. assignment: " << m.d_input->assignment() << std::endl;
  BZLALSLOG << "  new   assignment: " << m.d_assignment << std::endl;
  BZLALSLOG << std::endl;

  d_nmoves += 1;
  d_nupdates += update_cone(m.d_input, m.d_assignment);

  BZLALSLOG << "*** number of propagations: " << d_nprops << std::endl;
  BZLALSLOG << std::endl;
  BZLALSLOG << "*** number of updates: " << d_nupdates << std::endl;
  BZLALSLOG << std::endl;

  if (d_roots.empty()) return SAT;
  return BzlaLs::UNKNOWN;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzlals
