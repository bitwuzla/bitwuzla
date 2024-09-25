/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/elim_udiv.h"

#include <vector>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

namespace bzla::preprocess::pass {

using namespace node;

PassElimUdiv::PassElimUdiv(Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "eud", "elim_udiv"),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

void
PassElimUdiv::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    Node assertion = assertions[i];
    if (!processed(assertion))
    {
      cache_assertion(assertion);
      Node processed = process(assertion);
      assertions.replace(i, processed);
    }
  }
}

Node
PassElimUdiv::process(const Node& assertion)
{
  node::node_ref_vector visit{assertion};

  NodeManager& nm = d_env.nm();
  std::vector<Node> new_assertions;
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = d_cache.emplace(cur, Node());
    if (inserted)
    {
      if (cur.kind() == Kind::FORALL || cur.kind() == Kind::EXISTS)
      {
        it->second = cur;
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      std::vector<Node> children;
      for (const Node& child : cur)
      {
        auto iit = d_cache.find(child);
        assert(iit != d_cache.end());
        children.push_back(iit->second);
      }
      if (cur.kind() == Kind::BV_UDIV || cur.kind() == Kind::BV_UREM)
      {
        const Node& a = children[0];
        const Node& b = children[1];
        const Node& q = quotient(cur);
        const Node& r = remainder(cur);

        Node zero = nm.mk_value(BitVector::mk_zero(q.type().bv_size()));
        Node ones = nm.mk_value(BitVector::mk_ones(q.type().bv_size()));

        Node b_dis_zero = nm.mk_node(Kind::DISTINCT, {b, zero});
        Node b_eq_zero  = nm.mk_node(Kind::EQUAL, {b, zero});
        Node q_mul_b    = nm.mk_node(Kind::BV_MUL, {q, b});
        Node qb_add_r   = nm.mk_node(Kind::BV_ADD, {q_mul_b, r});
        new_assertions.push_back(
            nm.mk_node(Kind::IMPLIES,
                       {b_dis_zero, nm.mk_node(Kind::EQUAL, {qb_add_r, a})}));
        new_assertions.push_back(nm.mk_node(
            Kind::IMPLIES, {b_dis_zero, nm.mk_node(Kind::BV_ULT, {r, b})}));
        new_assertions.push_back(nm.mk_node(
            Kind::IMPLIES, {b_eq_zero, nm.mk_node(Kind::EQUAL, {q, ones})}));
        new_assertions.push_back(nm.mk_node(
            Kind::IMPLIES, {b_eq_zero, nm.mk_node(Kind::EQUAL, {r, a})}));
        new_assertions.push_back(
            nm.mk_node(Kind::NOT, {nm.mk_node(Kind::BV_UMULO, {q, b})}));
        new_assertions.push_back(
            nm.mk_node(Kind::NOT, {nm.mk_node(Kind::BV_UADDO, {q_mul_b, r})}));

        if (cur.kind() == Kind::BV_UDIV)
        {
          it->second = q;
        }
        else
        {
          it->second = r;
        }
      }
      else
      {
        it->second = utils::rebuild_node(nm, cur, children);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  auto it = d_cache.find(assertion);
  assert(it != d_cache.end());
  if (!new_assertions.empty())
  {
    new_assertions.push_back(it->second);
    it->second = utils::mk_nary(nm, Kind::AND, new_assertions);
  }

  return it->second;
}

const Node&
PassElimUdiv::quotient(const Node& node)
{
  assert(node.kind() == Kind::BV_UDIV || node.kind() == Kind::BV_UREM);
  NodeManager& nm = d_env.nm();

  Node lookup = nm.mk_node(Kind::BV_UDIV, {node[0], node[1]});
  auto it     = d_quot_cache.find(lookup);
  if (it == d_quot_cache.end())
  {
    auto [iit, inserted] =
        d_quot_cache.emplace(lookup, nm.mk_const(lookup.type()));
    return iit->second;
  }
  return it->second;
}

const Node&
PassElimUdiv::remainder(const Node& node)
{
  assert(node.kind() == Kind::BV_UDIV || node.kind() == Kind::BV_UREM);
  NodeManager& nm = d_env.nm();

  Node lookup = nm.mk_node(Kind::BV_UREM, {node[0], node[1]});
  auto it     = d_rem_cache.find(lookup);
  if (it == d_rem_cache.end())
  {
    auto [iit, inserted] =
        d_rem_cache.emplace(lookup, nm.mk_const(lookup.type()));
    return iit->second;
  }
  return it->second;
}

PassElimUdiv::Statistics::Statistics(util::Statistics& stats,
                                     const std::string& prefix)
    : num_eliminated(stats.new_stat<uint64_t>(prefix + "num_eliminated"))
{
}

}  // namespace bzla::preprocess::pass
