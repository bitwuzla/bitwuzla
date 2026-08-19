/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bitblast/aig/aig_cnf.h"

#include <cstdlib>
#include <functional>
#include <unordered_set>
#include <vector>

namespace bzla::bitblast {

AigCnfEncoder::AigCnfEncoder(SatInterface& sat_solver)
    : d_sat_solver(sat_solver), d_true_var(0)
{
  // Reserve slot for true, the actual SAT variable is allocated in
  // initialize().
  d_aig_encoded.push_back(0);
}

void
AigCnfEncoder::initialize()
{
  // Allocate SAT variable for true.
  assert(d_true_var == 0);
  d_true_var       = d_sat_solver.new_var();
  d_aig_encoded[0] = d_true_var;
  ++d_statistics.allocated_vars;
}

void
AigCnfEncoder::encode(const AigNode& node, bool top_level, uint32_t level)
{
  if (d_true_var == 0)
  {
    initialize();
  }

  d_sat_solver.set_level(level);
  if (top_level)
  {
    // flatten, thus only add leafs of top-level AIGs
    std::unordered_set<int64_t> cache;
    std::vector<AigNode> visit{node};
    std::vector<AigNode> children;
    do
    {
      AigNode cur = visit.back();
      visit.pop_back();

      auto [it, inserted] = cache.insert(cur.get_id());
      if (!inserted)
      {
        continue;
      }

      if (cur.is_and() && !cur.is_negated())
      {
        visit.push_back(cur[1]);
        visit.push_back(cur[0]);
      }
      else
      {
        children.push_back(cur);
      }
    } while (!visit.empty());
    assert(!children.empty());

    std::vector<AigNode> leafs;
    for (const AigNode& child : children)
    {
      // A top-level leaf that is a negated AND is an asserted (n-ary) OR:
      // encode it directly as a clause instead of introducing a variable for
      // it (and for all AND nodes it is composed of).
      if (child.is_and() && child.is_negated() && is_mergeable(child))
      {
        leafs.clear();
        collect_and(child, leafs, s_max_top_or_size);
        for (const AigNode& leaf : leafs)
        {
          _encode(leaf);
        }
        // leafs of top-level AIGs are associated with the top-most AIG
        for (const AigNode& leaf : leafs)
        {
          d_sat_solver.add(-cnf_lit(leaf), node.get_id());
        }
        d_sat_solver.add(0, node.get_id());
        ++d_statistics.num_clauses;
        d_statistics.num_literals += leafs.size();
        ++d_statistics.num_top_ors;
        // The OR node itself and all AND nodes merged into it do not require
        // a CNF variable.
        d_statistics.num_merged += leafs.size() - 1;
      }
      else
      {
        _encode(child);
        // leafs of top-level AIGs are associated with the top-most AIG
        d_sat_solver.add_clause({cnf_lit(child)}, node.get_id());
        ++d_statistics.num_clauses;
        ++d_statistics.num_literals;
      }
    }
  }
  else
  {
    _encode(node);
  }
}

int32_t
AigCnfEncoder::value(const AigNode& aig)
{
  if (aig.is_true())
  {
    return 1;
  }
  else if (aig.is_false())
  {
    return -1;
  }

  int32_t val;
  if (is_encoded(aig))
  {
    val = d_sat_solver.value(cnf_var(aig)) ? 1 : -1;
  }
  else if (aig.is_and())
  {
    // `aig` has no CNF variable of its own because it was merged into the gate
    // of its parent. Evaluate the AND from its children, which are either
    // encoded or merged themselves; the recursive call applies the negation of
    // a child.
    val = 1;
    std::vector<AigNode> visit{aig};
    do
    {
      AigNode cur = visit.back();
      visit.pop_back();
      for (int i = 0; i < 2; ++i)
      {
        AigNode child = cur[i];
        if (child.is_and() && !child.is_negated() && !is_encoded(child))
        {
          visit.push_back(child);
        }
        else if (value(child) < 0)
        {
          val = -1;
          visit.clear();
          break;
        }
      }
    } while (!visit.empty());
  }
  else
  {
    // An AIG constant that does not occur in any encoded cone is
    // unconstrained, return the default value.
    assert(aig.is_const());
    val = -1;
  }

  return aig.is_negated() ? -val : val;
}

int32_t
AigCnfEncoder::cnf_var(const AigNode& aig) const
{
  assert(is_encoded(aig));
  int64_t id = aig.get_id();
  size_t pos = static_cast<size_t>(std::abs(id) - 1);
  assert(pos < d_aig_encoded.size());
  return std::abs(d_aig_encoded[pos]);
}

int32_t
AigCnfEncoder::cnf_lit(const AigNode& aig) const
{
  assert(is_encoded(aig));
  int32_t var = cnf_var(aig);
  return aig.is_negated() ? -var : var;
}

void
AigCnfEncoder::push()
{
  d_aig_encoded_ids_control.push_back(d_aig_encoded_ids.size());
}

void
AigCnfEncoder::pop()
{
  assert(!d_aig_encoded_ids_control.empty());
  size_t size = d_aig_encoded_ids_control.back();
  d_aig_encoded_ids_control.pop_back();
  while (d_aig_encoded_ids.size() > size)
  {
    size_t pos = d_aig_encoded_ids.back();
    d_aig_encoded_ids.pop_back();
    // Flip back from encoded (<0) to allocated-but-not-encoded (>0).
    d_aig_encoded[pos] *= -1;
    --d_statistics.num_vars;
  }
}

const AigCnfEncoder::Statistics&
AigCnfEncoder::statistics() const
{
  return d_statistics;
}

namespace {

/**
 * Check whether given two-level AIG encodes an ite(c,a,b).
 *
 * @param aig The AIG to check.
 * @param children If not null, the children of ite(c,a,b), added as c,~a,~b.
 *                 Note that a and b have to be negated when encoding the ite
 *                 to CNF since we do not push new negated nodes onto the
 *                 vector, but use the existing ones that occur in `aig`.
 *
 * @return True if given AIG is a if-then-else.
 */
bool
is_ite(const AigNode& aig, std::vector<AigNode>* children = nullptr)
{
  assert(aig.is_and());
  assert(children == nullptr || children->empty());

  const AigNode l = aig[0];
  if (!l.is_negated() || !l.is_and())
  {
    return false;
  }

  const AigNode r = aig[1];
  if (!r.is_negated() || !r.is_and())
  {
    return false;
  }

  // Only extract ITE if both inner AND nodes are local to `aig`.
  if (l.parents() > 1 || r.parents() > 1)
  {
    return false;
  }

  // ite(c,a,b) == (c -> a) /\ (~c -> b)
  // Check all commutative cases of: ~(c /\ ~a) /\ ~(~c /\ ~b)
  //                                   ll   lr       rl    rr
  int64_t ll = l.child_id(0);
  int64_t lr = l.child_id(1);
  int64_t rl = r.child_id(0);
  int64_t rr = r.child_id(1);

  // ~(~b /\ ~c) /\  ~(c /\ ~a)
  if (-lr == rl)
  {
    if (children != nullptr)
    {
      children->push_back(r[0]);  // c
      children->push_back(r[1]);  // ~a
      children->push_back(l[0]);  // ~b
    }
    return true;
  }
  // ~(~c /\ ~b) /\ ~(c /\ ~a)
  if (-ll == rl)
  {
    if (children != nullptr)
    {
      children->push_back(r[0]);  // c
      children->push_back(r[1]);  // ~a
      children->push_back(l[1]);  // ~b
    }
    return true;
  }
  // ~(~b /\ ~c) /\  ~(~a /\ c)
  if (-lr == rr)
  {
    if (children != nullptr)
    {
      children->push_back(r[1]);  // c
      children->push_back(r[0]);  // ~a
      children->push_back(l[0]);  // ~b
    }
    return true;
  }
  // ~(~c /\ ~b) /\  ~(~a /\ c)
  if (-ll == rr)
  {
    if (children != nullptr)
    {
      children->push_back(r[1]);  // c
      children->push_back(r[0]);  // ~a
      children->push_back(l[1]);  // ~b
    }
    return true;
  }

  return false;
}

}  // namespace

bool
AigCnfEncoder::extracts_as_ite(const AigNode& aig,
                               std::vector<AigNode>* children)
{
  assert(aig.is_and());
  // Extraction drops the two inner AND nodes, but only if neither requires a
  // CNF variable.
  return !aig[0].requires_cnf_var() && !aig[1].requires_cnf_var()
         && is_ite(aig, children);
}

bool
AigCnfEncoder::is_mergeable(const AigNode& aig) const
{
  assert(aig.is_and());
  // A node with more than one parent needs a CNF variable for its other
  // parent(s). A node with no parent only gets here as a leaf of a top-level
  // AND, where merging it into the asserted clause is fine.
  if (aig.parents() > 1 || is_encoded(aig) || aig.requires_cnf_var())
  {
    return false;
  }
  // Merging an extracted ite would cost the two variables and 6 clauses of its
  // inner AND nodes instead of one variable and 4 clauses. We need the same
  // check as in _encode(): a node whose extraction is refused because an inner
  // node requires a CNF variable is better merged than kept.
  return !extracts_as_ite(aig, nullptr);
}

void
AigCnfEncoder::collect_and(const AigNode& aig,
                           std::vector<AigNode>& leafs,
                           size_t max_size)
{
  assert(aig.is_and());
  assert(leafs.empty());
  assert(d_visit.empty());

  d_visit.push_back(aig[1]);
  d_visit.push_back(aig[0]);
  do
  {
    AigNode cur = d_visit.back();
    d_visit.pop_back();

    if (cur.is_and() && !cur.is_negated() && is_mergeable(cur)
        && leafs.size() + d_visit.size() < max_size)
    {
      d_visit.push_back(cur[1]);
      d_visit.push_back(cur[0]);
    }
    else
    {
      leafs.push_back(cur);
    }
  } while (!d_visit.empty());
}

void
AigCnfEncoder::_encode(const AigNode& aig)
{
  std::vector<AigNode> visit;
  std::unordered_set<int64_t> cache;
  std::vector<AigNode> children;
  visit.push_back(aig);
  do
  {
    AigNode cur = visit.back();
    if (is_encoded(cur))
    {
      visit.pop_back();
      continue;
    }

    if (!cur.is_and())
    {
      assert(cur.is_const() || cur.is_true() || cur.is_false());
      visit.pop_back();
      set_encoded(cur);

      if (cur.is_true() || cur.is_false())
      {
        d_sat_solver.add_clause({cnf_var(cur)}, std::abs(cur.get_id()));
        ++d_statistics.num_clauses;
        ++d_statistics.num_literals;
      }
    }
    else
    {
      assert(cur.is_and());
      auto [it, inserted] = cache.insert(cur.get_id());

      children.clear();
      bool ite = extracts_as_ite(cur, &children);
      if (!ite)
      {
        children.clear();
        collect_and(cur, children, s_max_and_size);
      }

      if (inserted)
      {
        visit.insert(visit.end(), children.begin(), children.end());
      }
      else
      {
        visit.pop_back();
        set_encoded(cur);

        auto id = std::abs(cur.get_id());
        auto x  = cnf_var(cur);

        if (ite)
        {
          // Encode x <-> ite(c,a,b)
          auto c = cnf_lit(children[0]);   // cond
          auto a = -cnf_lit(children[1]);  // then
          auto b = -cnf_lit(children[2]);  // else

          d_sat_solver.add_clause({-x, -c, a}, id);
          d_sat_solver.add_clause({-x, c, b}, id);
          d_sat_solver.add_clause({x, -c, -a}, id);
          d_sat_solver.add_clause({x, c, -b}, id);
          d_statistics.num_clauses += 4;
          d_statistics.num_literals += 12;
          // xor is the ite variant ite(c,a,~a)
          if (children[1].get_id() == -children[2].get_id())
          {
            ++d_statistics.num_xors;
          }
          else
          {
            ++d_statistics.num_ites;
          }
        }
        else
        {
          // Encode n-ary AND
          //
          // x <-> a1 /\ ... /\ an
          //   --> (~x \/ a1) /\ ... /\ (~x \/ an)
          //    /\ (x \/ ~a1 \/ ... \/ ~an)
          assert(children.size() >= 2);
          for (const AigNode& child : children)
          {
            d_sat_solver.add_clause({-x, cnf_lit(child)}, id);
          }
          d_sat_solver.add(x, id);
          for (const AigNode& child : children)
          {
            d_sat_solver.add(-cnf_lit(child), id);
          }
          d_sat_solver.add(0, id);
          d_statistics.num_clauses += children.size() + 1;
          d_statistics.num_literals += 3 * children.size() + 1;
          // A binary AND is the base case, every additional leaf saves the
          // variable and 2 clauses of one merged AND node.
          d_statistics.num_merged += children.size() - 2;
        }
      }
    }
  } while (!visit.empty());
}

void
AigCnfEncoder::resize(const AigNode& aig)
{
  size_t pos = static_cast<size_t>(std::abs(aig.get_id()) - 1);
  if (pos < d_aig_encoded.size())
  {
    return;
  }
  d_aig_encoded.resize(pos + 1, 0);
}

bool
AigCnfEncoder::is_encoded(const AigNode& aig) const
{
  size_t pos = static_cast<size_t>(std::abs(aig.get_id()) - 1);
  if (pos < d_aig_encoded.size())
  {
    return d_aig_encoded[pos] < 0;
  }
  return false;
}

void
AigCnfEncoder::set_encoded(const AigNode& aig)
{
  resize(aig);
  size_t pos = static_cast<size_t>(std::abs(aig.get_id()) - 1);
  assert(pos < d_aig_encoded.size());
  auto& encoded = d_aig_encoded[pos];
  // No variable allocated in SAT solver yet.
  if (encoded == 0)
  {
    encoded = d_sat_solver.new_var();
    ++d_statistics.allocated_vars;
  }
  // Variable allocated, but not yet encoded.
  assert(encoded > 0);
  encoded *= -1;
  ++d_statistics.num_vars;
  if (!d_aig_encoded_ids_control.empty())
  {
    d_aig_encoded_ids.push_back(pos);
  }
}

}  // namespace bzla::bitblast
