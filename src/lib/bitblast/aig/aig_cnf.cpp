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

void
AigCnfEncoder::encode(const AigNode& node, bool top_level)
{
  if (top_level)
  {
    std::unordered_set<int64_t> cache;
    std::vector<std::reference_wrapper<const AigNode>> visit{node};
    std::vector<std::reference_wrapper<const AigNode>> children;
    do
    {
      const AigNode& cur = visit.back();
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
        _encode(cur);
      }
    } while (!visit.empty());
    assert(!children.empty());

    for (const AigNode& child : children)
    {
      d_sat_solver.add_clause({child.get_id()});
      ++d_statistics.num_clauses;
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

  int32_t val = -1;
  if (is_encoded(aig))
  {
    val = d_sat_solver.value(std::abs(aig.get_id())) ? 1 : -1;
  }

  return aig.is_negated() ? -val : val;
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
 * @param children The children of ite(c,a,b), added as c,~a,~b. Note that a
 *                 and b have to be negated when encoding the ite to CNF since
 *                 we do not push new negated nodes onto the vector, but use
 *                 the existing ones that occur in `aig`.
 *
 * @return True if given AIG is a if-then-else.
 */
bool
is_ite(const AigNode& aig, std::vector<const AigNode*>& children)
{
  assert(aig.is_and());
  assert(children.empty());

  const auto& l = aig[0];
  if (!l.is_negated() || !l.is_and())
  {
    return false;
  }

  // Do not extract ITE if it destroys sharing
  if (l.parents() > 1)
  {
    return false;
  }

  const auto& r = aig[1];
  if (!r.is_negated() || !r.is_and())
  {
    return false;
  }

  // Do not extract ITE if it destroys sharing
  if (r.parents() > 1)
  {
    return false;
  }

  // ite(c,a,b) == (c -> a) /\ (~c -> b)
  // Check all commutative cases of: ~(c /\ ~a) /\ ~(~c /\ ~b)
  //                                   ll   lr       rl    rr
  const auto& ll = l[0];
  const auto& lr = l[1];
  const auto& rl = r[0];
  const auto& rr = r[1];

  // ~(~b /\ ~c) /\  ~(c /\ ~a)
  if (-lr.get_id() == rl.get_id())
  {
    children.push_back(&rl);  // c
    children.push_back(&rr);  // ~a
    children.push_back(&ll);  // ~b
    return true;
  }
  // ~(~c /\ ~b) /\ ~(c /\ ~a)
  if (-ll.get_id() == rl.get_id())
  {
    children.push_back(&rl);  // c
    children.push_back(&rr);  // ~a
    children.push_back(&lr);  // ~b
    return true;
  }
  // ~(~b /\ ~c) /\  ~(~a /\ c)
  if (-lr.get_id() == rr.get_id())
  {
    children.push_back(&rr);  // c
    children.push_back(&rl);  // ~a
    children.push_back(&ll);  // ~b
    return true;
  }
  // ~(~c /\ ~b) /\  ~(~a /\ c)
  if (-ll.get_id() == rr.get_id())
  {
    children.push_back(&rr);  // c
    children.push_back(&rl);  // ~a
    children.push_back(&lr);  // ~b
    return true;
  }

  return false;
}

}  // namespace

void
AigCnfEncoder::_encode(const AigNode& aig)
{
  std::vector<const AigNode*> visit;
  std::unordered_set<const AigNode*> cache;
  visit.push_back(&aig);
  do
  {
    auto cur = visit.back();
    resize(*cur);

    if (is_encoded(*cur))
    {
      visit.pop_back();
      continue;
    }

    if (cur->is_true() || cur->is_false() || cur->is_const())
    {
      visit.pop_back();
      set_encoded(*cur);
      if (cur->is_true() || cur->is_false())
      {
        d_sat_solver.add_clause({std::abs(cur->get_id())});
        ++d_statistics.num_clauses;
        ++d_statistics.num_literals;
      }
    }
    else
    {
      assert(cur->is_and());

      auto [it, inserted] = cache.insert(cur);

      std::vector<const AigNode*> children;
      bool ite = is_ite(*cur, children);

      if (inserted)
      {
        if (ite)
        {
          visit.insert(visit.end(), children.begin(), children.end());
        }
        else
        {
          visit.push_back(&(*cur)[0]);
          visit.push_back(&(*cur)[1]);
        }
      }
      else
      {
        visit.pop_back();
        set_encoded(*cur);

        // TODO: and optimization: collect all children and encode one big and
        // TODO: xor optimization: use native xor encoding

        if (ite)
        {
          // Encode x <-> ite(c,a,b)
          auto x = std::abs(cur->get_id());
          auto c = children[0]->get_id();   // cond
          auto a = -children[1]->get_id();  // then
          auto b = -children[2]->get_id();  // else

          d_sat_solver.add_clause({-x, -c, a});
          d_sat_solver.add_clause({-x, c, b});
          d_sat_solver.add_clause({x, -c, -a});
          d_sat_solver.add_clause({x, c, -b});
          d_statistics.num_clauses += 4;
          d_statistics.num_literals += 12;
        }
        else
        {
          // Encode binary AND
          //
          // x <-> a /\ b --> (~x \/ a) /\ (~x \/ b) /\ (x \/ ~a \/ ~b)

          auto x = std::abs(cur->get_id());
          auto a = (*cur)[0].get_id();
          auto b = (*cur)[1].get_id();

          d_sat_solver.add_clause({-x, a});
          d_sat_solver.add_clause({-x, b});
          d_sat_solver.add_clause({x, -a, -b});
          d_statistics.num_clauses += 3;
          d_statistics.num_literals += 7;
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
  d_aig_encoded.resize(pos + 1, false);
}

bool
AigCnfEncoder::is_encoded(const AigNode& aig) const
{
  size_t pos = static_cast<size_t>(std::abs(aig.get_id()) - 1);
  if (pos < d_aig_encoded.size())
  {
    return d_aig_encoded[pos];
  }
  return false;
}

void
AigCnfEncoder::set_encoded(const AigNode& aig)
{
  size_t pos = static_cast<size_t>(std::abs(aig.get_id()) - 1);
  assert(pos < d_aig_encoded.size());
  d_aig_encoded[pos] = true;
  ++d_statistics.num_vars;
}
}  // namespace bzla::bitblast
