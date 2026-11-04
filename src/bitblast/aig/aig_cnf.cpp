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

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <span>
#include <unordered_set>
#include <vector>

namespace bzla::bitblast {

AigCnfEncoder::AigCnfEncoder(SatInterface& sat_solver, LevelMode mode)
    : d_mode(mode), d_sat_solver(sat_solver), d_true_var(0)
{
  // Reserve slot for true, the actual SAT variable is allocated in
  // initialize().
  d_aig_encoded.push_back(0);
}

void
AigCnfEncoder::initialize()
{
  // Allocate SAT variable for true, set_encoded() assigns it to true.
  assert(d_true_var == 0);
  d_true_var = d_sat_solver.new_var();
  ++d_statistics.allocated_vars;
}

void
AigCnfEncoder::encode(const AigNode& node, bool top_level, uint32_t level)
{
  if (d_true_var == 0)
  {
    initialize();
  }

  size_t size = static_cast<size_t>(std::abs(node.get_id()));
  if (size > d_expanded.size())
  {
    d_expanded.resize(size, false);
  }

  d_level = level;
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
        uint32_t clause_level = level;
        for (const AigNode& leaf : leafs)
        {
          _encode(leaf);
          clause_level = std::max(clause_level, this->level(leaf));
        }
        d_sat_solver.set_level(clause_level);
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
        d_sat_solver.set_level(std::max(level, this->level(child)));
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
  size_t pos = aig_pos(aig);
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
  d_levels.emplace_back();
}

void
AigCnfEncoder::pop()
{
  assert(!d_levels.empty());
  const Level& top = d_levels.back();
  for (size_t pos : top.ids)
  {
    // Flip back from encoded (<0) to allocated-but-not-encoded (>0).
    d_aig_encoded[pos] *= -1;
    --d_statistics.num_vars;
    ++d_statistics.pop.num_reset_aigs;
  }
  update_reuse(top.candidates);
  d_levels.pop_back();
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
      // A reuse candidate merged into the gate of `aig` is needed again.
      reuse_pending(cur);
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
  std::vector<AigNode> leafs;
  // The children of the expanded nodes, one segment per node. Nodes are encoded
  // in reverse order of expansion, hence the segment of the node to encode is
  // always on top.
  std::vector<AigNode> pending;
  std::vector<std::pair<size_t, bool>> segments;  // (start in pending, is ite)
  visit.push_back(aig);
  do
  {
    AigNode cur = visit.back();
    if (is_encoded(cur))
    {
      if (!d_pending.empty())
      {
        mark_reused(cur);
      }
      visit.pop_back();
      continue;
    }

    if (!cur.is_and())
    {
      assert(cur.is_const() || cur.is_true() || cur.is_false());
      visit.pop_back();

      if (cur.is_true() || cur.is_false())
      {
        uint32_t level = d_mode == LevelMode::ASSERTION ? d_level : 0;
        bool reencoded = set_encoded(cur, level);
        d_sat_solver.set_level(level);
        d_sat_solver.add_clause({cnf_var(cur)}, std::abs(cur.get_id()));
        ++d_statistics.num_clauses;
        ++d_statistics.num_literals;
        if (reencoded)
        {
          ++d_statistics.pop.num_reencoded_clauses;
        }
      }
      else
      {
        set_encoded(cur, input_level(cur));
      }
    }
    else
    {
      assert(cur.is_and());
      size_t pos = aig_pos(cur);
      assert(pos < d_expanded.size());
      if (!d_expanded[pos])
      {
        d_expanded[pos] = true;
        leafs.clear();
        bool ite = extracts_as_ite(cur, &leafs);
        if (!ite)
        {
          leafs.clear();
          collect_and(cur, leafs, s_max_and_size);
        }
        segments.emplace_back(pending.size(), ite);
        pending.insert(pending.end(), leafs.begin(), leafs.end());
        visit.insert(visit.end(), leafs.begin(), leafs.end());
      }
      else
      {
        d_expanded[pos] = false;
        visit.pop_back();

        auto [start, ite] = segments.back();
        segments.pop_back();
        std::span<const AigNode> children(pending.begin() + start,
                                          pending.end());

        uint32_t level = 0;
        if (d_mode == LevelMode::ASSERTION)
        {
          level = d_level;
        }
        // ADAPTIVE: without pushed levels, all levels are 0.
        else if (d_mode == LevelMode::ADAPTIVE && !d_levels.empty())
        {
          for (const AigNode& child : children)
          {
            level = std::max(level, this->level(child));
          }
          // A node required by an assertion of a pushed level over inputs of
          // lower levels may be needed again after the pop. Unless this is
          // expected, it takes the assertion level. Lemmas are encoded at
          // level 0 and are not considered.
          if (level < d_level)
          {
            d_levels.back().candidates.push_back(pos);
            ++d_statistics.adaptive.num_candidates;
            if (reuse_expected())
            {
              ++d_statistics.adaptive.num_candidates_kept;
            }
            else
            {
              level = d_level;
              ++d_statistics.adaptive.num_candidates_at_assertion_level;
            }
          }
        }
        bool reencoded = set_encoded(cur, level);
        d_sat_solver.set_level(level);
        uint64_t num_clauses = d_statistics.num_clauses;

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
        if (reencoded)
        {
          d_statistics.pop.num_reencoded_clauses +=
              d_statistics.num_clauses - num_clauses;
        }
        pending.resize(start);
      }
    }
  } while (!visit.empty());
  assert(pending.empty() && segments.empty());
}

uint32_t
AigCnfEncoder::level(const AigNode& aig) const
{
  assert(is_encoded(aig));
  size_t pos = aig_pos(aig);
  return pos < d_aig_level.size() ? d_aig_level[pos] : 0;
}

uint32_t
AigCnfEncoder::input_level(const AigNode& aig) const
{
  assert(aig.is_const());
  // Without pushed levels, all levels are 0.
  if (d_mode != LevelMode::ADAPTIVE || d_levels.empty())
  {
    return 0;
  }
  uint32_t level = d_input_level ? d_input_level(aig) : 0;
  // Inputs of levels that have no clauses yet are encoded at the current one.
  return std::min(level, static_cast<uint32_t>(d_levels.size()));
}

void
AigCnfEncoder::mark_reused(const AigNode& aig)
{
  assert(d_mode == LevelMode::ADAPTIVE);
  if (!reuse_pending(aig))
  {
    return;
  }
  // Clear the pending candidates, which are AND nodes, in the cone of `aig`.
  // The cone of an encoded node consists of encoded nodes and AND nodes merged
  // into their parent's gate, which are not encoded themselves.
  std::vector<AigNode> visit{aig[0], aig[1]};
  do
  {
    AigNode cur = visit.back();
    visit.pop_back();
    if (reuse_pending(cur) || (cur.is_and() && !is_encoded(cur)))
    {
      assert(cur.is_and());
      visit.push_back(cur[0]);
      visit.push_back(cur[1]);
    }
  } while (!visit.empty());
}

bool
AigCnfEncoder::reuse_pending(const AigNode& aig)
{
  size_t pos = aig_pos(aig);
  if (pos >= d_pending.size() || !d_pending[pos])
  {
    return false;
  }
  d_pending[pos] = false;
  ++d_num_reused_since;
  ++d_statistics.adaptive.num_candidates_needed_again;
  return true;
}

void
AigCnfEncoder::update_reuse(const std::vector<size_t>& candidates)
{
  assert(d_mode == LevelMode::ADAPTIVE || candidates.empty());
  uint64_t num_new = 0;
  for (size_t pos : candidates)
  {
    if (pos >= d_pending.size())
    {
      d_pending.resize(d_aig_encoded.size(), false);
    }
    if (!d_pending[pos])
    {
      d_pending[pos] = true;
      ++num_new;
    }
  }
  // The candidates of a popped level are needed again (if at all) before the
  // candidates of the next popped level, close the current window.
  if (num_new > 0)
  {
    if (d_num_pending_last > 0)
    {
      double reused = std::min(
          1.0, static_cast<double>(d_num_reused_since) / d_num_pending_last);
      d_reuse = (d_reuse + reused) / 2;
    }
    d_num_pending_last = num_new;
    d_num_reused_since = 0;
  }
}

void
AigCnfEncoder::resize(const AigNode& aig)
{
  size_t pos = aig_pos(aig);
  if (pos < d_aig_encoded.size())
  {
    return;
  }
  d_aig_encoded.resize(pos + 1, 0);
}

bool
AigCnfEncoder::is_encoded(const AigNode& aig) const
{
  size_t pos = aig_pos(aig);
  if (pos < d_aig_encoded.size())
  {
    return d_aig_encoded[pos] < 0;
  }
  return false;
}

bool
AigCnfEncoder::set_encoded(const AigNode& aig, uint32_t level)
{
  resize(aig);
  size_t pos = aig_pos(aig);
  assert(pos < d_aig_encoded.size());
  auto& encoded  = d_aig_encoded[pos];
  bool reencoded = encoded != 0;
  // No variable allocated in SAT solver yet.
  if (encoded == 0)
  {
    if (pos == 0)
    {
      encoded = d_true_var;
    }
    else
    {
      encoded = d_sat_solver.new_var();
      ++d_statistics.allocated_vars;
    }
  }
  else
  {
    ++d_statistics.pop.num_reencoded_aigs;
  }
  // Variable allocated, but not yet encoded.
  assert(encoded > 0);
  encoded *= -1;
  ++d_statistics.num_vars;

  if (d_mode == LevelMode::ASSERTION)
  {
    // All AIGs encoded while a level is pushed are reset on its pop, including
    // AIGs of lemmas encoded at a lower level.
    if (!d_levels.empty())
    {
      d_levels.back().ids.push_back(pos);
    }
  }
  else if (d_mode == LevelMode::ADAPTIVE)
  {
    assert(level <= d_levels.size());
    if (level > 0)
    {
      if (pos >= d_aig_level.size())
      {
        d_aig_level.resize(d_aig_encoded.size(), 0);
      }
      d_levels[level - 1].ids.push_back(pos);
    }
    // AIGs beyond the end of d_aig_level have level 0.
    if (pos < d_aig_level.size())
    {
      d_aig_level[pos] = level;
    }
    reuse_pending(aig);
  }
  return reencoded;
}

}  // namespace bzla::bitblast
