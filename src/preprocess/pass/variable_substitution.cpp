/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/variable_substitution.h"

#include "bv/bitvector.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

using namespace node;

namespace {
/**
 * Can we rewrite `node` as `factor * lhs + rhs` where `lhs` is a constant
 * and `factor` is odd? We check whether this is possible with at most `bound`
 * recursive calls.
 */
bool
get_linear_bv_term_aux(NodeManager& nm,
                       const Node& node,
                       BitVector& factor,
                       Node& lhs,
                       Node& rhs,
                       uint32_t& bound)
{
  assert(node.type().is_bv());

  if (bound == 0)
  {
    return false;
  }

  bound -= 1;

  if (node.is_inverted())
  {
    // node = ~subterm
    //      = -1 - subterm
    //      = -1 - (factor * lhs + rhs)
    //      = (-factor) * lhs + (-1 -rhs)
    //      = (-factor) * lhs + ~rhs

    BitVector tmp_factor;
    if (!get_linear_bv_term_aux(
            nm, nm.invert_node(node), tmp_factor, lhs, rhs, bound))
    {
      return false;
    }
    rhs = nm.invert_node(rhs);
    assert(!factor.is_null());
    factor.ibvneg();
  }
  else if (node.kind() == Kind::BV_ADD)
  {
    Node tmp, other;
    if (get_linear_bv_term_aux(nm, node[0], factor, lhs, tmp, bound))
    {
      // node = node[0] + node[1]
      //      = (factor * lhs + rhs) + node[1]
      //      = factor * lhs + (node[1] + rhs)
      other = node[1];
    }
    else if (get_linear_bv_term_aux(nm, node[1], factor, lhs, tmp, bound))
    {
      // node = node[0] + node[1]
      //      = node[0] + (factor * lhs + rhs)
      //      = factor * lhs + (node[0] + rhs)
      other = node[0];
    }
    else
    {
      return false;
    }
    rhs = nm.mk_node(Kind::BV_ADD, {other, tmp});
  }
  else if (node.kind() == Kind::BV_MUL)
  {
    Node tmp, other;
    if (node[0].is_value() && node[0].value<BitVector>().lsb())
    {
      if (!get_linear_bv_term_aux(nm, node[1], factor, lhs, tmp, bound))
      {
        return false;
      }
      // node = node[0] * node[1]
      //      = node[0] * (factor * lhs + rhs)
      //      = (node[0] * factor) * lhs + node[0] * rhs
      //      = (other * factor) * lhs + other * rhs
      other = node[0];
    }
    else if (node[1].is_value() && node[1].value<BitVector>().lsb())
    {
      if (!get_linear_bv_term_aux(nm, node[0], factor, lhs, tmp, bound))
      {
        return false;
      }
      // node = node[0] * node[1]
      //      = (factor * lhs + rhs) * node[1]
      //      = (node[1] * factor) * lhs + node[1] * rhs
      //      = (other * factor) * lhs + other * rhs
      other = node[1];
    }
    else
    {
      return false;
    }
    assert(!other.is_inverted());
    assert(!factor.is_null());
    factor.ibvmul(other.value<BitVector>());
    rhs = nm.mk_node(Kind::BV_MUL, {other, tmp});
  }
  else if (node.is_const())
  {
    uint64_t size = node.type().bv_size();
    lhs           = node;
    rhs           = nm.mk_value(BitVector::mk_zero(size));
    factor        = BitVector::mk_one(size);
  }
  else
  {
    return false;
  }

  assert(lhs.is_const());
  return true;
}

bool
get_linear_bv_term(
    NodeManager& nm, const Node& node, BitVector& factor, Node& lhs, Node& rhs)
{
  uint32_t bound = 100;
  bool res       = get_linear_bv_term_aux(nm, node, factor, lhs, rhs, bound);
  return res;
}

}  // namespace

std::pair<Node, Node>
PassVariableSubstitution::normalize_substitution_eq(const Node& node)
{
  assert(node.kind() == Kind::EQUAL);

  if (!node[0].type().is_bv() || node[0].is_const() || node[1].is_const())
  {
    return {};
  }

  NodeManager& nm   = d_env.nm();
  const Node& left  = node[0];
  const Node& right = node[1];
  Node var, subst, tmp;
  BitVector factor;
  if (get_linear_bv_term(nm, left, factor, var, tmp))
  {
    subst = nm.mk_node(Kind::BV_SUB, {right, tmp});
    d_stats.num_norm_eq_linear_eq += 1;
  }
  else if (get_linear_bv_term(nm, right, factor, var, tmp))
  {
    subst = nm.mk_node(Kind::BV_SUB, {left, tmp});
    d_stats.num_norm_eq_linear_eq += 1;
  }
  else
  {
    // no substitution found
    return {};
  }
  d_stats.num_norm_eq_gauss_elim += 1;
  subst = nm.mk_node(Kind::BV_MUL, {subst, nm.mk_value(factor.ibvmodinv())});
  if (var.is_inverted())
  {
    var   = nm.invert_node(var);
    subst = nm.invert_node(subst);
  }
  return std::make_pair(var, subst);
}

Kind
get_subst_inv_ineq_kind(Kind kind)
{
  if (kind == Kind::BV_ULT) return Kind::BV_UGT;
  if (kind == Kind::BV_ULE) return Kind::BV_UGE;
  if (kind == Kind::BV_UGT) return Kind::BV_ULT;
  if (kind == Kind::BV_UGE) return Kind::BV_ULE;
  if (kind == Kind::BV_SLT) return Kind::BV_SGT;
  if (kind == Kind::BV_SLE) return Kind::BV_SGE;
  if (kind == Kind::BV_SGT) return Kind::BV_SLT;
  assert(kind == Kind::BV_SGE);
  return Kind::BV_SLE;
}

std::pair<Node, Node>
PassVariableSubstitution::normalize_substitution_bv_ineq(const Node& node)
{
  assert(node.kind() == Kind::BV_ULT || node.kind() == Kind::BV_SLT
         || (node.is_inverted()
             && (node[0].kind() == Kind::BV_ULT
                 || node[0].kind() == Kind::BV_SLT)));

  bool inverted = node.is_inverted();
  const Node& n = inverted ? node[0] : node;
  Kind kind     = inverted
                      ? (n.kind() == Kind::BV_ULT ? Kind::BV_UGE : Kind::BV_SGE)
                      : n.kind();
  Node var, right;

  if (n[0].is_const())
  {
    var   = n[0];
    right = n[1];
  }
  else if (n[1].is_const())
  {
    var   = n[1];
    right = n[0];
    kind  = get_subst_inv_ineq_kind(kind);
  }
  else
  {
    return {};
  }

  NodeManager& nm = d_env.nm();

  // (<ineq_kind> (bvnot a) b) is equal to (<inv_ineq_kind> (a bvnot b))
  if (var.is_inverted())
  {
    var   = var[0];
    right = nm.invert_node(right);
    kind  = get_subst_inv_ineq_kind(n.kind());
  }

  BitVector value;
  if (right.is_value())
  {
    value = right.value<BitVector>();
  }
  else if (right.is_inverted() && right[0].is_value())
  {
    value = right[0].value<BitVector>().bvnot();
  }
  else
  {
    return {};
  }

  if (kind == Kind::BV_ULT || kind == Kind::BV_ULE)
  {
    uint64_t clz = value.count_leading_zeros();
    uint64_t size = var.type().bv_size();
    if (clz != size && clz > 0)
    {
      d_stats.num_norm_bv_ult += 1;
      Node subst = nm.mk_node(Kind::BV_CONCAT,
                              {nm.mk_value(BitVector::mk_zero(clz)),
                               nm.mk_const(nm.mk_bv_type(size - clz))});
      return {var, subst};
    }
  }
  else if (kind == Kind::BV_UGT || kind == Kind::BV_UGE)
  {
    uint64_t clo = value.count_leading_ones();
    uint64_t size = var.type().bv_size();
    if (clo != size && clo > 0)
    {
      d_stats.num_norm_bv_ult += 1;
      Node subst = nm.mk_node(Kind::BV_CONCAT,
                              {nm.mk_value(BitVector::mk_ones(clo)),
                               nm.mk_const(nm.mk_bv_type(size - clo))});
      return {var, subst};
    }
  }
  else if (kind == Kind::BV_SLT || kind == Kind::BV_SLE)
  {
    if (value.msb())
    {
      d_stats.num_norm_bv_slt += 1;
      uint64_t clz = 0;
      uint64_t size = var.type().bv_size();
      if (size > 1)
      {
        clz = value.bvextract(size - 2, 0).count_leading_zeros();
      }
      if (clz < size - 1)
      {
        Node subst = nm.mk_node(Kind::BV_CONCAT,
                                {nm.mk_value(BitVector::mk_min_signed(clz + 1)),
                                 nm.mk_const(nm.mk_bv_type(size - clz - 1))});
        return {var, subst};
      }
    }
  }
  else
  {
    assert(kind == Kind::BV_SGT || kind == Kind::BV_SGE);
    if (!value.msb())
    {
      d_stats.num_norm_bv_slt += 1;
      uint64_t clo = 0;
      uint64_t size = var.type().bv_size();
      if (size > 1)
      {
        clo = value.bvextract(size - 2, 0).count_leading_ones();
      }
      if (clo < size - 1)
      {
        Node subst = nm.mk_node(Kind::BV_CONCAT,
                                {nm.mk_value(BitVector::mk_max_signed(clo + 1)),
                                 nm.mk_const(nm.mk_bv_type(size - clo - 1))});
        return {var, subst};
      }
    }
  }
  return {};
}

std::pair<Node, Node>
PassVariableSubstitution::find_substitution(const Node& assertion)
{
  util::Timer timer(d_stats.time_find_substitution);
  NodeManager& nm = d_env.nm();

  if (assertion.kind() == Kind::EQUAL)
  {
    if (assertion[0].kind() == Kind::CONSTANT)
    {
      return std::make_pair(assertion[0], assertion[1]);
    }

    if (assertion[1].kind() == Kind::CONSTANT)
    {
      return std::make_pair(assertion[1], assertion[0]);
    }

    if (d_env.options().pp_variable_subst_norm_eq())
    {
      return normalize_substitution_eq(assertion);
    }
  }
  else if (assertion.is_const())
  {
    return std::make_pair(assertion, nm.mk_value(true));
  }
  else if (assertion.is_inverted() && assertion[0].is_const())
  {
    return std::make_pair(assertion[0], nm.mk_value(false));
  }
  return std::make_pair(Node(), Node());
}

namespace {
/**
 * match:  (= (bvconcat a_[n] b) c_[m])
 * result: (and
 *           (=
 *             ((_ extract u l) (bvconcat a b))
 *             ((_ extract u l) c))
 *           (=
 *             ((_ extract (l - 1) 0) (bvconcat a b))
 *             ((_ extract (l - 1)  0) c))
 *         with u = m - 1
 *              l = m - n + 1
 */
Node
_rw_eq_bv_concat(Rewriter& rewriter, const Node& node, size_t idx)
{
  assert(node.num_children() == 2);
  size_t idx0 = idx;
  size_t idx1 = 1 - idx;
  if (node[idx0].kind() == Kind::BV_CONCAT)
  {
    uint64_t m = node[idx1].type().bv_size();
    uint64_t u = m - 1;
    uint64_t l = m - node[idx0][0].type().bv_size();

    Node ext1_lhs = rewriter.mk_node(Kind::BV_EXTRACT, {node[idx1]}, {u, l});
    Node ext1_rhs =
        rewriter.mk_node(Kind::BV_EXTRACT, {node[idx1]}, {l - 1, 0});
    Node ext0_lhs = rewriter.mk_node(Kind::BV_EXTRACT, {node[idx0]}, {u, l});
    Node ext0_rhs =
        rewriter.mk_node(Kind::BV_EXTRACT, {node[idx0]}, {l - 1, 0});

    if ((ext1_lhs.kind() != Kind::BV_EXTRACT
         || ext1_lhs[0].kind() == Kind::CONSTANT)
        && (ext1_rhs.kind() != Kind::BV_EXTRACT
            || ext1_rhs[0].kind() == Kind::CONSTANT)
        && (ext0_lhs.kind() != Kind::BV_EXTRACT
            || ext0_lhs[0].kind() == Kind::CONSTANT)
        && (ext0_rhs.kind() != Kind::BV_EXTRACT
            || ext0_rhs[0].kind() == Kind::CONSTANT))
    {
      Node lhs = rewriter.mk_node(Kind::EQUAL, {ext0_lhs, ext1_lhs});
      Node rhs = rewriter.mk_node(Kind::EQUAL, {ext0_rhs, ext1_rhs});
      return rewriter.mk_node(Kind::AND, {lhs, rhs});
    }
  }
  return node;
}

Node
rw_eq_bv_concat(Rewriter& rewriter, const Node& node)
{
  Node rewritten = node, prev;
  do
  {
    prev = rewritten;
    if (prev.kind() == Kind::EQUAL)
    {
      rewritten = _rw_eq_bv_concat(rewriter, prev, 0);
      if (rewritten == prev)
      {
        rewritten = _rw_eq_bv_concat(rewriter, prev, 1);
      }
    }
  } while (rewritten != prev);
  return rewritten;
}

Node
rw_eq_bv_concat_apply(Rewriter& rewriter, const Node& n)
{
  if (n.kind() == Kind::EQUAL && n[0].type().is_bv())
  {
    Node rewritten = rw_eq_bv_concat(rewriter, n);
    if (rewritten != n)
    {
      return rewritten;
    }
  }
  else if (n.kind() == Kind::NOT && n[0].kind() == Kind::EQUAL
           && n[0][0].type().is_bv())
  {
    Node rewritten = rw_eq_bv_concat(rewriter, n[0]);
    if (rewritten != n[0])
    {
      return rewriter.mk_node(Kind::NOT, {rewritten});
    }
  }
  return Node();
}

}  // namespace

std::vector<Node>
PassVariableSubstitution::normalize_substitution_eq_bv_concat(const Node& n)
{
  std::vector<Node> res;
  std::vector<Node> visit;
  unordered_node_ref_set visited;

  Node rewritten = rw_eq_bv_concat_apply(d_env.rewriter(), n);
  if (!rewritten.is_null())
  {
    visit.push_back(rewritten);
  }

  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = visited.insert(cur);
    if (inserted)
    {
      rewritten = rw_eq_bv_concat_apply(d_env.rewriter(), cur);
      if (!rewritten.is_null())
      {
        visit.push_back(rewritten);
      }
      else if (cur.kind() == Kind::AND)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }

      if (cur.kind() == Kind::EQUAL && (cur[0].is_const() || cur[1].is_const()))
      {
        res.push_back(cur);
      }
      else if (cur.is_const() || (cur.kind() == Kind::NOT && cur[0].is_const()))
      {
        res.push_back(cur);
      }
      else if (cur.kind() == Kind::NOT && cur[0].kind() == Kind::EQUAL)
      {
        res.push_back(cur);
      }
    }
  }

  d_stats.num_norm_eq_bv_concat += res.size();
  return res;
}

std::vector<Node>
PassVariableSubstitution::normalize_for_substitution(const Node& assertion)
{
  NodeManager& nm = d_env.nm();
  if (d_env.options().pp_variable_subst_norm_diseq() && assertion.is_inverted()
      && assertion[0].kind() == Kind::EQUAL
      && (assertion[0][0].type().is_bool()
          || (assertion[0][0].type().is_bv()
              && assertion[0][0].type().bv_size() == 1)))
  {
    // This is worse on FP, and overall does not yield an improvement.
    // a != b is the same as a == ~b
    const Node& eq  = assertion[0];
    if (eq[0].is_const())
    {
      return {nm.mk_node(Kind::EQUAL, {eq[0], nm.invert_node(eq[1])})};
    }
    if (eq[1].is_const())
    {
      return {nm.mk_node(Kind::EQUAL, {eq[1], nm.invert_node(eq[0])})};
    }
  }
  else if (d_env.options().pp_variable_subst_norm_bv_ineq()
           && (assertion.kind() == Kind::BV_ULT
               || assertion.kind() == Kind::BV_SLT
               || (assertion.is_inverted()
                   && (assertion[0].kind() == Kind::BV_ULT
                       || assertion[0].kind() == Kind::BV_SLT))))
  {
    auto [var, term] = normalize_substitution_bv_ineq(assertion);
    if (!var.is_null())
    {
      return {nm.mk_node(Kind::EQUAL, {var, term})};
    }
  }

  return normalize_substitution_eq_bv_concat(assertion);
}

/* --- PassVariableSubstitution public -------------------------------------- */

PassVariableSubstitution::PassVariableSubstitution(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "vs", "varsubst"),
      d_substitutions(backtrack_mgr),
      d_subst_cache(backtrack_mgr),
      d_coi_cache(backtrack_mgr),
      d_coi(backtrack_mgr),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

void
PassVariableSubstitution::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);
  Log(1) << "Apply variable substitution";

  // Check current set of assertions for variable substitutions
  std::unordered_map<Node, std::vector<Node>> new_substs;
  std::unordered_map<Node, std::vector<Node>> subst_asserts;
  {
    util::Timer timer(d_stats.time_register);
    for (size_t i = 0; i < assertions.size(); ++i)
    {
      const Node assertion = assertions[i];
      if (!cache_assertion(assertion))
      {
        continue;
      }
      auto [var, term] = find_substitution(assertion);

      // No variable substitution
      if (var.is_null())
      {
        // Try to normalize assertion for term substitution.
        auto normalized = normalize_for_substitution(assertion);
        if (!normalized.empty())
        {
          // Explicitly add normalized assertion that was derived from
          // assertion.
          for (const auto& n : normalized)
          {
            assertions.push_back(n, assertion);
          }
        }
        continue;
      }

      // Check if we can safely substitute the variable, i.e., the variable
      // does not appear in assertions at lower assertion levels.
      if (!is_safe_to_substitute(var))
      {
        if (term.is_const() && is_safe_to_substitute(term))
        {
          std::swap(var, term);
        }
        else
        {
          continue;
        }
      }

      // Variable already substituted, try to swap with term.
      if (d_substitutions.find(var) != d_substitutions.end())
      {
        if (term.is_const() && is_safe_to_substitute(term)
            && d_substitutions.find(term) == d_substitutions.end())
        {
          std::swap(var, term);
        }
        else
        {
          continue;
        }
      }
      // Variable already substituted, try to swap with term and collect
      // substitution candidate.
      else if (new_substs.find(var) != new_substs.end())
      {
        if (term.is_const() && is_safe_to_substitute(term))
        {
          std::swap(var, term);
        }
      }

      // Collect all substitution candidates
      new_substs[var].emplace_back(term);
      subst_asserts[var].emplace_back(assertion);
      Log(2) << "Add substitution: " << var << " -> " << term;
    }
    Log(1) << "Found " << new_substs.size() << " new substitution candidates";
  }

  // No substitutions
  if (d_substitutions.empty() && new_substs.empty())
  {
    return;
  }

  // Reset substitution caches since we have new substitutions
  if (!new_substs.empty())
  {
    d_subst_cache.clear();
    d_coi_cache.clear();
  }

  // Compute COI of substitutions and remove cyclic substitutions
  mark_coi_and_remove_cycles(assertions, new_substs);
  Log(2) << "Substitution COI size: " << d_coi.size();

  if (d_substitutions.empty() && new_substs.empty())
  {
    return;
  }

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value())
    {
      continue;
    }
    Node replacement = substitute(assertion, new_substs, d_subst_cache, true);
    assertions.replace(i, replacement);
  }

  // Add new substitutions to substitution map
  d_stats.num_substs += new_substs.size();
  for (const auto& [var, terms] : new_substs)
  {
    auto it = subst_asserts.find(var);
    assert(it != subst_asserts.end());
    size_t i = it->second.size() - terms.size();
    d_substitutions.emplace(var, std::make_pair(terms.front(), it->second[i]));
  }
}

Node
PassVariableSubstitution::process(const Node& term)
{
  util::Timer timer(d_stats.time_process);
  std::unordered_map<Node, std::vector<Node>> map;
  return substitute(term, map, d_subst_cache, false);
}

bool
PassVariableSubstitution::is_safe_to_substitute(const Node& var)
{
  return !d_preproc_cache.frozen(var);
}

void
PassVariableSubstitution::mark_coi_and_remove_cycles(
    const AssertionVector& assertions,
    std::unordered_map<Node, std::vector<Node>>& subst_candidates)
{
  // Compute COI of substitutions for current set of assertions
  util::Timer timer(d_stats.time_coi);
  std::vector<Node> coi_visit;
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    coi_visit.push_back(assertions[i]);
  }

  // Make sure to include substitution terms in COI.
  for (const auto& p : subst_candidates)
  {
    coi_visit.push_back(p.first);
  }

  std::vector<size_t> subst_var;
  while (!coi_visit.empty())
  {
    const Node cur = coi_visit.back();
    ++d_stats.num_coi_trav;

    if (d_preproc_cache.frozen(cur))
    {
      d_coi_cache.try_emplace(cur, true, 0);
      coi_visit.pop_back();
      continue;
    }

    auto [it, inserted] = d_coi_cache.try_emplace(cur, false, coi_visit.size());
    if (inserted)
    {
      if (cur.is_const())
      {
        auto its = subst_candidates.find(cur);
        if (its != subst_candidates.end())
        {
          const Node& cached = d_preproc_cache.get(its->second.front());
          subst_var.push_back(coi_visit.size() - 1);  // Points to index of cur
          coi_visit.push_back(cached);
        }
        else if (d_substitutions.find(cur) != d_substitutions.end())
        {
          d_coi.insert(cur);
          coi_visit.push_back(d_preproc_cache.get(cur));
        }
      }
      else
      {
        coi_visit.insert(coi_visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (!it->second.first)
    {
      // Cyclic substitution detected
      if (it->second.second != coi_visit.size())
      {
        util::Timer timer(d_stats.time_backtrack_cyclic_subst);
        ++d_stats.num_cycles;

        assert(!subst_var.empty());
        size_t pop_to = subst_var.back();
        subst_var.pop_back();

        assert(pop_to < coi_visit.size());
        Node var = coi_visit[pop_to];
        assert(subst_candidates.find(var) != subst_candidates.end());

        // Reset visit stack to var, but keep var on stack. Remove current path
        // from coi cache.
        while (coi_visit.size() > pop_to + 1)
        {
          const Node& n = coi_visit.back();
          auto itc      = d_coi_cache.find(n);
          // Only remove from cache if it was added after var, otherwise it
          // can happen that nodes are removed that were added before var.
          if (itc != d_coi_cache.end() && itc->second.second > pop_to)
          {
            d_coi_cache.erase(itc);
          }
          coi_visit.pop_back();
        }
        assert(coi_visit.back() == var);

        // Remove substitution candidate
        assert(subst_candidates.find(var) != subst_candidates.end());
        auto& terms = subst_candidates[var];
        assert(!terms.empty());
        terms.erase(terms.begin());
        if (terms.empty())  // No more candidate terms, delete substitution
        {
          subst_candidates.erase(var);
        }
        else  // Try next substitution candidate
        {
          d_coi_cache.erase(var);
        }
        continue;
      }
      else
      {
        auto m_it           = d_coi_cache.modify(it);
        m_it->second.first  = true;
        m_it->second.second = 0;
        if (cur.is_const())
        {
          auto its = subst_candidates.find(cur);
          if (its != subst_candidates.end())
          {
            assert(coi_visit[subst_var.back()] == cur);
            subst_var.pop_back();
            d_coi.insert(cur);
          }
        }
        else
        {
          for (const Node& c : cur)
          {
            if (d_coi.find(c) != d_coi.end())
            {
              d_coi.insert(cur);
              break;
            }
          }
        }
      }
    }
    coi_visit.pop_back();
  }
}

const backtrack::unordered_map<Node, std::pair<Node, Node>>&
PassVariableSubstitution::substitutions() const
{
  return d_substitutions;
}

const Node&
PassVariableSubstitution::substitution_assertion(const Node& var) const
{
  auto it = d_substitutions.find(var);
  assert(it != d_substitutions.end());
  return it->second.second;
}

/* --- PassVariableSubstitution private ------------------------------------- */

#ifndef NDEBUG
namespace {

void
dbg_check_all_substituted(
    const Node& n,
    const backtrack::unordered_map<Node, std::pair<Node, Node>>& substitutions,
    const std::unordered_map<Node, std::vector<Node>>& new_substitutions)
{
  std::vector<Node> visit{n};
  std::unordered_set<Node> cache;

  do
  {
    Node cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (substitutions.find(cur) != substitutions.end())
      {
        std::cout << "not substituted (old): " << cur << std::endl;
      }
      assert(substitutions.find(cur) == substitutions.end());
      if (new_substitutions.find(cur) != new_substitutions.end())
      {
        std::cout << "not substituted (new): " << cur << std::endl;
      }
      assert(new_substitutions.find(cur) == new_substitutions.end());
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

}  // namespace
#endif

Node
PassVariableSubstitution::substitute(
    const Node& term,
    const std::unordered_map<Node, std::vector<Node>>& substitutions,
    backtrack::unordered_map<Node, bool>& cache,
    bool use_coi)
{
  util::Timer timer(d_stats.time_substitute);

  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    ++d_stats.num_subst_trav;

    if ((use_coi && d_coi.find(cur) == d_coi.end())
        || d_preproc_cache.frozen(cur))
    {
      cache.emplace(cur, true);
      visit.pop_back();
      continue;
    }
    assert(!d_preproc_cache.frozen(cur));

    auto [it, inserted] = cache.emplace(cur, false);
    if (inserted)
    {
      if (cur.is_const())
      {
        auto its = substitutions.find(cur);
        if (its != substitutions.end())
        {
          visit.push_back(d_preproc_cache.get(its->second.front()));
        }
        else if (d_substitutions.find(cur) != d_substitutions.end())
        {
          visit.push_back(d_preproc_cache.get(cur));
        }
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (!it->second)
    {
      auto m_it    = cache.modify(it);
      m_it->second = true;
      auto its = cur.is_const() ? substitutions.find(cur) : substitutions.end();

      Node res;
      if (its != substitutions.end())
      {
        res = d_preproc_cache.get(its->second.front());
      }
      else
      {
        res = d_preproc_cache.rebuild_node(d_env.nm(), cur);
      }
      assert(!res.is_null());

      d_preproc_cache.add(
          cur, res, preprocess::SimplifyCache::Cacher::VARSUBST);
    }
    visit.pop_back();
  } while (!visit.empty());

  Node res = d_env.rewriter().rewrite(d_preproc_cache.get(term));
#ifndef NDEBUG
  dbg_check_all_substituted(res, d_substitutions, substitutions);
#endif
  return res;
}

PassVariableSubstitution::Statistics::Statistics(util::Statistics& stats,
                                                 const std::string& prefix)
    : time_register(
          stats.new_stat<util::TimerStatistic>(prefix + "time_register")),
      time_backtrack_cyclic_subst(stats.new_stat<util::TimerStatistic>(
          prefix + "time_backtrack_cyclic_subst")),
      time_substitute(
          stats.new_stat<util::TimerStatistic>(prefix + "time_substitute")),
      time_coi(stats.new_stat<util::TimerStatistic>(prefix + "time_coi")),
      time_find_substitution(stats.new_stat<util::TimerStatistic>(
          prefix + "time_find_substitution")),
      time_process(
          stats.new_stat<util::TimerStatistic>(prefix + "time_process")),
      num_substs(stats.new_stat<uint64_t>(prefix + "num_substs")),
      num_cycles(stats.new_stat<uint64_t>(prefix + "num_cycles")),
      num_norm_eq_linear_eq(
          stats.new_stat<uint64_t>(prefix + "normalize_eq::num_linear_eq")),
      num_norm_eq_gauss_elim(
          stats.new_stat<uint64_t>(prefix + "normalize_eq::num_gauss_elim")),
      num_norm_eq_bv_concat(
          stats.new_stat<uint64_t>(prefix + "normalize_eq::num_bv_concat")),
      num_norm_bv_ult(
          stats.new_stat<uint64_t>(prefix + "normalize_bv_ineq::num_ult")),
      num_norm_bv_slt(
          stats.new_stat<uint64_t>(prefix + "normalize_bv_ineq::num_slt")),
      num_coi_trav(stats.new_stat<uint64_t>(prefix + "num_coi_traversals")),
      num_subst_trav(stats.new_stat<uint64_t>(prefix + "num_subst_traversals"))

{
}

}  // namespace bzla::preprocess::pass
