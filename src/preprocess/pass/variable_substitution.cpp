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
#include "node/node_utils.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "util/hash.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

using namespace node;
using namespace node::utils;

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
    if (!get_linear_bv_term_aux(nm, node[0], factor, lhs, rhs, bound))
    {
      return false;
    }
    rhs = invert_node(nm, rhs);
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
  assert(var.is_const());
  d_stats.num_norm_eq_gauss_elim += 1;
  subst = nm.mk_node(Kind::BV_MUL, {subst, nm.mk_value(factor.ibvmodinv())});
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
  assert(var.is_const());

  NodeManager& nm = d_env.nm();

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
      return {nm.mk_node(Kind::EQUAL, {eq[0], invert_node(nm, eq[1])})};
    }
    if (eq[1].is_const())
    {
      return {nm.mk_node(Kind::EQUAL, {eq[1], invert_node(nm, eq[0])})};
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

namespace {

void
collect_extracts(const Node& assertion,
                 std::unordered_map<Node, std::vector<std::pair<Node, Node>>>& extracts)
{
  if (assertion.kind() == Kind::EQUAL)
  {
    if (assertion[0].kind() == Kind::BV_EXTRACT && assertion[0][0].is_const())
    {
      extracts[assertion[0][0]].emplace_back(assertion[0], assertion[1]);
    }
    if (assertion[1].kind() == Kind::BV_EXTRACT && assertion[1][0].is_const())
    {
      extracts[assertion[1][0]].emplace_back(assertion[1], assertion[0]);
    }
  }
}

void
extract_terms(NodeManager& nm,
              uint64_t offset,
              uint64_t upper,
              uint64_t lower,
              const std::vector<Node>& terms,
              std::vector<Node>& res)
{
  assert(!terms.empty());
#ifndef NDEBUG
  uint64_t size = terms[0].type().bv_size();
#endif
  upper -= offset;
  lower -= offset;
  for (const auto& t : terms)
  {
    assert(t.type().bv_size() == size);
    assert(upper < size);
    assert(lower < size);
    assert(lower <= upper);
    // Avoid double extract
    if (t.kind() == Kind::BV_EXTRACT)
    {
      const auto l = t.index(1);
      res.push_back(nm.mk_node(Kind::BV_EXTRACT, {t[0]}, {upper + l, lower + l}));
    }
    else
    {
      res.push_back(nm.mk_node(Kind::BV_EXTRACT, {t}, {upper, lower}));
    }
  }
  #ifndef NDEBUG
  for (const auto& n : res)
  {
    assert(n.type().bv_size() == upper - lower + 1);
  }
  #endif
}

}  // namespace

/* --- PassVariableSubstitution public -------------------------------------- */

PassVariableSubstitution::PassVariableSubstitution(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr, "vs", "varsubst"),
      d_substitutions(backtrack_mgr),
      d_substitution_assertions(backtrack_mgr),
      d_keep(backtrack_mgr),
      d_prev_nodes(backtrack_mgr),
      d_prev_scanned(backtrack_mgr),
      d_stats(env.statistics(), "preprocess::" + name() + "::")
{
}

void
PassVariableSubstitution::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats_pass.time_apply);

  // Disabled if unsat cores enabled for now.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }
  // Requires special labeling of substituted variable bits and post-processing
  // of interpolant, not yet supported.
  if (d_env.options().produce_interpolants())
  {
    return;
  }

  Log(1) << "Apply variable substitution";

  // Check current set of assertions for substitution candidates.
  assert(d_candidates.empty());
  std::unordered_map<Node, std::vector<std::pair<Node, Node>>> extract_map;
  std::vector<std::tuple<Node, Node, Node, size_t>> concats;
  {
    util::Timer timer(d_stats.time_register);
    // Note: Normalized assertions added in this loop are checked, too.
    for (size_t i = 0; i < assertions.size(); ++i)
    {
      // Note: Do not use a reference here since it may become invalid when
      //       resizing the assertions vector.
      const Node assertion = assertions[i];
      // Assertions are checked once for substitution candidates.
      if (!cache_assertion(assertion))
      {
        continue;
      }
      auto [var, term] = find_substitution(assertion);
      if (!var.is_null())
      {
        if (is_concat_of_vars(term))
        {
          concats.emplace_back(var, term, assertion, i);
          continue;
        }
        if (add_candidate(assertions, var, term, assertion, i))
        {
          continue;
        }
      }
      // Try to normalize assertion for term substitution.
      auto normalized = normalize_for_substitution(assertion);
      if (normalized.empty())
      {
        collect_extracts(assertion, extract_map);
        continue;
      }
      // Explicitly add normalized assertion that was derived from assertion.
      for (const auto& n : normalized)
      {
        assertions.push_back(n, assertion);
      }
    }
  }

  // Splitting `var = (concat x_1 ... x_n)` over variables x_i yields
  // substitutions of all x_i with slices of var instead of a single
  // substitution of var, and keeps var for other substitutions. This is only
  // beneficial if the x_i are not substituted otherwise, and if it does not
  // require keeping the substitution constraint of some x_i while the
  // substitution of var does not need to be kept.
  auto split_keeps = [&](const Node& var, const Node& concat) {
    if (occurs_in_previous(assertions, var))
    {
      return false;
    }
    node_ref_vector visit{concat};
    do
    {
      const Node& cur = visit.back();
      visit.pop_back();
      if (cur.kind() == Kind::BV_CONCAT)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      else if (occurs_in_previous(assertions, cur))
      {
        return true;
      }
    } while (!visit.empty());
    return false;
  };
  for (const auto& [var, term, assertion, index] : concats)
  {
    // The x_i may have gotten candidates since it was deferred.
    if (is_concat_of_vars(term) && !split_keeps(var, term))
    {
      // Split into x_i = var[u_i:l_i]. Not done above, since normalization is
      // skipped if a direct substitution was found.
      auto normalized = normalize_for_substitution(assertion);
      if (!normalized.empty())
      {
        for (const auto& n : normalized)
        {
          size_t i = assertions.size();
          assertions.push_back(n, assertion);
          auto [v, t] = find_substitution(n);
          if (!v.is_null())
          {
            add_candidate(assertions, v, t, n, i);
          }
        }
        continue;
      }
    }
    add_candidate(assertions, var, term, assertion, index);
  }

  if (!extract_map.empty())
  {
    process_extracts(extract_map, assertions);
  }

  Log(1) << "Found " << d_candidates.size() << " substitution candidates";

  // No substitutions
  if (d_substitutions.empty() && d_candidates.empty())
  {
    return;
  }

  size_t start_index = assertions.start_index();
  size_t num_substs  = d_substitutions.size();
  if (d_candidates.empty())
  {
    sync_cache();
  }
  else
  {
    // Cached results do not reflect the new candidates.
    d_cache.clear();
    // Substituting a candidate variable resolves its cycles. Process them in
    // the order they were found, which determines which candidate of a cycle
    // is dropped.
    for (const Node& var : d_candidate_vars)
    {
      substitute(var);
    }
    for (const Node& var : d_candidate_vars)
    {
      const Candidate& c = d_candidates.at(var);
      if (c.selected == c.terms.size())
      {
        continue;
      }
      const auto& [term, assertion, index] = c.terms[c.selected];
      // Store the fully substituted term. Storing the term as found would
      // require to expand chains of substitutions again whenever the cache
      // is reset.
      auto it = d_cache.find(var);
      assert(it != d_cache.end());
      d_substitutions.emplace(var, it->second);
      d_substitution_assertions.emplace(var, assertion);
      if (c.keep)
      {
        d_keep.emplace(start_index + index, var);
      }
      auto ite = d_extract_eqs.find(assertion);
      if (ite != d_extract_eqs.end())
      {
        d_stats.num_eq_elim_extracts += ite->second;
        ++d_stats.num_eq_elim_extracts_substs;
      }
      Log(2) << "Add substitution: " << var << " -> " << it->second;
    }
    d_candidates.clear();
    d_candidate_vars.clear();
    d_extract_eqs.clear();
    d_cache_num_substs = d_substitutions.size();
    d_stats.num_substs = d_substitutions.size();
    Log(1) << d_substitutions.size() << " substitutions after cycle removal";
    // All candidates were cyclic.
    if (d_substitutions.empty())
    {
      return;
    }
  }

  // Apply substitutions.
  //
  // Note: We have to be careful when applying the substitutions to
  // substitution constraints since we can not always simplify them to true.
  //
  // For example:
  //
  // 1. check-sat call
  //
  //   a = t, F1[a], F2[b]
  //
  //   --> true, F1[a/t], F2[b]
  //
  // 2. check-sat call
  //
  //   true, F1[a/t], F2[b], b = s, F3[b]
  //
  //   --> true, F1[a/t], F2[b], b = s, F3[b/s]
  //
  // We are not allowed to substitute b = s with true since b occurs in one of
  // the assertions of a previous check-sat call, which are not reprocessed.
  // We therefore keep the substitution constraint of such variables.
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (assertion.is_value())
    {
      continue;
    }
    auto it = d_keep.find(start_index + i);
    if (it != d_keep.end())
    {
      // Only rebuild on new substitutions, other passes may have simplified
      // the constraint and rebuilding it every round would revert this.
      if (d_substitutions.size() > num_substs)
      {
        const Node& var = it->second;
        assertions.replace(
            i, d_env.rewriter().mk_node(Kind::EQUAL, {var, substitute(var)}));
      }
      continue;
    }
    Node replacement = process(assertion);
    // Substituted nodes do not contain any substituted variables.
    d_cache.emplace(replacement, replacement);
    assertions.replace(i, replacement);
  }
}

void
PassVariableSubstitution::exclude(const std::unordered_set<Node>& exclude)
{
  d_exclude_consts.insert(exclude.begin(), exclude.end());
}

Node
PassVariableSubstitution::process(const Node& term)
{
  assert(d_candidates.empty());
  sync_cache();
  // Rebuilt nodes are only rewritten locally, which requires rewritten input.
  return substitute(d_env.rewriter().rewrite(term));
}

const std::unordered_map<Node, Node>&
PassVariableSubstitution::substitutions() const
{
  return d_substitutions.map();
}

const Node&
PassVariableSubstitution::substitution_assertion(const Node& var) const
{
  auto it = d_substitution_assertions.find(var);
  assert(it != d_substitution_assertions.end());
  return it->second;
}

/* --- PassVariableSubstitution private ------------------------------------- */

bool
PassVariableSubstitution::can_substitute(const Node& var) const
{
  return var.is_const() && d_substitutions.find(var) == d_substitutions.end()
         && d_exclude_consts.find(var) == d_exclude_consts.end();
}

bool
PassVariableSubstitution::is_concat_of_vars(const Node& term) const
{
  // Variables that already have a candidate are not considered.
  if (term.kind() != Kind::BV_CONCAT)
  {
    return false;
  }
  node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();
    if (cur.kind() == Kind::BV_CONCAT)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (!can_substitute(cur)
             || d_candidates.find(cur) != d_candidates.end())
    {
      return false;
    }
  } while (!visit.empty());
  return true;
}

bool
PassVariableSubstitution::add_candidate(const AssertionVector& assertions,
                                        Node var,
                                        Node term,
                                        const Node& assertion,
                                        size_t index)
{
  // Rebuilt nodes are only rewritten locally, which requires rewritten terms.
  term = d_env.rewriter().rewrite(term);
  // If both sides are variables, choose the orientation of `var = term`.
  // Substituting variable v is less effective if
  //  - v occurs in assertions of previous calls, which are not reprocessed,
  //    hence the substitution constraint must be kept (cost 2), or
  //  - v already has a candidate, hence the term is only a fallback in case
  //    the candidate is cyclic (cost 1).
  // Swap only if the other orientation is strictly cheaper.
  auto cost = [&](const Node& v) {
    return (occurs_in_previous(assertions, v) ? 2 : 0)
           + (d_candidates.find(v) == d_candidates.end() ? 0 : 1);
  };
  if (term.is_const() && can_substitute(term)
      && (!can_substitute(var) || cost(term) < cost(var)))
  {
    std::swap(var, term);
  }
  else if (!can_substitute(var))
  {
    return false;
  }

  auto [it, inserted] = d_candidates.try_emplace(var);
  Candidate& c        = it->second;
  if (inserted)
  {
    d_candidate_vars.push_back(var);
    c.keep         = occurs_in_previous(assertions, var);
    d_min_subst_id = std::min(d_min_subst_id, var.id());
  }
  // Values can not be cyclic and yield the most simplification, try them
  // first.
  if (term.is_value())
  {
    c.terms.emplace(c.terms.begin(), term, assertion, index);
  }
  else
  {
    c.terms.emplace_back(term, assertion, index);
  }
  Log(2) << "Add substitution candidate: " << var << " -> " << term;
  return true;
}

Node
PassVariableSubstitution::substitute(const Node& term)
{
  util::Timer timer(d_stats.time_substitute);

  // Get substitution term of given node, and whether it is a candidate.
  auto get_subst = [this](const Node& node) -> std::pair<const Node*, bool> {
    if (node.is_const())
    {
      auto it = d_substitutions.find(node);
      if (it != d_substitutions.end())
      {
        return {&it->second, false};
      }
      auto itc = d_candidates.find(node);
      if (itc != d_candidates.end())
      {
        const Candidate& c = itc->second;
        if (c.selected < c.terms.size())
        {
          return {&std::get<0>(c.terms[c.selected]), true};
        }
      }
    }
    return {nullptr, false};
  };
  Rewriter& rw = d_env.rewriter();

  struct VisitEntry
  {
    ConstNodeRef node;
    /** Result entry in d_cache, null if the node was not expanded yet. */
    Node* result = nullptr;
    /** Size of the result stack when the node was expanded. */
    size_t base = 0;
    /** True if the node was expanded to its substitution term. */
    bool subst = false;
    /** True if the substitution term is a candidate term. */
    bool candidate = false;
  };
  std::vector<VisitEntry> visit{{term}};
  // Results of processed nodes, in the order the nodes were completed.
  std::vector<ConstNodeRef> results;
  // Stack positions of expanded candidate variables.
  std::vector<size_t> expanded;
  std::vector<Node> children;
  do
  {
    VisitEntry& entry = visit.back();
    const Node& cur   = entry.node;

    if (!entry.result)
    {
      if (cur.id() < d_min_subst_id)
      {
        results.push_back(cur);
        visit.pop_back();
        continue;
      }

      auto [it, inserted] = d_cache.emplace(cur, Node());
      if (inserted)
      {
        entry.result               = &it->second;
        entry.base                 = results.size();
        auto [subst, is_candidate] = get_subst(cur);
        if (subst)
        {
          entry.subst     = true;
          entry.candidate = is_candidate;
          if (is_candidate)
          {
            expanded.push_back(visit.size() - 1);
          }
          visit.push_back({*subst});
        }
        else
        {
          for (const Node& child : cur)
          {
            visit.push_back({child});
          }
        }
        continue;
      }
      if (!it->second.is_null())
      {
        results.push_back(it->second);
        visit.pop_back();
        continue;
      }

      // Node is reached while it is expanded, i.e., the current path is
      // cyclic. Committed substitutions are acyclic, hence the cycle contains
      // a candidate. Break it by switching the innermost candidate on the path
      // to its next term. Already processed nodes stay valid since they do
      // not reach any node on the path.
      ++d_stats.num_cycles;
      assert(!expanded.empty());
      size_t pos = expanded.back();
      expanded.pop_back();
      while (visit.size() > pos + 1)
      {
        if (visit.back().result)
        {
          d_cache.erase(visit.back().node);
        }
        visit.pop_back();
      }
      VisitEntry& var_entry = visit.back();
      assert(var_entry.result);
      assert(var_entry.candidate);
      results.erase(results.begin() + var_entry.base, results.end());
      const Node& var = var_entry.node;
      d_cache.erase(var);
      var_entry.result    = nullptr;
      var_entry.subst     = false;
      var_entry.candidate = false;
      Candidate& c        = d_candidates.at(var);
      Log(2) << "Remove cyclic substitution candidate: " << var << " -> "
             << std::get<0>(c.terms[c.selected]);
      ++c.selected;
      continue;
    }

    Node res;
    if (entry.subst)
    {
      assert(results.size() == entry.base + 1);
      res = results.back();
      results.pop_back();
      if (entry.candidate)
      {
        assert(expanded.back() == visit.size() - 1);
        expanded.pop_back();
      }
    }
    else if (cur.num_children() > 0)
    {
      // Children are processed in reverse order, hence their results are on
      // the result stack in reverse order.
      size_t n = cur.num_children();
      assert(results.size() == entry.base + n);
      children.clear();
      for (size_t i = 0; i < n; ++i)
      {
        children.push_back(results[entry.base + n - 1 - i]);
      }
      results.erase(results.begin() + entry.base, results.end());
      // Children are already rewritten, only rewrite the rebuilt node.
      res = rw.rebuild_node(cur, children);
    }
    else
    {
      res = cur;
    }
    *entry.result = res;
    results.push_back(*entry.result);
    visit.pop_back();
  } while (!visit.empty());

  assert(results.size() == 1);
  return results.back();
}

void
PassVariableSubstitution::sync_cache()
{
  // Substitutions only grow in apply(), which resets the cache. If they
  // shrink, substitutions were popped and cached results are outdated.
  if (d_cache_num_substs != d_substitutions.size())
  {
    d_cache.clear();
    d_cache_num_substs = d_substitutions.size();
  }
}

bool
PassVariableSubstitution::occurs_in_previous(const AssertionVector& assertions,
                                             const Node& var)
{
  if (assertions.initial_assertions())
  {
    return false;
  }

  // Collect nodes of assertions of previous preprocessing calls on demand.
  size_t end = assertions.start_index();
  if (d_prev_scanned.get() < end)
  {
    util::Timer timer(d_stats.time_scan_previous);
    node::node_ref_vector visit;
    for (size_t i = d_prev_scanned.get(); i < end; ++i)
    {
      visit.push_back(assertions.previous(i));
      do
      {
        const Node& cur = visit.back();
        visit.pop_back();
        if (d_prev_nodes.insert(cur).second)
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      } while (!visit.empty());
    }
    d_prev_scanned = end;
  }
  return d_prev_nodes.find(var) != d_prev_nodes.end();
}

namespace {

// Prefer value kinds, then constants, then everything else.
int32_t
priority(const Node& n)
{
  if (n.is_value()) return 0;
  if (n.is_const()) return 1;
  return 2;
}

}  // namespace

void
PassVariableSubstitution::process_extracts(
    const std::unordered_map<Node, std::vector<std::pair<Node, Node>>>&
        extract_map,
    AssertionVector& assertions)
{
  NodeManager& nm = d_env.nm();
  Rewriter& rw = d_env.rewriter();

  for (const auto& [var, extracts] : extract_map)
  {
    if (!can_substitute(var) || d_candidates.find(var) != d_candidates.end())
    {
      continue;
    }

    std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
    uint64_t size = var.type().bv_size();

    for (const auto& [extract, term] : extracts)
    {
      indices[std::make_pair(extract.index(0), extract.index(1))].push_back(
          term);
    }
    auto non_overlapping = compute_non_overlapping(nm, size, indices);
    if (non_overlapping.empty())
    {
      continue;
    }

    bool full_subst = true;
    std::vector<Node> slices;
    for (const auto& [upper, lower, terms] : non_overlapping)
    {
      std::vector<Node> terms_rw;
      for (const auto& t : terms)
      {
        terms_rw.push_back(rw.rewrite(t));
      }
      std::sort(
          terms_rw.begin(), terms_rw.end(), [](const Node& n1, const Node& n2) {
            auto p1 = priority(n1), p2 = priority(n2);
            return p1 < p2 || (p1 == p2 && n1.id() < n2.id());
          });
      bool added = false;
      for (const auto& t : terms_rw)
      {
        if (t == var || (t.kind() == Kind::BV_EXTRACT && t[0] == var))
        {
          continue;
        }
        slices.push_back(t);
        added = true;
        break;
      }
      if (!added)
      {
        full_subst = false;
        break;
      }
    }
    if (full_subst)
    {
      Node concat  = utils::mk_nary(nm, Kind::BV_CONCAT, slices);
      Node eq      = nm.mk_node(Kind::EQUAL, {var, concat});
      size_t index = assertions.size();
      assertions.push_back(eq, Node());
      add_candidate(assertions, var, concat, eq, index);
      d_extract_eqs.emplace(eq, extracts.size());
    }
  }
}

// Partition overlapping bit-ranges into non-overlapping sub-ranges.
//
// `indices` maps bit-ranges [u:l] to the terms (BV_EXTRACT nodes) that use
// that range.  When two ranges overlap, they are split into non-overlapping
// sub-ranges so that each sub-range collects terms from all original ranges
// that covered it.
//
// The algorithm works in a single pass using a boundary sweep:
//
//   1. Collect boundaries: every entry [u:l] contributes l (start) and u+1
//      (one-past-end) to a boundary set.
//
//   2. Sort and deduplicate the boundaries.  Consecutive pairs of boundaries
//      define the non-overlapping sub-ranges that partition the bit axis.
//
//   3. For each sub-range, find all original entries that cover it and collect
//      their terms (via extract_terms, or by direct move for exact matches).
//
// Example:
//   Input:  [7:0] -> {a}, [5:2] -> {b}
//   Boundaries: {0, 2, 6, 8}
//   Sub-ranges: [1:0], [5:2], [7:6]
//   Result: [1:0] -> {a[1:0]}, [5:2] -> {b, a[5:2]}, [7:6] -> {a[7:6]}
//
// Returns the non-overlapping sub-ranges sorted descending by upper bound if
// they fully cover [size-1:0], or an empty vector otherwise.
std::vector<PassVariableSubstitution::Range>
PassVariableSubstitution::compute_non_overlapping(
    NodeManager& nm,
    uint64_t size,
    std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>>&
        indices)
{
  std::vector<Range> result;

  util::Timer timer(d_stats.time_compute_non_overlap);

  // Step 1: Collect all entries and their range boundaries.
  // Each entry [u:l] contributes boundaries l and u+1 (one-past-end).
  std::vector<Range> ranges;
  std::vector<uint64_t> boundaries;
  ranges.reserve(indices.size());
  boundaries.reserve(2 * indices.size());
  for (auto& [key, terms] : indices)
  {
    auto [u, l] = key;
    ranges.push_back({u, l, std::move(terms)});
    boundaries.push_back(l);
    boundaries.push_back(u + 1);
  }
  indices.clear();

  // Step 2: Sort and deduplicate boundaries.
  std::sort(boundaries.begin(), boundaries.end());
  boundaries.erase(std::unique(boundaries.begin(), boundaries.end()),
                   boundaries.end());

  // Step 3: Walk consecutive boundaries to form sub-ranges.
  // Each pair (boundaries[j], boundaries[j+1]) defines a sub-range
  // [boundaries[j+1]-1 : boundaries[j]].  For each sub-range, collect
  // terms from all original entries that cover it.
  for (size_t j = 0; j + 1 < boundaries.size(); ++j)
  {
    uint64_t sub_l = boundaries[j];
    uint64_t sub_u = boundaries[j + 1] - 1;

    std::vector<Node> terms;
    bool covered = false;
    for (auto& r : ranges)
    {
      // Range [r.upper:r.lower] does not cover [sub_u:sub_l].
      if (r.lower > sub_l || r.upper < sub_u)
      {
        continue;
      }
      covered = true;
      if (r.lower == sub_l && r.upper == sub_u)
      {
        // Exact match — move terms directly, no extract needed.
        terms.insert(terms.end(),
                     std::make_move_iterator(r.terms.begin()),
                     std::make_move_iterator(r.terms.end()));
      }
      else
      {
        // Entry is wider than the sub-range — extract the relevant slice.
        extract_terms(nm, r.lower, sub_u, sub_l, r.terms, terms);
      }
    }
    if (covered)
    {
#ifndef NDEBUG
      for (const auto& t : terms)
      {
        assert(t.type() == terms[0].type());
      }
#endif
      result.push_back({sub_u, sub_l, std::move(terms)});
    }
  }

  // Sort descending by upper bound (then by lower bound).
  std::sort(result.begin(), result.end(), [](const Range& a, const Range& b) {
    return a.upper > b.upper || (a.upper == b.upper && a.lower > b.lower);
  });

  // Verify full coverage of [size-1 : 0]
  if (!result.empty())
  {
    bool covers =
        (result.front().upper == size - 1) && (result.back().lower == 0);
    for (size_t i = 0; covers && i + 1 < result.size(); ++i)
    {
      covers = (result[i].lower == result[i + 1].upper + 1);
    }
    if (!covers)
    {
      result.clear();
    }
  }

  return result;
}

PassVariableSubstitution::Statistics::Statistics(util::Statistics& stats,
                                                 const std::string& prefix)
    : time_register(
          stats.new_stat<util::TimerStatistic>(prefix + "time_register")),
      time_substitute(
          stats.new_stat<util::TimerStatistic>(prefix + "time_substitute")),
      time_scan_previous(
          stats.new_stat<util::TimerStatistic>(prefix + "time_scan_previous")),
      time_find_substitution(stats.new_stat<util::TimerStatistic>(
          prefix + "time_find_substitution")),
      time_compute_non_overlap(stats.new_stat<util::TimerStatistic>(
          prefix + "time_compute_non_overlap")),
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
      num_eq_elim_extracts(
          stats.new_stat<uint64_t>(prefix + "num_eq_elim_extract")),
      num_eq_elim_extracts_substs(
          stats.new_stat<uint64_t>(prefix + "num_eq_elim_extract_substs"))

{
}

}  // namespace bzla::preprocess::pass
