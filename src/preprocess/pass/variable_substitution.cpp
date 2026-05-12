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

#include <deque>

#include "bv/bitvector.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "util/hash.h"
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
      d_first_seen(backtrack_mgr),
      d_first_seen_cache(backtrack_mgr),
      d_cache(backtrack_mgr),
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

  auto& substitution_map = d_cache.substitutions();
  bool process_term      = !substitution_map.empty();
  size_t start_index     = assertions.start_index();

  // Check current set of assertions for variable substitutions
  std::unordered_map<Node, Node> new_substs;
  std::unordered_map<Node, size_t> subst_index;
  std::unordered_map<Node, std::vector<std::pair<Node, Node>>> extract_map;
  {
    util::Timer timer(d_stats.time_register);
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      const Node& assertion  = assertions[i];
      if (!cache_assertion(assertion))
      {
        continue;
      }
      find_vars(assertion, start_index + i);
      // Try to normalize assertion for term substitution.
      auto normalized = normalize_for_substitution(assertion);
      if (!normalized.empty())
      {
        // Explicitly add normalized assertion that was derived from assertion.
        // Note: Do not use assertion here since this reference may become
        //       invalid when resizing the assertions vector.
        Node parent = assertion;
        for (const auto& n : normalized)
        {
          assertions.push_back(n, parent);
        }
        continue;
      }
      auto [var, term] = find_substitution(assertion);
      // No variable substitution
      if (var.is_null())
      {
        collect_extracts(assertion, extract_map);
        continue;
      }
      // If var already substituted, check if term is also a variable.
      else if (d_substitutions.find(var) != d_substitutions.end()
               || new_substs.find(var) != new_substs.end())
      {
        if (term.is_const()
            && (d_substitutions.find(term) == d_substitutions.end()
                && new_substs.find(term) == new_substs.end()))
        {
          std::swap(var, term);
        }
        else
        {
          continue;
        }
      }

      if (d_exclude_consts.find(var) != d_exclude_consts.end())
      {
        continue;
      }

      // If we already have substitutions, process the term first to ensure
      // that all variables in this term are substituted before we check for
      // cycles. This allows us to incrementally add new substitutions and
      // check for cycles.
      Node term_processed = process_term ? process(term) : term;

      // Do not add direct substitution cycles
      if (!is_direct_cycle(var, term_processed))
      {
        new_substs.emplace(var, term_processed);
        subst_index.emplace(var, i);
        Log(2) << "Add substitution: " << var << " -> " << term_processed;
      }
    }
  }

  if (!extract_map.empty())
  {
    process_extracts(extract_map, assertions, new_substs, subst_index);
  }

  Log(1) << "Found " << new_substs.size() << " new substitutions";

  // Remove substitution cycles
  {
    util::Timer timer_cycles(d_stats.time_remove_cycles);
    remove_indirect_cycles(new_substs);
    Log(1) << new_substs.size() << " substitutions after cycle removal";
  }

  // Add new substitutions to substitution map
  substitution_map.insert(new_substs.begin(), new_substs.end());
  d_stats.num_substs = substitution_map.size();

  // Cache assertion indices of non-cyclic substitutions.
  for (const auto& [var, term] : new_substs)
  {
    auto it = subst_index.find(var);
    assert(it != subst_index.end());
    size_t real_index = it->second + start_index;
    assert(d_substitution_assertions.find(real_index)
           == d_substitution_assertions.end());
    d_substitution_assertions.emplace(real_index, var);
    d_substitutions.emplace(var, std::make_pair(term, assertions[it->second]));
  }

  // No substitutions
  if (substitution_map.empty())
  {
    return;
  }

  // Reset substitution cache since we have new substitutions
  if (!new_substs.empty())
  {
    d_cache.cache().clear();
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
  // the assertions of a previous check-sat call. Since we only preprocess
  // newly added assertions b will not be globally substituted in all
  // assertions and therefore we have to keep the substitution constraint b = s
  // around. As a solution we only fully substitute initial assertions, i.e.,
  // assertions from the first check-sat call.
  // We could check whether a variable to be substituted occurs in assertions
  // of previous check-sat calls in order to optimize this, but for now we keep
  // the assertion since this avoids an additional traversal over previous
  // assertions that we don't have access to in this pass.
  bool initial_assertions = assertions.initial_assertions();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    // Only do full substitution on initial assertions.
    if (!initial_assertions)
    {
      auto it = d_substitution_assertions.find(start_index + i);
      if (it != d_substitution_assertions.end())
      {
        const auto& var = it->second;
        // Variable occurs in previous assertions, don't perform full
        // substitution.
        if (!is_safe_to_substitute(var, start_index))
        {
          Node replacement = process(assertion, var);
          assertions.replace(i, replacement);
          continue;
        }
      }
    }
    Node replacement = process(assertion);
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
  Node null;
  return d_env.rewriter().rewrite(
      substitute(term, null, d_cache.substitutions(), d_cache.cache()));
}

bool
PassVariableSubstitution::is_safe_to_substitute(const Node& var,
                                                size_t assertion_start_index)
{
  auto it = d_first_seen.find(var);
  assert(it != d_first_seen.end());
  return it->second >= assertion_start_index;
}

void
PassVariableSubstitution::find_vars(const Node& assertion, size_t index)
{
  util::Timer timer(d_stats.time_find_vars);
  node_ref_vector visit{assertion};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    if (d_first_seen_cache.insert(cur).second)
    {
      if (cur.is_const())
      {
        d_first_seen.emplace(cur, index);
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

const std::unordered_map<Node, Node>&
PassVariableSubstitution::substitutions() const
{
  return d_cache.substitutions();
}

const Node&
PassVariableSubstitution::substitution_assertion(const Node& var) const
{
  auto it = d_substitutions.find(var);
  assert(it != d_substitutions.end());
  return it->second.second;
}

/* --- PassVariableSubstitution private ------------------------------------- */

void
PassVariableSubstitution::remove_indirect_cycles(
    std::unordered_map<Node, Node>& substitutions) const
{
  int64_t order_num = 1;
  std::unordered_map<Node, int64_t> order;
  node::unordered_node_ref_map<bool> cache;
  node::node_ref_vector visit, nodes;
  std::vector<size_t> marker{0};

  // Compute topological order of substitutions. Assumes that direct cycles
  // were already removed.
  for (const auto& [var, term] : substitutions)
  {
    visit.push_back(var);
    do
    {
      const Node& cur = visit.back();

      auto [it, inserted] = cache.emplace(cur, false);
      if (inserted)
      {
        if (cur.kind() == Kind::CONSTANT)
        {
          auto its = substitutions.find(cur);
          if (its != substitutions.end())
          {
            // Mark first occurrence of substituted constant on the stack
            marker.push_back(visit.size());
            visit.push_back(its->second);
          }
        }
        else
        {
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
        continue;
      }
      // Check if constant is first occurrence on the stack (i.e., marked)
      else if (marker.back() == visit.size())
      {
        assert(cur.kind() == Kind::CONSTANT);
        assert(substitutions.find(cur) != substitutions.end());
        marker.pop_back();
        // Assign substitution rank
        assert(order.find(cur) == order.end());
        order.emplace(cur, order_num++);
      }
      else if (!it->second)
      {
        it->second = true;
      }
      visit.pop_back();
    } while (!visit.empty());
  }

  cache.clear();

  // Compute ranking for all remaining nodes.
  for (const auto& [var, term] : substitutions)
  {
    visit.push_back(term);
    do
    {
      const Node& cur     = visit.back();
      auto [it, inserted] = cache.emplace(cur, false);
      if (inserted)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      else if (!it->second)
      {
        if (order.find(cur) == order.end())
        {
          int64_t max = 0;
          for (const Node& child : cur)
          {
            auto iit = order.find(child);
            assert(iit != order.end());
            if (iit->second > max)
            {
              max = iit->second;
            }
          }
          order.emplace(cur, max);
        }
        it->second = true;
      }
      visit.pop_back();
    } while (!visit.empty());
  }

  // Remove substitutions to break cycles.
  auto it = substitutions.begin();
  while (it != substitutions.end())
  {
    auto itv = order.find(it->first);
    auto itt = order.find(it->second);
    assert(itv != order.end());
    assert(itt != order.end());

    // Found cycle if the rank of the term > rank of substituted constant.
    // Remove cyclic substitution.
    if (itt->second > itv->second)
    {
      it = substitutions.erase(it);
      Log(2) << "Remove cyclic substitution: " << itv->first << " -> "
             << itt->first;
    }
    else
    {
      ++it;
    }
  }
}

bool
PassVariableSubstitution::is_direct_cycle(const Node& var,
                                          const Node& term) const
{
  util::Timer timer(d_stats.time_direct_cycle_check);
  node::unordered_node_ref_set cache;
  std::deque<ConstNodeRef> visit{term};
  do
  {
    const Node& cur = visit.front();
    visit.pop_front();

    // var cannot be in cur
    if (cur.id() < var.id())
    {
      continue;
    }

    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      if (cur == var)
      {
        return true;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

Node
PassVariableSubstitution::substitute(
    const Node& term,
    const Node& excl_var,
    const std::unordered_map<Node, Node>& substitutions,
    std::unordered_map<Node, Node>& subst_cache)
{
  util::Timer timer(d_stats.time_substitute);
  node::node_ref_vector visit{term};
  std::unordered_map<Node, Node> local_cache;
  // Use local cache if excl_var should not be substituted, but was already
  // substituted in a previous substitute call. This makes sure that excl_var
  // will not be substituted.
  auto& cache = excl_var.is_null() ? subst_cache : local_cache;
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      auto its = substitutions.find(cur);
      if (cur != excl_var && its != substitutions.end())
      {
        visit.push_back(its->second);
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      auto its = substitutions.find(cur);
      if (cur != excl_var && its != substitutions.end())
      {
        auto iit = cache.find(its->second);
        assert(iit != cache.end());
        it->second = iit->second;
      }
      else
      {
        it->second = utils::rebuild_node(d_env.nm(), cur, cache);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(term);
}

Node
PassVariableSubstitution::process(const Node& term, const Node& excl_var)
{
  return d_env.rewriter().rewrite(
      substitute(term, excl_var, d_cache.substitutions(), d_cache.cache()));
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
    const std::unordered_map<Node, std::vector<std::pair<Node, Node>>>& extract_map,
    AssertionVector& assertions,
    std::unordered_map<Node, Node>& new_substs,
    std::unordered_map<Node, size_t>& subst_index)
{
  NodeManager& nm = d_env.nm();
  Rewriter& rw = d_env.rewriter();

  for (const auto& [var, extracts] : extract_map)
  {
    if (d_substitutions.find(var) != d_substitutions.end()
        || new_substs.find(var) != new_substs.end())
    {
      continue;
    }
    if (d_exclude_consts.find(var) != d_exclude_consts.end())
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
      Node concat = utils::mk_nary(nm, Kind::BV_CONCAT, slices);
      // Process term first to ensure that all variables in this term are
      // substituted before we check for cycles.
      if (!d_cache.substitutions().empty())
      {
        concat = process(concat);
      }
      if (!is_direct_cycle(var, concat))
      {
        Node eq = nm.mk_node(Kind::EQUAL, {var, concat});
        subst_index.emplace(var, assertions.size());
        assertions.push_back(eq, Node());
        new_substs.emplace(var, concat);
        d_stats.num_eq_elim_extracts += extracts.size();
        ++d_stats.num_eq_elim_extracts_substs;
        Log(2) << "Add substitution: " << var << " -> " << concat;
      }
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
      time_direct_cycle_check(stats.new_stat<util::TimerStatistic>(
          prefix + "time_direct_cycle_check")),
      time_remove_cycles(
          stats.new_stat<util::TimerStatistic>(prefix + "time_remove_cycles")),
      time_substitute(
          stats.new_stat<util::TimerStatistic>(prefix + "time_substitute")),
      time_find_vars(
          stats.new_stat<util::TimerStatistic>(prefix + "time_find_vars")),
      time_find_substitution(stats.new_stat<util::TimerStatistic>(
          prefix + "time_find_substitution")),
      time_compute_non_overlap(stats.new_stat<util::TimerStatistic>(
          prefix + "time_compute_non_overlap")),
      num_substs(stats.new_stat<uint64_t>(prefix + "num_substs")),
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

/* --- PassVariableSubstitution::Cache -------------------------------------- */

PassVariableSubstitution::Cache::Cache(backtrack::BacktrackManager* mgr)
    : Backtrackable(mgr)
{
  d_map.emplace_back();
  d_cache.emplace_back();
}

void
PassVariableSubstitution::Cache::push()
{
  // Make copy of previous level to allow calling process() after a pop()
  // without calling preprocess().
  d_map.emplace_back(d_map.back());
  d_cache.emplace_back(d_cache.back());
}

void
PassVariableSubstitution::Cache::pop()
{
  d_map.pop_back();
  d_cache.pop_back();
}

std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::substitutions()
{
  return d_map.back();
}

const std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::substitutions() const
{
  return d_map.back();
}

std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::cache()
{
  return d_cache.back();
}

}  // namespace bzla::preprocess::pass
