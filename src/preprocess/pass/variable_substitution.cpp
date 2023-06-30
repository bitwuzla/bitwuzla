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
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "rewrite/rewriter.h"
#include "util/logger.h"

namespace bzla::preprocess::pass {

using namespace node;

namespace {
bool
get_linear_bv_term_aux(
    const Node& node, BitVector& factor, Node& lhs, Node& rhs, uint32_t& bound)
{
  assert(node.type().is_bv());

  if (bound == 0)
  {
    return false;
  }

  bound -= 1;

  NodeManager& nm = NodeManager::get();
  if (node.is_inverted())
  {
    // node = ~subterm
    //      = -1 - subterm
    //      = -1 - (factor * lhs + rhs)
    //      = (-factor) * lhs + (-1 -rhs)
    //      = (-factor) * lhs + ~rhs

    BitVector tmp_factor;
    if (!get_linear_bv_term_aux(
            nm.invert_node(node), tmp_factor, lhs, rhs, bound))
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
    if (get_linear_bv_term_aux(node[0], factor, lhs, tmp, bound))
    {
      // node = node[0] + node[1]
      //      = (factor * lhs + rhs) + node[1]
      //      = factor * lhs + (node[1] + rhs)
      other = node[1];
    }
    else if (get_linear_bv_term_aux(node[1], factor, lhs, tmp, bound))
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
      if (!get_linear_bv_term_aux(node[1], factor, lhs, tmp, bound))
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
      if (!get_linear_bv_term_aux(node[0], factor, lhs, tmp, bound))
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
get_linear_bv_term(const Node& node, BitVector& factor, Node& lhs, Node& rhs)
{
  uint32_t bound = 100;
  bool res       = get_linear_bv_term_aux(node, factor, lhs, rhs, bound);
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

  NodeManager& nm   = NodeManager::get();
  const Node& left  = node[0];
  const Node& right = node[1];
  Node var, subst, tmp;
  BitVector factor;
  if (get_linear_bv_term(left, factor, var, tmp))
  {
    subst = nm.mk_node(Kind::BV_SUB, {right, tmp});
    d_stats.num_linear_eq += 1;
  }
  else if (get_linear_bv_term(right, factor, var, tmp))
  {
    subst = nm.mk_node(Kind::BV_SUB, {left, tmp});
    d_stats.num_linear_eq += 1;
  }
  else
  {
    // no substitution found
    return {};
  }
  d_stats.num_gauss_elim += 1;
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

  NodeManager& nm = NodeManager::get();

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
  NodeManager& nm = NodeManager::get();

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

Node
PassVariableSubstitution::normalize_for_substitution(const Node& assertion)
{
  NodeManager& nm = NodeManager::get();
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
      return nm.mk_node(Kind::EQUAL, {eq[0], nm.invert_node(eq[1])});
    }
    if (eq[1].is_const())
    {
      return nm.mk_node(Kind::EQUAL, {eq[1], nm.invert_node(eq[0])});
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
      return nm.mk_node(Kind::EQUAL, {var, term});
    }
  }
  return Node();
}

/* --- PassVariableSubstitution public -------------------------------------- */

PassVariableSubstitution::PassVariableSubstitution(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_substitution_assertions(backtrack_mgr),
      d_first_seen(backtrack_mgr),
      d_first_seen_cache(backtrack_mgr),
      d_cache(backtrack_mgr),
      d_stats(env.statistics())
{
}

void
PassVariableSubstitution::apply(AssertionVector& assertions)
{
  util::Timer timer(d_stats.time_apply);
  Log(1) << "Apply variable substitution";

  auto& substitution_map = d_cache.substitutions();
  bool process_term      = !substitution_map.empty();
  size_t start_index     = assertions.start_index();

  // Check current set of assertions for variable substitutions
  std::unordered_map<Node, Node> new_substs;
  std::unordered_map<Node, size_t> subst_index;
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
      Node normalized = normalize_for_substitution(assertion);
      if (!normalized.is_null())
      {
        // Explicitly add normalized assertion that was derived from assertion.
        // Note: Do not use assertion here since this reference may become
        //       invalid when resizing the assertions vector.
        Node parent = assertion;
        assertions.push_back(normalized, parent);
        continue;
      }
      auto [var, term] = find_substitution(assertion);
      // No variable substitution
      if (var.is_null())
      {
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
    Log(1) << "Found " << new_substs.size() << " new substitutions";
  }

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
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.front();
    visit.erase(visit.begin());

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
        it->second = utils::rebuild_node(cur, cache);
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

PassVariableSubstitution::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::varsubst::time_apply")),
      time_register(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_register")),
      time_direct_cycle_check(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_direct_cycle_check")),
      time_remove_cycles(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_remove_cycles")),
      time_substitute(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_substitute")),
      time_find_vars(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_find_vars")),
      time_find_substitution(stats.new_stat<util::TimerStatistic>(
          "preprocess::varsubst::time_find_substitution")),
      num_substs(stats.new_stat<uint64_t>("preprocess::varsubst::num_substs")),
      num_linear_eq(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_eq::num_linear_eq")),
      num_gauss_elim(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_eq::num_gauss_elim")),
      num_norm_bv_ult(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_bv_ult::num_norm_bv_ult")),
      num_norm_bv_slt(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_bv_slt::num_norm_bv_slt"))

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
