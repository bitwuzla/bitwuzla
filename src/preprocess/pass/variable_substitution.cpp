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

  auto [it, inserted] = d_norm_subst_cache.insert(node);
  if (inserted)
  {
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
  return {};
}

Kind
get_subst_inv_ineq_kind(Kind kind)
{
  if (kind == Kind::BV_ULT) return Kind::BV_UGT;
  if (kind == Kind::BV_ULE) return Kind::BV_UGE;
  if (kind == Kind::BV_UGT) return Kind::BV_ULT;
  assert(kind == Kind::BV_UGE);
  return Kind::BV_ULE;
}

std::pair<Node, Node>
PassVariableSubstitution::normalize_substitution_bvult(const Node& node)
{
  assert(node.kind() == Kind::BV_ULT
         || (node.is_inverted() && node[0].kind() == Kind::BV_ULT));

  bool inverted = node.is_inverted();
  const Node& n = inverted ? node[0] : node;
  Kind kind     = inverted ? Kind::BV_UGE : Kind::BV_ULT;
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
    kind  = get_subst_inv_ineq_kind(n.kind());
  }
  else
  {
    return {};
  }

  NodeManager& nm = NodeManager::get();

  // ((bvnot a) <ineq_kind> b) is equal to (<inv_ineq_kind> (a bvnot b))
  if (var.is_inverted())
  {
    var   = var[0];
    right = nm.invert_node(right);
    kind  = get_subst_inv_ineq_kind(n.kind());
  }

  if (!right.is_value())
  {
    return {};
  }

  const BitVector& value = right.value<BitVector>();

  if (kind == Kind::BV_ULT || kind == Kind::BV_ULE)
  {
    uint64_t clz = value.count_leading_zeros();
    if (clz > 0)
    {
      d_stats.num_norm_bvult += 1;
      Node subst =
          nm.mk_node(Kind::BV_CONCAT,
                     {nm.mk_value(BitVector::mk_zero(clz)),
                      nm.mk_const(nm.mk_bv_type(var.type().bv_size() - clz))});
      return {var, subst};
    }
  }
  else
  {
    assert(kind == Kind::BV_UGT || kind == Kind::BV_UGE);
    uint64_t clo = value.count_leading_ones();
    if (clo > 0)
    {
      d_stats.num_norm_bvult += 1;
      Node subst =
          nm.mk_node(Kind::BV_CONCAT,
                     {nm.mk_value(BitVector::mk_ones(clo)),
                      nm.mk_const(nm.mk_bv_type(var.type().bv_size() - clo))});
      return {var, subst};
    }
  }
  return {};
}

std::pair<Node, Node>
PassVariableSubstitution::find_substitution(const Node& assertion)
{
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
  else if (d_env.options().pp_variable_subst_norm_bvult()
           && (assertion.kind() == Kind::BV_ULT
               || (assertion.is_inverted()
                   && assertion[0].kind() == Kind::BV_ULT)))
  {
    return normalize_substitution_bvult(assertion);
  }
  else if (assertion.is_const())
  {
    return std::make_pair(assertion, nm.mk_value(true));
  }
  else if (assertion.is_inverted() && assertion[0].is_const())
  {
    return std::make_pair(assertion[0], nm.mk_value(false));
  }
  // TODO: more substitution normalizations
  return std::make_pair(Node(), Node());
}

/* --- PassVariableSubstitution public -------------------------------------- */

PassVariableSubstitution::PassVariableSubstitution(
    Env& env, backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env),
      d_backtrack_mgr(backtrack_mgr),
      d_substitutions(backtrack_mgr),
      d_substitution_assertions(backtrack_mgr),
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

  // Check current set of assertions for variable substitutions
  std::unordered_map<Node, Node> new_substs;
  {
    util::Timer timer(d_stats.time_register);
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      const Node& assertion  = assertions[i];
      auto [var, term]       = find_substitution(assertion);
      // No variable substitution
      if (var.is_null())
      {
        continue;
      }
      // If var already substituted, check if term is also a variable.
      else if (d_substitutions.find(var) != d_substitutions.end())
      {
        if (term.is_const()
            && d_substitutions.find(term) == d_substitutions.end())
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
        d_substitutions.emplace(var, term_processed);
        d_substitution_assertions.emplace(assertion, std::make_pair(var, term));
        new_substs.emplace(var, term_processed);
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

  // No substitutions
  if (substitution_map.empty())
  {
    return;
  }

  // Reset substitution cache since we have new substitutions
  d_cache.cache().clear();

  // Apply substitutions.
  //
  // Note: For non-top-level substitution assertions, we only process the term
  // side of the assertion and do not eliminate the assertion itself since we
  // have to keep the variable equality for cases where the variable still
  // occurs in lower levels (if variable substitution assertion was added in a
  // scope > 0). We could check whether the variable occurs in lower levels,
  // but for now we keep the assertion since this makes it simpler overall.
  bool top_level  = d_backtrack_mgr->num_levels() == 0;
  NodeManager& nm = NodeManager::get();
  Rewriter& rewriter = d_env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    // Keep non-top-level variable substitution assertion, but apply
    // substitutions in term.
    if (!top_level)
    {
      auto it = d_substitution_assertions.find(assertion);
      if (it != d_substitution_assertions.end())
      {
        const auto& [var, term] = it->second;
        assert(!var.is_null());
        // Make sure to rewrite the assertion, otherwise we may run into loops
        // with rewriter pass due to the substitution normalizations in
        // find_substitution(), e.g., a -- subst --> a = true -- rewrite --> a.
        Node rewritten =
            rewriter.rewrite(nm.mk_node(Kind::EQUAL, {var, process(term)}));
        assertions.replace(i, rewritten);
        // Add new substitution assertion to cache in order to avoid that this
        // new assertion will be eliminated by variable substitution.
        d_substitution_assertions.emplace(rewritten, std::make_pair(var, term));
        continue;
      }
    }
    assertions.replace(i, process(assertion));
  }
}

Node
PassVariableSubstitution::process(const Node& term)
{
  return d_env.rewriter().rewrite(
      substitute(term, d_cache.substitutions(), d_cache.cache()));
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
    const std::unordered_map<Node, Node>& substitutions,
    std::unordered_map<Node, Node>& cache) const
{
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end())
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
      if (its != substitutions.end())
      {
        auto iit = cache.find(its->second);
        assert(iit != cache.end());
        it->second = iit->second;
      }
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto iit = cache.find(child);
          assert(iit != cache.end());
          assert(!iit->second.is_null());
          children.push_back(iit->second);
        }
        it->second = utils::rebuild_node(cur, children);
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(term);
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
      num_substs(stats.new_stat<uint64_t>("preprocess::varsubst::num_substs")),
      num_linear_eq(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_eq::num_linear_eq")),
      num_gauss_elim(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_eq::num_gauss_elim")),
      num_norm_bvult(stats.new_stat<uint64_t>(
          "preprocess::varsubst::normalize_bvult::num_norm_bvult"))

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

std::unordered_map<Node, Node>&
PassVariableSubstitution::Cache::cache()
{
  return d_cache.back();
}

}  // namespace bzla::preprocess::pass
