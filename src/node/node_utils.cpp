/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_utils.h"

#include <algorithm>
#include <sstream>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::node::utils {

namespace {
bool
_is_bv_sext_aux(const Node& ite, const Node& ext, size_t idx)
{
  size_t idx0  = idx;
  size_t idx1  = 1 - idx;
  uint64_t msb = ext.type().bv_size() - 1;

  if (ite[0][idx0].kind() == Kind::BV_EXTRACT && ite[0][idx1].is_value()
      && ite[0][idx0][0] == ext && ite[0][idx0].index(0) == msb
      && ite[0][idx0].index(1) == msb && ite[1].is_value() && ite[2].is_value()
      && ((ite[0][idx1].value<BitVector>().is_one()
           && ite[1].value<BitVector>().is_ones()
           && ite[2].value<BitVector>().is_zero())
          || (ite[0][idx1].value<BitVector>().is_zero()
              && ite[1].value<BitVector>().is_zero()
              && ite[2].value<BitVector>().is_ones())))
  {
    return true;
  }
  return false;
}
}  // namespace

bool
is_bv_sext(const Node& node, Node& child)
{
  if (node.kind() == Kind::BV_SIGN_EXTEND)
  {
    child = node[0];
    return true;
  }

  if (node.kind() != Kind::BV_CONCAT)
  {
    return false;
  }

  const Node& ite = node[0];
  if (ite.kind() != Kind::ITE || ite[0].kind() != Kind::EQUAL)
  {
    return false;
  }

  if (_is_bv_sext_aux(ite, node[1], 0) || _is_bv_sext_aux(ite, node[1], 1))
  {
    child = node[1];
    return true;
  }

  return false;
}

bool
has_x(const Node& node, const Node& x)
{
  std::vector<Node> visit{node};
  std::unordered_set<Node> cache;
  do
  {
    auto cur            = visit.back();
    auto [it, inserted] = cache.emplace(cur);
    visit.pop_back();
    if (cur == x)
    {
      return true;
    }
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

namespace {

/**
 * Compute the free variables of `node` and all of its subterms into `cache`.
 * Nodes already present in `cache` are fully computed and not traversed again,
 * which is what makes sharing a cache across calls worthwhile.
 */
void
compute_free_vars(const Node& node,
                  std::unordered_map<Node, std::unordered_set<Node>>& cache)
{
  std::unordered_map<Node, bool> visited;
  node_ref_vector visit{node};
  do
  {
    const Node& cur = visit.back();

    if (cache.find(cur) != cache.end())
    {
      visit.pop_back();
      continue;
    }

    auto [it, inserted] = visited.emplace(cur, false);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (!it->second)
    {
      it->second = true;
      std::unordered_set<Node> vars;
      if (cur.kind() == Kind::VARIABLE)
      {
        vars.insert(cur);
      }
      else
      {
        for (const Node& child : cur)
        {
          const auto& child_vars = cache.at(child);
          vars.insert(child_vars.begin(), child_vars.end());
        }
        if (KindInfo::is_binder(cur.kind()))
        {
          vars.erase(cur[0]);
        }
      }
      cache.emplace(cur, std::move(vars));
    }
    visit.pop_back();
  } while (!visit.empty());
}

}  // namespace

bool
free_vars(const Node& node,
          std::unordered_set<Node>* fvs,
          std::unordered_map<Node, std::unordered_set<Node>>& cache)
{
  compute_free_vars(node, cache);
  const auto& vars = cache.at(node);
  if (fvs)
  {
    fvs->insert(vars.begin(), vars.end());
  }
  return !vars.empty();
}

bool
free_vars(const Node& node, std::unordered_set<Node>* fvs)
{
  std::unordered_map<Node, std::unordered_set<Node>> cache;
  return free_vars(node, fvs, cache);
}

Node
mk_nary(NodeManager& nm, Kind kind, const std::vector<Node>& terms)
{
  assert(!terms.empty());
  if (terms.size() == 1)
  {
    return terms[0];
  }

  size_t size     = terms.size();

  if (KindInfo::is_left_associative(kind))
  {
    Node res = nm.mk_node(kind, {terms[0], terms[1]});
    for (size_t i = 2; i < size; ++i)
    {
      res = nm.mk_node(kind, {res, terms[i]});
    }
    return res;
  }

  if (KindInfo::is_right_associative(kind))
  {
    Node res = nm.mk_node(kind, {terms[size - 2], terms[size - 1]});
    for (size_t i = 3; i <= size; ++i)
    {
      res = nm.mk_node(kind, {terms[size - i], res});
    }
    return res;
  }

  if (KindInfo::is_chainable(kind))
  {
    Node res = nm.mk_node(kind, {terms[0], terms[1]});
    for (size_t i = 2; i < size; ++i)
    {
      res = nm.mk_node(node::Kind::AND,
                       {res, nm.mk_node(kind, {terms[i - 1], terms[i]})});
    }
    return res;
  }

  assert(KindInfo::is_pairwise(kind));
  Node res;
  for (size_t i = 0; i < size - 1; ++i)
  {
    for (size_t j = i + 1; j < size; ++j)
    {
      if (res.is_null())
      {
        res = nm.mk_node(kind, {terms[i], terms[j]});
      }
      else
      {
        res = nm.mk_node(node::Kind::AND,
                         {res, nm.mk_node(kind, {terms[i], terms[j]})});
      }
    }
  }
  assert(!res.is_null());
  return res;
}

Node
mk_default_value(NodeManager& nm, const Type& type)
{
  if (type.is_bool())
  {
    return nm.mk_value(false);
  }
  else if (type.is_bv())
  {
    return nm.mk_value(BitVector::mk_zero(type.bv_size()));
  }
  else if (type.is_fp())
  {
    return nm.mk_value(
        FloatingPoint::fpzero(type.fp_exp_size(), type.fp_sig_size(), false));
  }
  else if (type.is_fun())
  {
    std::vector<Node> children;
    const std::vector<Type>& types = type.fun_types();
    for (size_t i = 0, size = types.size() - 1; i < size; ++i)
    {
      children.push_back(nm.mk_var(types[i]));
    }
    children.push_back(mk_default_value(nm, types.back()));
    return mk_nary(nm, Kind::LAMBDA, children);
  }
  else if (type.is_array())
  {
    return nm.mk_const_array(type, mk_default_value(nm, type.array_element()));
  }
  else if (type.is_uninterpreted())
  {
    std::stringstream ss;
    ss << "@const_def" << type.id();
    return nm.mk_value(type, ss.str());
  }
  assert(type.is_rm());
  return nm.mk_value(RoundingMode::RNA);
}

Node
next_value(NodeManager& nm, const Node& value)
{
  const Type& type = value.type();
  if (type.is_bool())
  {
    if (value.value<bool>())
    {
      return Node();
    }
    return nm.mk_value(true);
  }
  else if (type.is_bv())
  {
    if (value.value<BitVector>().is_ones())
    {
      return Node();
    }
    return nm.mk_value(value.value<BitVector>().bvinc());
  }
  else if (type.is_rm())
  {
    const auto& rm = value.value<RoundingMode>();
    assert(rm != RoundingMode::NUM_RM);
    RoundingMode next = static_cast<RoundingMode>(static_cast<int32_t>(rm) + 1);
    if (next == RoundingMode::NUM_RM)
    {
      return Node();
    }
    return nm.mk_value(next);
  }
  else
  {
    assert(type.is_fp());
    const FloatingPoint& fp = value.value<FloatingPoint>();

    if (fp.fpisnan())
    {
      return Node();
    }

    BitVector bv = fp.as_bv();
    bv.flip_bit(bv.size() - 1);
    if (!bv.msb())
    {
      bv.ibvinc();
      return nm.mk_value(
          FloatingPoint(type.fp_exp_size(), type.fp_sig_size(), bv));
    }
    return nm.mk_value(
        FloatingPoint(type.fp_exp_size(), type.fp_sig_size(), bv));
  }
}

Node
mk_binder(NodeManager& nm, Kind kind, const std::vector<Node>& terms)
{
  assert(terms.size() >= 2);
  Node res        = terms.back();
  for (size_t i = 1, size = terms.size(); i < size; ++i)
  {
    const auto& var = terms[size - 1 - i];
    assert(var.kind() == node::Kind::VARIABLE);
    res = nm.mk_node(kind, {var, res});
  }
  return res;
}

Node
bv1_to_bool(NodeManager& nm, const Node& node)
{
  assert(node.type().is_bv() && node.type().bv_size() == 1);
  return nm.mk_node(node::Kind::EQUAL,
                    {node, nm.mk_value(BitVector::mk_true())});
}

Node
bool_to_bv1(NodeManager& nm, const Node& node)
{
  assert(node.type().is_bool());
  return nm.mk_node(Kind::ITE,
                    {nm.mk_node(Kind::EQUAL, {node, nm.mk_value(true)}),
                     nm.mk_value(BitVector::mk_true()),
                     nm.mk_value(BitVector::mk_false())});
}

Node
rebuild_node(NodeManager& nm,
             const Node& node,
             const std::vector<Node>& children)
{
  assert(!node.is_null());
  assert(node.num_children() == children.size());
  if (node.num_children() == 0)
  {
    assert(children.empty());
    return node;
  }
  else if (node.kind() == Kind::CONST_ARRAY)
  {
    assert(children.size() == 1);
    return nm.mk_const_array(node.type(), children[0]);
  }
  else
  {
    if (node.num_indices() > 0)
    {
      return nm.mk_node(node.kind(), children, node.indices());
    }
    return nm.mk_node(node.kind(), children);
  }
}

Node
rebuild_node(NodeManager& nm,
             const Node& node,
             const std::unordered_map<Node, Node>& cache)
{
  assert(!node.is_null());
  std::vector<Node> children;

  bool changed = false;
  for (const Node& child : node)
  {
    auto iit = cache.find(child);
    assert(iit != cache.end());
    assert(!iit->second.is_null());
    children.push_back(iit->second);
    changed |= iit->second != child;
  }

  if (!changed || node.num_children() == 0)
  {
    return node;
  }
  else if (node.kind() == Kind::CONST_ARRAY)
  {
    assert(children.size() == 1);
    return nm.mk_const_array(node.type(), children[0]);
  }
  else
  {
    if (node.num_indices() > 0)
    {
      return nm.mk_node(node.kind(), children, node.indices());
    }
    return nm.mk_node(node.kind(), children);
  }
}

namespace {

/** Determine whether `node` is or contains a binder. */
bool
has_binder(const Node& node)
{
  const NodeInfo& info = node.node_info();
  return info.quantifier || info.lambda;
}

/** Maps a node to a set of variables. */
using FreeVarsMap = std::unordered_map<Node, std::unordered_set<Node>>;

/**
 * Determines whether a binder captures a substitution.
 *
 * A binder binds a variable, hence only substituting a variable can be
 * shadowed or captured by one. Substituting anything else is only captured if
 * it introduces free variables, which no caller does.
 */
struct Capture
{
  /**
   * Record the free variables of the term `var` is substituted with.
   *
   * Nothing is recorded for substituted nodes that are not variables and for
   * substitutions without free variables, neither of which can be captured.
   */
  void add(const Node& var, const Node& subst)
  {
    if (var.kind() != Kind::VARIABLE)
    {
#ifndef NDEBUG
      // Substituting a node that is not a variable is not capture-avoiding,
      // hence it must not introduce free variables that a binder can capture.
      compute_free_vars(var, d_fv_cache);
      compute_free_vars(subst, d_fv_cache);
      const auto& var_fvs = d_fv_cache.at(var);
      for (const Node& fv : d_fv_cache.at(subst))
      {
        assert(var_fvs.find(fv) != var_fvs.end());
      }
#endif
      return;
    }
    std::unordered_set<Node> fvs;
    if (free_vars(subst, &fvs, d_fv_cache))
    {
      d_vars.insert(fvs.begin(), fvs.end());
      d_var_fvs.emplace(var, std::move(fvs));
    }
  }

  /** @return True if no binder can capture a substitution. */
  bool empty() const { return d_vars.empty(); }

  /**
   * @return True if `binder` captures a substitution, i.e., if a substituted
   *         variable occurs free in `binder` and is substituted with a term in
   *         which the variable of `binder` occurs free.
   */
  bool is_captured(const Node& binder)
  {
    assert(KindInfo::is_binder(binder.kind()));

    // Only a binder that binds a free variable of a substituted term can
    // capture it. This keeps the free variables below the binder from being
    // computed for the vast majority of binders.
    if (d_vars.find(binder[0]) == d_vars.end())
    {
      return false;
    }
    compute_free_vars(binder, d_fv_cache);
    // The free variables of the binder exclude its own variable, i.e.,
    // variables that are shadowed by it are not considered here.
    const auto& binder_fvs = d_fv_cache.at(binder);
    for (const auto& [var, subst_fvs] : d_var_fvs)
    {
      if (binder_fvs.find(var) != binder_fvs.end()
          && subst_fvs.find(binder[0]) != subst_fvs.end())
      {
        return true;
      }
    }
    return false;
  }

 private:
  /** Maps a substituted variable to the free variables of its substitution. */
  FreeVarsMap d_var_fvs;
  /** The union of the above, used as a cheap check per binder. */
  std::unordered_set<Node> d_vars;
  /** Cache for the free variables computed below binders. */
  FreeVarsMap d_fv_cache;
};

Node substitute_aux(NodeManager& nm,
                    const Node& node,
                    const std::unordered_map<Node, Node>& substitutions,
                    Capture* capture,
                    std::unordered_map<Node, Node>& cache,
                    bool follow_substs,
                    uint64_t* num_substs);

/** Apply substitutions to the body of a binder that needs its own scope. */
Node
substitute_binder(NodeManager& nm,
                  const Node& binder,
                  const std::unordered_map<Node, Node>& substitutions,
                  bool captured,
                  Capture* capture,
                  bool follow_substs,
                  uint64_t* num_substs)
{
  assert(KindInfo::is_binder(binder.kind()));

  const Node& var = binder[0];
  Node new_var    = var;
  Node body       = binder[1];

  if (captured)
  {
    // Rename the variable of the binder in its body before substituting. The
    // renaming must not be applied to the substituted terms, which refer to
    // the variable of the enclosing scope. The fresh variable cannot capture
    // anything, it is bound by this binder only.
    new_var = nm.mk_var(var.type(), var.symbol());
    std::unordered_map<Node, Node> renaming{{var, new_var}};
    std::unordered_map<Node, Node> renaming_cache;
    body = substitute_aux(
        nm, body, renaming, nullptr, renaming_cache, false, nullptr);
  }

  // The binder shadows its variable, it must not be substituted in its scope.
  std::unordered_map<Node, Node> substs(substitutions);
  substs.erase(var);
  if (!substs.empty())
  {
    // Nodes in the scope of the binder are substituted w.r.t. `substs` and
    // must not be cached in the cache of the enclosing scope.
    std::unordered_map<Node, Node> scope_cache;
    body = substitute_aux(
        nm, body, substs, capture, scope_cache, follow_substs, num_substs);
  }

  return nm.mk_node(binder.kind(), {new_var, body});
}

/**
 * Apply substitutions to `node`.
 *
 * Binders that need a scope of their own are processed by substitute_binder(),
 * which recurses with the substitution map of that scope. `capture` is null if
 * no binder can capture a substitution; shadowing still has to be handled.
 */
Node
substitute_aux(NodeManager& nm,
               const Node& node,
               const std::unordered_map<Node, Node>& substitutions,
               Capture* capture,
               std::unordered_map<Node, Node>& cache,
               bool follow_substs,
               uint64_t* num_substs)
{
  node::node_ref_vector visit{node};

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());
    if (!inserted && !it->second.is_null())
    {
      visit.pop_back();
      continue;
    }

    auto its         = substitutions.find(cur);
    bool substituted = its != substitutions.end() && its->second != cur;

    if (inserted)
    {
      if (!substituted)
      {
        if (KindInfo::is_binder(cur.kind()))
        {
          // A binder that shadows a substituted node or that would capture a
          // substitution needs a scope of its own.
          bool captured = capture && capture->is_captured(cur);
          if (captured || substitutions.find(cur[0]) != substitutions.end())
          {
            // Note: `it` may be invalidated by the recursive call.
            cache[cur] = substitute_binder(nm,
                                           cur,
                                           substitutions,
                                           captured,
                                           capture,
                                           follow_substs,
                                           num_substs);
            visit.pop_back();
            continue;
          }
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      else if (follow_substs)
      {
        visit.push_back(its->second);
        continue;
      }
    }

    if (substituted)
    {
      assert(!its->second.is_null());
      // With `follow_substs` the substituted term has been processed above.
      it->second = follow_substs ? cache.at(its->second) : its->second;
      if (num_substs)
      {
        *num_substs += 1;
      }
    }
    else
    {
      it->second = rebuild_node(nm, cur, cache);
    }
    assert(!it->second.is_null());
    visit.pop_back();
  } while (!visit.empty());

  return cache.at(node);
}

}  // namespace

Node
substitute(NodeManager& nm,
           const Node& node,
           const std::unordered_map<Node, Node>& substitutions,
           std::unordered_map<Node, Node>& cache,
           bool follow_substs,
           uint64_t* num_substs)
{
  if (substitutions.empty())
  {
    return node;
  }

  // Shadowing and capture are only possible below a binder. If `follow_substs`
  // is enabled, substituted terms are also traversed and may contain binders.
  bool binders =
      has_binder(node)
      || (follow_substs
          && std::any_of(substitutions.begin(),
                         substitutions.end(),
                         [](const auto& p) { return has_binder(p.second); }));

  Capture capture;
  if (binders)
  {
    for (const auto& [n, subst] : substitutions)
    {
      capture.add(n, subst);
    }
  }

  return substitute_aux(nm,
                        node,
                        substitutions,
                        capture.empty() ? nullptr : &capture,
                        cache,
                        follow_substs,
                        num_substs);
}

Node
invert_node(NodeManager& nm, const Node& node)
{
  if (node.is_inverted())
  {
    return node[0];
  }
  const Type& type = node.type();
  if (type.is_bv())
  {
    return nm.mk_node(Kind::BV_NOT, {node});
  }
  assert(type.is_bool());
  return nm.mk_node(Kind::NOT, {node});
}

}  // namespace bzla::node::utils
