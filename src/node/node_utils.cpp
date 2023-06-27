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

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
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
      && ite[0][idx0].index(1) == msb && ite[1].is_value()
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

Node
mk_nary(Kind kind, const std::vector<Node>& terms)
{
  assert(!terms.empty());
  if (terms.size() == 1)
  {
    return terms[0];
  }

  NodeManager& nm = NodeManager::get();
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
mk_default_value(const Type& type)
{
  NodeManager& nm = NodeManager::get();
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
    return nm.mk_value(FloatingPoint::fpzero(type, false));
  }
  else if (type.is_fun())
  {
    std::vector<Node> children;
    const std::vector<Type>& types = type.fun_types();
    for (size_t i = 0, size = types.size() - 1; i < size; ++i)
    {
      children.push_back(nm.mk_var(types[i]));
    }
    children.push_back(mk_default_value(types.back()));
    return mk_nary(Kind::LAMBDA, children);
  }
  else if (type.is_array())
  {
    return nm.mk_const_array(type, mk_default_value(type.array_element()));
  }
  assert(type.is_rm());
  return nm.mk_value(RoundingMode::RNA);
}

Node
mk_binder(Kind kind, const std::vector<Node>& terms)
{
  assert(terms.size() >= 2);
  NodeManager& nm = NodeManager::get();
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
bv1_to_bool(const Node& node)
{
  assert(node.type().is_bv() && node.type().bv_size() == 1);
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(node::Kind::EQUAL,
                    {node, nm.mk_value(BitVector::mk_true())});
}

Node
bool_to_bv1(const Node& node)
{
  assert(node.type().is_bool());
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::ITE,
                    {nm.mk_node(Kind::EQUAL, {node, nm.mk_value(true)}),
                     nm.mk_value(BitVector::mk_true()),
                     nm.mk_value(BitVector::mk_false())});
}

Node
rebuild_node(const Node& node, const std::vector<Node>& children)
{
  assert(node.num_children() == children.size());
  if (node.num_children() == 0)
  {
    assert(children.empty());
    return node;
  }
  else if (node.kind() == Kind::CONST_ARRAY)
  {
    assert(children.size() == 1);
    return NodeManager::get().mk_const_array(node.type(), children[0]);
  }
  else
  {
    NodeManager& nm = NodeManager::get();
    if (node.num_indices() > 0)
    {
      return nm.mk_node(node.kind(), children, node.indices());
    }
    return nm.mk_node(node.kind(), children);
  }
}

Node
rebuild_node(const Node& node, const std::unordered_map<Node, Node>& cache)
{
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
    return NodeManager::get().mk_const_array(node.type(), children[0]);
  }
  else
  {
    NodeManager& nm = NodeManager::get();
    if (node.num_indices() > 0)
    {
      return nm.mk_node(node.kind(), children, node.indices());
    }
    return nm.mk_node(node.kind(), children);
  }
}

}  // namespace bzla::node::utils
