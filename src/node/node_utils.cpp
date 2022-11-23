#include "node/node_utils.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::node::utils {

bool
is_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::AND)
  {
    NodeManager& nm = NodeManager::get();
    child0 =
        node[0][0].is_inverted() ? node[0][0][0] : nm.invert_node(node[0][0]);
    child1 =
        node[0][1].is_inverted() ? node[0][1][0] : nm.invert_node(node[0][1]);
    return true;
  }
  return false;
}

bool
is_xor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::XOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  Node or0, or1;
  if (node.kind() == Kind::AND)
  {
    if ((is_or(node[0], or0, or1) && node[1].is_inverted()
         && node[1][0].kind() == Kind::AND
         && (node[1][0][0] == or0 || node[1][0][0] == or1)
         && (node[1][0][1] == or0 || node[1][0][1] == or1))
        || (is_or(node[1], or0, or1) && node[0].is_inverted()
            && node[0][0].kind() == Kind::AND
            && (node[0][0][0] == or0 || node[0][0][0] == or1)
            && (node[0][0][1] == or0 || node[0][0][1] == or1)))
    {
      child0 = or0;
      child1 = or1;
      return true;
    }
  }
  return false;
}

bool
is_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.is_inverted())
  {
    Node xor0, xor1;
    if (is_xor(node[0], xor0, xor1))
    {
      child0 = xor0;
      child1 = xor1;
      return true;
    }
  }
  return false;
}

bool
is_bv_neg(const Node& node, Node& child)
{
  Node one =
      NodeManager::get().mk_value(BitVector::mk_one(node.type().bv_size()));
  if (node.kind() == Kind::BV_NEG)
  {
    child = node[0];
    return true;
  }
  if (node.kind() == Kind::BV_ADD)
  {
    if (node[0] == one && node[1].is_inverted())
    {
      child = node[1][0];
      return true;
    }
    if (node[1] == one && node[0].is_inverted())
    {
      child = node[0][0];
      return true;
    }
    return false;
  }
  return false;
}

bool
is_bv_or(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_OR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_AND)
  {
    NodeManager& nm = NodeManager::get();
    child0 =
        node[0][0].is_inverted() ? node[0][0][0] : nm.invert_node(node[0][0]);
    child1 =
        node[0][1].is_inverted() ? node[0][1][0] : nm.invert_node(node[0][1]);
    return true;
  }
  return false;
}

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

bool
is_bv_sub(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_SUB)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.kind() == Kind::BV_ADD)
  {
    if (node::utils::is_bv_neg(node[0], child0))
    {
      child1 = node[1];
      return true;
    }
    if (node::utils::is_bv_neg(node[1], child1))
    {
      child0 = node[0];
      return true;
    }
  }
  return false;
}

bool
is_bv_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_XNOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.is_inverted() && node[0].kind() == Kind::BV_XOR)
  {
    child0 = node[0][0];
    child1 = node[0][1];
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

  if (s_node_kind_info.is_left_associative(kind))
  {
    Node res = nm.mk_node(kind, {terms[0], terms[1]});
    for (size_t i = 3; i < size; ++i)
    {
      res = nm.mk_node(kind, {res, terms[i]});
    }
    return res;
  }

  if (s_node_kind_info.is_right_associative(kind))
  {
    Node res = nm.mk_node(kind, {terms[size - 2], terms[size - 1]});
    for (size_t i = 3; i < size; ++i)
    {
      res = nm.mk_node(kind, {terms[size - i], res});
    }
    return res;
  }

  if (s_node_kind_info.is_chainable(kind))
  {
    Node res = nm.mk_node(kind, {terms[0], terms[1]});
    for (size_t i = 2; i < size; ++i)
    {
      res = nm.mk_node(node::Kind::AND,
                       {res, nm.mk_node(kind, {terms[i - 1], terms[i]})});
    }
    return res;
  }

  assert(s_node_kind_info.is_pairwise(kind));
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
    return nm.mk_node(Kind::LAMBDA, children);
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

}  // namespace bzla::node::utils
