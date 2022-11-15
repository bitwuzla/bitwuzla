#include "node/node_utils.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"

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
mk_nary(Kind kind, const std::vector<Node>& terms, bool left_assoc)
{
  assert(!terms.empty());
  if (terms.size() == 1)
  {
    return terms[0];
  }

  NodeManager& nm = NodeManager::get();
  size_t size     = terms.size();
  if (left_assoc)
  {
    Node res = nm.mk_node(kind, {terms[0], terms[1]});
    for (size_t i = 3; i < size; ++i)
    {
      res = nm.mk_node(kind, {res, terms[i]});
    }
    return res;
  }

  // Right-associative
  Node res = nm.mk_node(kind, {terms[size - 2], terms[size - 1]});
  for (size_t i = 3; i < size; ++i)
  {
    res = nm.mk_node(kind, {terms[size - i], res});
  }
  return res;
}

}  // namespace bzla::node::utils
