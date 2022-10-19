#include "node/node_utils.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"

namespace bzla::node::utils {

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

}  // namespace bzla::node::utils
