#include "node/node_utils.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"

namespace bzla::node::utils {

bool
is_bv_xnor(const Node& node, Node& child0, Node& child1)
{
  if (node.kind() == Kind::BV_XNOR)
  {
    child0 = node[0];
    child1 = node[1];
    return true;
  }

  if (node.kind() == Kind::BV_NOT && node[0].kind() == Kind::BV_XOR)
  {
    child0 = node[0][0];
    child1 = node[0][1];
    return true;
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
    if (node[0] == one && node[1].kind() == Kind::BV_NOT)
    {
      child = node[1][0];
      return true;
    }
    if (node[1] == one && node[0].kind() == Kind::BV_NOT)
    {
      child = node[0][0];
      return true;
    }
    return false;
  }
  return false;
}
}  // namespace bzla::node::utils
