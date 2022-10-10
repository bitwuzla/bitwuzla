#include "node/node_utils.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"

namespace bzla::node::utils {

bool
is_bv_xnor(const Node& node)
{
  return (node.kind() == Kind::BV_XNOR)
         || (node.kind() == Kind::BV_NOT && node[0].kind() == Kind::BV_XOR);
}

bool
is_bv_neg(const Node& node)
{
  Node one =
      NodeManager::get().mk_value(BitVector::mk_one(node.type().bv_size()));
  return node.kind() == Kind::BV_NEG
         || (node.kind() == Kind::BV_ADD
             && ((node[0] == one && node[1].kind() == Kind::BV_NOT)
                 || (node[1] == one && node[0].kind() == Kind::BV_NOT)));
}
}  // namespace bzla::node::utils
