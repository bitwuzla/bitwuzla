#include "node/node_utils.h"

namespace bzla::node::utils {

bool
is_bv_xnor(const Node& node)
{
  return node.kind() == Kind::BV_NOT && node[0].kind() == Kind::BV_XOR;
}

}  // namespace bzla::node::utils
