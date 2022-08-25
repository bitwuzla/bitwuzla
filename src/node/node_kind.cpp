#include "node/node_kind.h"

namespace bzla::node {

std::ostream&
operator<<(std::ostream& out, Kind kind)
{
  return out << s_node_kind_info[kind].enum_name;
}

}  // namespace bzla::node
