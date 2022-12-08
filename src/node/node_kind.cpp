#include "node/node_kind.h"

#include "node/kind_info.h"

namespace bzla::node {

std::ostream&
operator<<(std::ostream& out, Kind kind)
{
  return out << KindInfo::enum_name(kind);
}

}  // namespace bzla::node
