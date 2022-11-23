#include "node/node_kind.h"

namespace bzla::node {

/* --- KindInfo public ------------------------------------------------------ */

uint8_t
KindInfo::num_children(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_num_children;
}

uint8_t
KindInfo::num_indices(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_num_indices;
}

const char*
KindInfo::enum_name(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_enum_name;
}

const char*
KindInfo::smt2_name(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_smt2_name;
}

bool
KindInfo::is_nary(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_num_children == KindInfo::s_nary;
}

bool
KindInfo::is_left_associative(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::LEFT_ASSOC;
}

bool
KindInfo::is_right_associative(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::RIGHT_ASSOC;
}

bool
KindInfo::is_chainable(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::CHAINABLE;
}

bool
KindInfo::is_pairwise(Kind kind) const
{
  return d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::PAIRWISE;
}

std::ostream&
operator<<(std::ostream& out, Kind kind)
{
  return out << s_node_kind_info.enum_name(kind);
}

}  // namespace bzla::node
