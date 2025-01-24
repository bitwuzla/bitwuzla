#include "bitblast/aig/aig_node.h"

#include <cassert>
#include <sstream>

#include "bitblast/aig/aig_manager.h"

namespace bzla::bitblast {

AigNode::AigNode(AigNodeData* d, bool negated)
    : d_data(reinterpret_cast<uintptr_t>(d))
{
  assert(d);
  if (negated)
  {
    d_data |= 1;
  }
  data()->inc_refs();
}

AigNode::~AigNode()
{
  if (!is_null())
  {
    data()->dec_refs();
  }
}

AigNode::AigNode(const AigNode& other) : d_data(other.d_data)
{
  if (!is_null())
  {
    data()->inc_refs();
  }
}

AigNode&
AigNode::operator=(const AigNode& other)
{
  if (!is_null())
  {
    data()->dec_refs();
  }
  d_data = other.d_data;
  data()->inc_refs();
  return *this;
}

AigNode::AigNode(AigNode&& other)
{
  if (!is_null())
  {
    data()->dec_refs();
  }
  d_data       = other.d_data;
  other.d_data = 0;
}

AigNode&
AigNode::operator=(AigNode&& other)
{
  if (!is_null())
  {
    data()->dec_refs();
  }
  d_data       = other.d_data;
  other.d_data = 0;
  return *this;
}

std::string
AigNode::str() const
{
  std::stringstream ss;
  ss << get_id() << ": ";
  if (is_null())
  {
    ss << "(nil)";
  }
  else if (is_true())
  {
    ss << "true";
  }
  else if (is_false())
  {
    ss << "false";
  }
  else if (is_const())
  {
    ss << "const";
  }
  else
  {
    ss << (*this)[0].get_id() << " " << (*this)[1].get_id();
  }
  return ss.str();
}

void
AigNodeData::gc()
{
  d_mgr->garbage_collect(this);
}

std::ostream&
operator<<(std::ostream& out, const AigNode& aig)
{
  out << aig.str();
  return out;
}
}  // namespace bzla::bitblast
