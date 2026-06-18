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
  // Increment other's reference count before decrementing our own. This guards
  // against (1) other being a null (default-constructed) AigNode, in which case
  // there is no reference to increment, and (2) self-assignment where we hold
  // the last reference, in which case decrementing first would garbage collect
  // the data and turn the subsequent access into a use-after-free.
  if (!other.is_null())
  {
    other.data()->inc_refs();
  }
  if (!is_null())
  {
    data()->dec_refs();
  }
  d_data = other.d_data;
  return *this;
}

AigNode::AigNode(AigNode&& other) noexcept
{
  d_data       = other.d_data;
  other.d_data = 0;
}

AigNode&
AigNode::operator=(AigNode&& other) noexcept
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
