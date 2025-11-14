#include "bitblast/aig/aig_node.h"

#include <cassert>

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
  assert(!other.is_null());
  data()->inc_refs();
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

void
AigNodeData::gc()
{
  d_mgr->garbage_collect(this);
}

}  // namespace bzla::bitblast
