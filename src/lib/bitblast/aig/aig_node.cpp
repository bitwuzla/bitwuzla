#include "bitblast/aig/aig_node.h"

#include <cassert>

#include "bitblast/aig/aig_manager.h"

namespace bzla::bitblast {

AigNode::AigNode(AigNodeData* data, bool negated)
    : d_data(data), d_negated(negated)
{
  d_data->inc_refs();
}

AigNode::~AigNode()
{
  if (!is_null())
  {
    d_data->dec_refs();
  }
}

AigNode::AigNode(const AigNode& other)
    : d_data(other.d_data), d_negated(other.d_negated)
{
  assert(!other.is_null());
  d_data->inc_refs();
}

AigNode&
AigNode::operator=(const AigNode& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data    = other.d_data;
  d_negated = other.d_negated;
  d_data->inc_refs();
  return *this;
}

AigNode::AigNode(AigNode&& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data       = other.d_data;
  d_negated    = other.d_negated;
  other.d_data = nullptr;
}

AigNode&
AigNode::operator=(AigNode&& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data       = other.d_data;
  d_negated    = other.d_negated;
  other.d_data = nullptr;
  return *this;
}

void
AigNodeData::gc()
{
  d_mgr->garbage_collect(this);
}

}  // namespace bzla::bitblast
