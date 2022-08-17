#include "node/node_data.h"

#include "node/node.h"
#include "node/node_manager.h"

namespace bzla::node {

size_t
NodeDataHash::operator()(const NodeData* d) const
{
  size_t hash = static_cast<size_t>(d->d_kind);
  for (size_t i = 0, size = d->get_num_children(); i < size; ++i)
  {
    hash += s_primes[i] * d->get_child(i).get_id();
  }
  for (size_t i = 0, size = d->get_num_indices(); i < size; ++i)
  {
    hash += s_primes[i] * d->get_index(i);
  }
  // TODO: values
  return hash;
}

bool
NodeDataKeyEqual::operator()(const NodeData* d0, const NodeData* d1) const
{
  if (d0->get_kind() != d1->get_kind()
      || d0->get_num_children() != d1->get_num_children()
      || d0->get_num_indices() != d1->get_num_indices())
  {
    return false;
  }
  for (size_t i = 0, size = d0->get_num_children(); i < size; ++i)
  {
    if (d0->get_child(i) != d1->get_child(i))
    {
      return false;
    }
  }
  for (size_t i = 0, size = d0->get_num_indices(); i < size; ++i)
  {
    if (d0->get_index(i) != d1->get_index(i))
    {
      return false;
    }
  }
  // TODO: values
  return true;
}

/* --- NodeData public ----------------------------------------------------- */

size_t
NodeData::get_num_children() const
{
  if (has_children())
  {
    const NodeDataChildren& data =
        reinterpret_cast<const NodeDataChildren&>(*this);
    return data.d_num_children;
  }
  return 0;
}

const Node&
NodeData::get_child(size_t index) const
{
  assert(has_children());
  assert(index < get_num_children());
  const NodeDataChildren& data =
      reinterpret_cast<const NodeDataChildren&>(*this);
  return data.d_children[index];
}

Node&
NodeData::get_child(size_t index)
{
  assert(has_children());
  assert(index < get_num_children());
  NodeDataChildren& data = reinterpret_cast<NodeDataChildren&>(*this);
  return data.d_children[index];
}

size_t
NodeData::get_num_indices() const
{
  if (is_indexed())
  {
    const NodeDataIndexed& data =
        reinterpret_cast<const NodeDataIndexed&>(*this);
    return data.d_num_indices;
  }
  return 0;
}

uint64_t
NodeData::get_index(size_t index) const
{
  assert(is_indexed());
  assert(index < get_num_indices());
  const NodeDataIndexed& data = reinterpret_cast<const NodeDataIndexed&>(*this);
  return data.d_indices[index];
}

void
NodeData::inc_ref()
{
  ++d_refs;
}

void
NodeData::dec_ref()
{
  assert(d_refs > 0);
  --d_refs;
  if (d_refs == 0)
  {
    d_mgr->garbage_collect(this);
  }
}

/* --- NodeData private ---------------------------------------------------- */

bool
NodeData::has_children() const
{
  return d_kind > Kind::UNARY_START;
}

bool
NodeData::is_indexed() const
{
  return d_kind == Kind::BV_EXTRACT || d_kind == Kind::FP_TO_UBV
         || d_kind == Kind::FP_TO_SBV || d_kind == Kind::FP_TO_FP_FP
         || d_kind == Kind::FP_TO_FP_SBV || d_kind == Kind::FP_TO_FP_UBV;
}

}  // namespace bzla::node
