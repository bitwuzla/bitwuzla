#include "node/node_data.h"

#include "node/node.h"
#include "node/node_manager.h"

namespace bzla::node {

size_t
NodeDataHash::operator()(const NodeData* d) const
{
  return d->hash();
}

bool
NodeDataKeyEqual::operator()(const NodeData* d0, const NodeData* d1) const
{
  return d0->equals(*d1);
}

/* --- NodeData public ----------------------------------------------------- */

NodeData::NodeData(NodeManager* mgr, Kind kind) : d_mgr(mgr), d_kind(kind){};

size_t
NodeData::hash() const
{
  return static_cast<size_t>(d_kind);
}

bool
NodeData::equals(const NodeData& other) const
{
  (void) other;
  return d_kind == other.d_kind;
}

bool
NodeData::has_children() const
{
  return s_node_kind_info[d_kind].num_children > 0;
}

size_t
NodeData::get_num_children() const
{
  if (has_children())
  {
    if (is_nary())
    {
      const NodeDataNary& data = reinterpret_cast<const NodeDataNary&>(*this);
      return data.d_children.size();
    }
    else
    {
      const NodeDataChildren& data =
          reinterpret_cast<const NodeDataChildren&>(*this);
      return data.d_num_children;
    }
  }
  return 0;
}

const Node&
NodeData::get_child(size_t index) const
{
  assert(has_children());
  assert(index < get_num_children());
  if (is_nary())
  {
    const NodeDataNary& data = reinterpret_cast<const NodeDataNary&>(*this);
    return data.d_children[index];
  }
  const NodeDataChildren& data =
      reinterpret_cast<const NodeDataChildren&>(*this);
  return data.d_children[index];
}

Node&
NodeData::get_child(size_t index)
{
  assert(has_children());
  assert(index < get_num_children());
  if (is_nary())
  {
    NodeDataNary& data = reinterpret_cast<NodeDataNary&>(*this);
    return data.d_children[index];
  }
  NodeDataChildren& data = reinterpret_cast<NodeDataChildren&>(*this);
  return data.d_children[index];
}

bool
NodeData::is_indexed() const
{
  return s_node_kind_info[d_kind].num_indices > 0;
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

bool
NodeData::is_nary() const
{
  return s_node_kind_info[d_kind].num_children == KindInformation::s_nary;
}

std::optional<std::reference_wrapper<const std::string>>
NodeData::get_symbol() const
{
  return d_mgr->get_symbol(this);
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

NodeData::iterator
NodeData::begin() const
{
  if (has_children())
  {
    if (is_nary())
    {
      const NodeDataNary& data = reinterpret_cast<const NodeDataNary&>(*this);
      return data.d_children.data();
    }
    const NodeDataChildren& data =
        reinterpret_cast<const NodeDataChildren&>(*this);
    return data.d_children.begin();
  }
  return nullptr;
}

NodeData::iterator
NodeData::end() const
{
  if (has_children())
  {
    if (is_nary())
    {
      const NodeDataNary& data = reinterpret_cast<const NodeDataNary&>(*this);
      return data.d_children.data() + data.d_children.size();
    }
    const NodeDataChildren& data =
        reinterpret_cast<const NodeDataChildren&>(*this);
    return data.d_children.begin() + data.d_num_children;
  }
  return nullptr;
}

/* --- NodeDataChildren public --------------------------------------------- */

NodeDataChildren::NodeDataChildren(NodeManager* mgr,
                                   Kind kind,
                                   const std::vector<Node>& children)
    : NodeData(mgr, kind), d_num_children(children.size())
{
  assert(d_num_children > 0);
  assert(d_num_children <= s_max_children);
  assert(s_node_kind_info[kind].num_children > 0);
  uint8_t i = 0;
  for (auto n : children)
  {
    assert(!n.is_null());
    d_children[i++] = n;
  }
  assert(i == d_num_children);
};

size_t
NodeDataChildren::hash() const
{
  size_t hash = NodeData::hash();
  for (size_t i = 0; i < d_num_children; ++i)
  {
    hash += NodeDataHash::s_primes[i] * d_children[i].id();
  }
  return hash;
}

bool
NodeDataChildren::equals(const NodeData& other) const
{
  if (!NodeData::equals(other))
  {
    return false;
  }
  assert(other.has_children());
  const NodeDataChildren& o = reinterpret_cast<const NodeDataChildren&>(other);
  if (d_num_children != o.d_num_children)
  {
    return false;
  }
  for (size_t i = 0; i < d_num_children; ++i)
  {
    if (d_children[i] != o.d_children[i])
    {
      return false;
    }
  }
  return true;
}

/* --- NodeDataIndexed public ---------------------------------------------- */

NodeDataIndexed::NodeDataIndexed(NodeManager* mgr,
                                 Kind kind,
                                 const std::vector<Node>& children,
                                 const std::vector<uint64_t>& indices)
    : NodeDataChildren(mgr, kind, children), d_num_indices(indices.size())
{
  assert(s_node_kind_info[kind].num_indices == indices.size());
  uint8_t i = 0;
  for (auto idx : indices)
  {
    d_indices[i++] = idx;
  }
  assert(i == d_num_indices);
};

size_t
NodeDataIndexed::hash() const
{
  size_t hash = NodeDataChildren::hash();
  for (size_t i = 0; i < d_num_indices; ++i)
  {
    hash += NodeDataHash::s_primes[i] * d_indices[i];
  }
  return hash;
}

bool
NodeDataIndexed::equals(const NodeData& other) const
{
  if (!NodeDataChildren::equals(other))
  {
    return false;
  }
  assert(other.is_indexed());
  const NodeDataIndexed& o = reinterpret_cast<const NodeDataIndexed&>(other);
  assert(d_num_indices == o.d_num_indices);
  for (size_t i = 0; i < d_num_indices; ++i)
  {
    if (d_indices[i] != o.d_indices[i])
    {
      return false;
    }
  }
  return true;
}

/* --- NodeDataNary public ------------------------------------------------- */

NodeDataNary::NodeDataNary(NodeManager* mgr,
                           Kind kind,
                           const std::vector<Node>& children)
    : NodeData(mgr, kind), d_children(children)
{
  assert(is_nary());
};

size_t
NodeDataNary::hash() const
{
  size_t hash = NodeData::hash();
  for (size_t i = 0, size = d_children.size(); i < size; ++i)
  {
    hash += NodeDataHash::s_primes[i % sizeof(NodeDataHash::s_primes)]
            * d_children[i].id();
  }
  return hash;
}

bool
NodeDataNary::equals(const NodeData& other) const
{
  if (!NodeData::equals(other))
  {
    return false;
  }
  assert(other.is_nary());
  const NodeDataNary& o = reinterpret_cast<const NodeDataNary&>(other);
  if (d_children.size() != o.d_children.size())
  {
    return false;
  }
  for (size_t i = 0, size = d_children.size(); i < size; ++i)
  {
    if (d_children[i] != o.d_children[i])
    {
      return false;
    }
  }
  return true;
}

}  // namespace bzla::node
