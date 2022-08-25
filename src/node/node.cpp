#include "node/node.h"

#include <array>
#include <cassert>
#include <iterator>

#include "node/node_data.h"
#include "node/node_manager.h"

namespace bzla::node {

/* --- Node public --------------------------------------------------------- */

Node::~Node()
{
  if (!is_null())
  {
    assert(d_data);
    d_data->dec_ref();
  }
}

Node::Node(const Node& other) : d_data(other.d_data)
{
  if (d_data)
  {
    d_data->inc_ref();
  }
}

Node&
Node::operator=(const Node& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  if (other.d_data)
  {
    d_data = other.d_data;
    d_data->inc_ref();
  }
  return *this;
}

Node::Node(Node&& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  d_data       = other.d_data;
  other.d_data = nullptr;
}

Node&
Node::operator=(Node&& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  d_data       = other.d_data;
  other.d_data = nullptr;
  return *this;
}

uint64_t
Node::get_id() const
{
  if (d_data)
  {
    return d_data->get_id();
  }
  return 0;
}

Kind
Node::get_kind() const
{
  if (is_null())
  {
    return Kind::NULL_NODE;
  }
  return d_data->get_kind();
}

const type::Type&
Node::get_type() const
{
  assert(!is_null());
  return d_data->get_type();
}

bool
Node::is_null() const
{
  return d_data == nullptr;
}

bool
Node::operator==(const Node& other) const
{
  return d_data == other.d_data;
}

bool
Node::operator!=(const Node& other) const
{
  return d_data != other.d_data;
}

size_t
Node::get_num_children() const
{
  if (is_null())
  {
    return 0;
  }
  return d_data->get_num_children();
}

const Node&
Node::operator[](size_t index) const
{
  assert(d_data != nullptr);
  return d_data->get_child(index);
}

size_t
Node::get_num_indices() const
{
  assert(!is_null());
  return d_data->get_num_indices();
}

uint64_t
Node::get_index(size_t index) const
{
  assert(!is_null());
  assert(get_num_indices() > 0);
  return d_data->get_index(index);
}

Node::iterator
Node::begin() const
{
  if (!is_null() && d_data->has_children())
  {
    const NodeDataChildren& data =
        reinterpret_cast<const NodeDataChildren&>(*d_data);
    return data.d_children.begin();
  }
  return nullptr;
}

Node::iterator
Node::end() const
{
  if (!is_null() && d_data->has_children())
  {
    const NodeDataChildren& data =
        reinterpret_cast<const NodeDataChildren&>(*d_data);
    return data.d_children.begin() + data.d_num_children;
  }
  return nullptr;
}

/* --- Node private -------------------------------------------------------- */

Node::Node(NodeData* data) : d_data(data)
{
  assert(data != nullptr);
  d_data->inc_ref();
};

}  // namespace bzla::node
