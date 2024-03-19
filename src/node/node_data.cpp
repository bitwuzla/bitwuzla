/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_data.h"

#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"

namespace bzla::node {

/* --- NodeData public ----------------------------------------------------- */

NodeData*
NodeData::alloc(Kind kind,
                const std::vector<Node>& children,
                const std::vector<uint64_t>& indices)
{
  size_t size         = sizeof(NodeData);
  size_t payload_size = 0;

  if (!children.empty())
  {
    payload_size += sizeof(PayloadChildren);
    payload_size +=
        sizeof(PayloadChildren::d_children[0]) * (children.size() - 1);
  }

  if (!indices.empty())
  {
    payload_size += sizeof(PayloadIndexed);
    payload_size += sizeof(PayloadIndexed::d_indices[0]) * (indices.size() - 1);
  }

  NodeData* data = static_cast<NodeData*>(std::calloc(1, size + payload_size));
  if (data == nullptr)
  {
    throw std::bad_alloc();
  }
  data->d_kind = kind;
  data->d_hash = static_cast<size_t>(kind);

  // Connect children payload
  if (!children.empty())
  {
    auto& payload = data->payload_children();
    assert(payload.d_num_children == 0);
    for (auto n : children)
    {
      assert(!n.is_null());
      payload.d_children[payload.d_num_children++] = n;
    }
    assert(payload.d_num_children == children.size());

    auto& hash = data->d_hash;
    for (size_t i = 0; i < payload.d_num_children; ++i)
    {
      hash += NodeDataHash::s_primes[i % NodeDataHash::s_primes.size()]
              * payload.d_children[i].id();
    }
  }

  // Connect indices payload
  if (!indices.empty())
  {
    auto& payload = data->payload_indexed();
    assert(payload.d_num_indices == 0);
    for (auto i : indices)
    {
      payload.d_indices[payload.d_num_indices++] = i;
    }
    assert(payload.d_num_indices == indices.size());

    auto& hash = data->d_hash;
    for (size_t i = 0; i < payload.d_num_indices; ++i)
    {
      hash += NodeDataHash::s_primes[i % NodeDataHash::s_primes.size()]
              * payload.d_indices[i];
    }
  }

  return data;
}

void
NodeData::dealloc(NodeData* data)
{
  std::free(data);
}

NodeData::~NodeData()
{
  if (has_children())
  {
    auto& payload_c = payload_children();
    for (size_t i = 0, size = payload_c.d_num_children; i < size; ++i)
    {
      payload_c.d_children[i].~Node();
    }
  }
  else if (d_kind == Kind::VALUE)
  {
    if (d_type.is_bv())
    {
      auto& payload = payload_value<BitVector>();
      payload.d_value.~BitVector();
    }
    else if (d_type.is_fp())
    {
      auto& payload = payload_value<FloatingPoint>();
      payload.d_value.~FloatingPoint();
    }
  }
}

size_t
NodeData::hash() const
{
  return d_hash;
}

bool
NodeData::equals(const NodeData& other) const
{
  if (d_kind != other.d_kind)
  {
    return false;
  }

  if (has_children())
  {
    assert(other.has_children());
    const auto& payload       = payload_children();
    const auto& payload_other = other.payload_children();

    if (payload.d_num_children != payload_other.d_num_children)
    {
      return false;
    }

    for (size_t i = 0, size = payload.d_num_children; i < size; ++i)
    {
      if (payload.d_children[i] != payload_other.d_children[i])
      {
        return false;
      }
    }

    // Constant arrays are a special case since they require the type info.
    if (get_kind() == Kind::CONST_ARRAY)
    {
      // not needed anymore?
      assert(!get_type().is_null());
      assert(!other.get_type().is_null());
      return get_type() == other.get_type();
    }
  }

  if (is_indexed())
  {
    assert(other.is_indexed());
    const auto& payload       = payload_indexed();
    const auto& payload_other = other.payload_indexed();

    if (payload.d_num_indices != payload_other.d_num_indices)
    {
      return false;
    }

    for (size_t i = 0, size = payload.d_num_indices; i < size; ++i)
    {
      if (payload.d_indices[i] != payload_other.d_indices[i])
      {
        return false;
      }
    }
  }

  if (get_kind() == Kind::VALUE)
  {
    assert(!d_type.is_null());
    assert(!other.d_type.is_null());
    if (get_type() != other.get_type())
    {
      return false;
    }

    if (d_type.is_bool())
    {
      return get_value<bool>() == other.get_value<bool>();
    }
    else if (d_type.is_bv())
    {
      return get_value<BitVector>() == other.get_value<BitVector>();
    }
    else if (d_type.is_rm())
    {
      return get_value<RoundingMode>() == other.get_value<RoundingMode>();
    }
    else
    {
      assert(d_type.is_fp());
      return get_value<FloatingPoint>() == other.get_value<FloatingPoint>();
    }
  }

  return true;
}

bool
NodeData::has_children() const
{
  return KindInfo::num_children(d_kind) > 0;
}

size_t
NodeData::get_num_children() const
{
  if (has_children())
  {
    const auto& payload = payload_children();
    return payload.d_num_children;
  }
  return 0;
}

const Node&
NodeData::get_child(size_t index) const
{
  assert(has_children());
  assert(index < get_num_children());
  const auto& payload = payload_children();
  return payload.d_children[index];
}

Node&
NodeData::get_child(size_t index)
{
  assert(has_children());
  assert(index < get_num_children());
  auto& payload = payload_children();
  return payload.d_children[index];
}

bool
NodeData::is_indexed() const
{
  return KindInfo::num_indices(d_kind) > 0;
}

size_t
NodeData::get_num_indices() const
{
  if (is_indexed())
  {
    const auto& payload = payload_indexed();
    return payload.d_num_indices;
  }
  return 0;
}

uint64_t
NodeData::get_index(size_t index) const
{
  assert(is_indexed());
  assert(index < get_num_indices());
  const auto& payload = payload_indexed();
  return payload.d_indices[index];
}

std::optional<std::reference_wrapper<const std::string>>
NodeData::get_symbol() const
{
  return d_nm->get_symbol(this);
}

NodeData::iterator
NodeData::begin() const
{
  if (has_children())
  {
    const auto& payload = payload_children();
    return payload.d_children;
  }
  return nullptr;
}

NodeData::iterator
NodeData::end() const
{
  if (has_children())
  {
    const auto& payload = payload_children();
    return payload.d_children + payload.d_num_children;
  }
  return nullptr;
}

void
NodeData::gc()
{
  d_nm->garbage_collect(this);
}

}  // namespace bzla::node
