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
NodeData::alloc(Kind kind, const std::optional<std::string>& symbol)
{
  size_t size = sizeof(NodeData) + sizeof(PayloadSymbol);

  NodeData* data = static_cast<NodeData*>(std::calloc(1, size));
  if (data == nullptr)
  {
    throw std::bad_alloc();
  }
  data->d_kind     = kind;
  auto& payload    = data->payload_symbol();
  payload.d_symbol = symbol;
  return data;
}

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

  // Connect children payload
  if (!children.empty())
  {
    auto& payload = data->payload_children();
    assert(payload.d_num_children == 0);
    for (size_t i = 0, size = children.size(); i < size; ++i)
    {
      assert(!children[i].is_null());
      payload.d_children[i] = children[i];
      data->d_info.set(children[i].node_info());
    }
    payload.d_num_children = children.size();

    if (kind == Kind::FORALL || kind == Kind::EXISTS)
    {
      data->info().quantifier = 1;
    }
    else if (kind == Kind::LAMBDA)
    {
      data->info().lambda = 1;
    }
  }

  // Connect indices payload
  if (!indices.empty())
  {
    auto& payload = data->payload_indexed();
    assert(payload.d_num_indices == 0);
    for (size_t i = 0, size = indices.size(); i < size; ++i)
    {
      payload.d_indices[i] = indices[i];
    }
    payload.d_num_indices = indices.size();
  }

  return data;
}

void
NodeData::dealloc(NodeData* data)
{
  data->~NodeData();
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
  else if (d_kind == Kind::CONSTANT || d_kind == Kind::VALUE)
  {
    auto& payload = payload_symbol();
    payload.d_symbol.~optional();
  }
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
