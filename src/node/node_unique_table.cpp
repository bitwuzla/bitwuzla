/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_unique_table.h"

#include "solver/fp/floating_point.h"

namespace bzla::node {

/* --- NodeUniqueTable public ----------------------------------------------- */

NodeUniqueTable::NodeUniqueTable() : d_slots(16) {}

NodeUniqueTable::~NodeUniqueTable()
{
  // `NodeManager::release` defers destruction until the last `NodeData` is
  // freed, so all hash-consed nodes are already gone by the time we run.
  assert(d_num_elements == 0);
}

std::pair<bool, NodeData*>
NodeUniqueTable::find_or_insert(Kind kind,
                                const Type& type,
                                const std::vector<Node>& children,
                                std::span<const uint64_t> indices)
{
  assert(kind != Kind::VALUE);

  uint32_t t = tag(hash(kind, children, indices));
  size_t pos = find(t, [&](const NodeData* d) {
    return equals(*d, kind, type, children, indices);
  });
  if (d_slots[pos].d_data)
  {
    return std::make_pair(false, d_slots[pos].d_data);
  }
  return std::make_pair(
      true, insert(pos, t, NodeData::alloc(kind, children, indices, t)));
}

void
NodeUniqueTable::erase(const NodeData* d)
{
  // Nodes with children store their tag, which avoids accessing the children
  // before the slot.
  uint32_t t =
      d->get_kind() == Kind::VALUE ? tag(hash(d)) : d->payload_children().d_tag;
  assert(t == tag(hash(d)));
  size_t i = find(t, [d](const NodeData* cur) { return cur == d; });
  assert(d_slots[i].d_data == d);

  // Backward shift deletion: Move node data further down the probe sequence
  // into the free slot if the free slot is between its home slot and its slot.
  for (size_t j = next(i); d_slots[j].d_data; j = next(j))
  {
    if (distance(position(d_slots[j].d_tag), j) >= distance(i, j))
    {
      d_slots[i] = d_slots[j];
      i          = j;
    }
  }
  d_slots[i] = Slot();
  --d_num_elements;
}

/* --- NodeUniqueTable private ---------------------------------------------- */

NodeData*
NodeUniqueTable::insert(size_t pos, uint32_t tag, NodeData* d)
{
  assert(d_slots[pos].d_data == nullptr);
  // Keep the load factor at most 7/8 to keep probe sequences short.
  if (8 * (d_num_elements + 1) > 7 * d_slots.size())
  {
    resize();
    pos = find(tag, [](const NodeData*) { return false; });
  }
  d_slots[pos] = {tag, d};
  ++d_num_elements;
  return d;
}

void
NodeUniqueTable::resize()
{
  // Double small tables to keep the number of moved slots low, but grow large
  // tables by a factor of 1.5 to keep them close to the maximum load factor.
  size_t size = d_slots.size();
  std::vector<Slot> slots(size < s_double_max_size ? 2 * size
                                                   : size + size / 2);
  std::swap(slots, d_slots);

  for (const Slot& slot : slots)
  {
    if (slot.d_data)
    {
      d_slots[find(slot.d_tag, [](const NodeData*) { return false; })] = slot;
    }
  }
}

size_t
NodeUniqueTable::hash(const NodeData* d) const
{
  size_t hash = static_cast<size_t>(d->get_kind());

  if (d->get_kind() == Kind::VALUE)
  {
    const Type& t = d->get_type();
    if (t.is_bool())
    {
      const auto& payload = d->payload_value<bool>();
      hash += std::hash<bool>{}(payload.d_value);
    }
    else if (t.is_bv())
    {
      const auto& payload = d->payload_value<BitVector>();
      hash += std::hash<BitVector>{}(payload.d_value);
    }
    else if (t.is_rm())
    {
      const auto& payload = d->payload_value<RoundingMode>();
      hash += std::hash<RoundingMode>{}(payload.d_value);
    }
    else if (t.is_fp())
    {
      const auto& payload = d->payload_value<FloatingPoint>();
      hash += std::hash<FloatingPoint>{}(payload.d_value);
    }
    else if (t.is_uninterpreted())
    {
      const auto& payload = d->payload_value<std::string>();
      hash += std::hash<std::string>{}(payload.d_value);
    }
    else
    {
      assert(false);
    }
  }
  else
  {
    assert(d->has_children());
    const auto& payload = d->payload_children();
    hash = hash_children(hash, payload.d_num_children, payload.d_children);

    if (d->is_indexed())
    {
      const auto& payload = d->payload_indexed();
      hash = hash_indices(hash, payload.d_num_indices, payload.d_indices);
    }
  }

  return hash;
}

size_t
NodeUniqueTable::hash(Kind kind,
                      const std::vector<Node>& children,
                      std::span<const uint64_t> indices) const
{
  assert(!children.empty());

  size_t hash = static_cast<size_t>(kind);

  hash = hash_children(hash, children.size(), children.data());
  if (!indices.empty())
  {
    hash = hash_indices(hash, indices.size(), indices.data());
  }

  return hash;
}

bool
NodeUniqueTable::equals(const NodeData& data,
                        Kind kind,
                        const Type& type,
                        const std::vector<Node>& children,
                        std::span<const uint64_t> indices) const
{
  assert(kind != Kind::VALUE);

  if (data.d_kind != kind)
  {
    return false;
  }

  if (!children.empty())
  {
    assert(data.has_children());
    const auto& payload = data.payload_children();

    size_t num_children = children.size();
    if (payload.d_num_children != num_children)
    {
      return false;
    }

    for (size_t i = 0; i < num_children; ++i)
    {
      // compare node data directly, operator!= is not inlined
      if (payload.d_children[i].d_data != children[i].d_data)
      {
        return false;
      }
    }

    // Constant arrays are a special case since they require the type info.
    if (kind == Kind::CONST_ARRAY)
    {
      assert(!data.get_type().is_null());
      assert(!type.is_null());
      return data.get_type() == type;
    }
  }

  if (!indices.empty())
  {
    assert(data.is_indexed());
    const auto& payload = data.payload_indexed();

    size_t num_indices = payload.d_num_indices;
    if (num_indices != indices.size())
    {
      return false;
    }

    for (size_t i = 0; i < num_indices; ++i)
    {
      if (payload.d_indices[i] != indices[i])
      {
        return false;
      }
    }
  }

  return true;
}

}  // namespace bzla::node
