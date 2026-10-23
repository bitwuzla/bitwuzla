/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_UNIQUE_TABLE_H_INCLUDED
#define BZLA_NODE_NODE_UNIQUE_TABLE_H_INCLUDED

#include <span>
#include <vector>

#include "node/node_data.h"

namespace bzla::node {

class NodeUniqueTable
{
 public:
  NodeUniqueTable();
  ~NodeUniqueTable();

  /**
   * Find node with specified criteria. If node does not exist yet, allocates
   * new node data.
   */
  std::pair<bool, NodeData*> find_or_insert(Kind kind,
                                            const Type& type,
                                            const std::vector<Node>& children,
                                            std::span<const uint64_t> indices);

  /**
   * Find value with specified criteria. If node does not exist yet, allocates
   * new node data.
   */
  template <class T>
  std::pair<bool, NodeData*> find_or_insert(const Type& type, const T& value)
  {
    uint32_t t = tag(hash_value(value));
    size_t pos = find(t, [&](const NodeData* d) {
      return d->d_kind == Kind::VALUE && d->get_type() == type
             && d->payload_value<T>().d_value == value;
    });
    if (d_slots[pos].d_data)
    {
      return std::make_pair(false, d_slots[pos].d_data);
    }
    return std::make_pair(true, insert(pos, t, NodeData::alloc(value)));
  }

  /**
   * Delete node data from unique table. The hash value of values is
   * recomputed, nodes with children store their tag.
   */
  void erase(const NodeData* d);

 private:
  static constexpr std::array<size_t, 4> s_primes = {
      333444569u, 76891121u, 456790003u, 111130391u};

  /** Tables with fewer slots are doubled on resize. */
  static constexpr size_t s_double_max_size = size_t(1) << 18;

  /**
   * A slot of the hash table. The tag is stored in the slot to only access
   * node data on tag matches and to resize without accessing it.
   */
  struct Slot
  {
    uint32_t d_tag   = 0;
    NodeData* d_data = nullptr;
  };

  /**
   * Find the slot of the node data with the given tag that satisfies `equal`,
   * probing linearly from its home slot.
   * @return The position of the slot, or of the empty slot that ends the
   *         probe sequence if no such node data exists.
   */
  template <class Equal>
  size_t find(uint32_t tag, Equal&& equal) const
  {
    for (size_t i = position(tag);; i = next(i))
    {
      const Slot& slot = d_slots[i];
      if (slot.d_data == nullptr || (slot.d_tag == tag && equal(slot.d_data)))
      {
        return i;
      }
    }
  }

  /**
   * Insert node data into the empty slot at the given position, resizes the
   * table if necessary.
   * @return The inserted node data.
   */
  NodeData* insert(size_t pos, uint32_t tag, NodeData* d);

  /** Resizes unique table and reinserts node data. */
  void resize();

  /**
   * @return The tag of the given hash value. Fibonacci hashing mixes all bits
   *         of the hash value into the upper 32 bits, which form the tag.
   */
  static uint32_t tag(size_t hash)
  {
    return static_cast<uint32_t>(
        (static_cast<uint64_t>(hash) * UINT64_C(0x9e3779b97f4a7c15)) >> 32);
  }

  /** @return The home slot position of the given tag. */
  size_t position(uint32_t tag) const
  {
    assert(d_slots.size() <= UINT32_MAX);
    return static_cast<size_t>((static_cast<uint64_t>(tag) * d_slots.size())
                               >> 32);
  }

  /** @return The position after the given position, wrapping around. */
  size_t next(size_t pos) const
  {
    return pos + 1 == d_slots.size() ? 0 : pos + 1;
  }

  /** @return The distance from position `from` to position `to`. */
  size_t distance(size_t from, size_t to) const
  {
    return to >= from ? to - from : to + d_slots.size() - from;
  }

  /** Hash node data. */
  size_t hash(const NodeData* d) const;

  /** Compute hash value of node lookup data. */
  size_t hash(Kind kind,
              const std::vector<Node>& children,
              std::span<const uint64_t> indices) const;

  /** Compare node data against node lookup data. */
  bool equals(const NodeData& data,
              Kind kind,
              const Type& type,
              const std::vector<Node>& children,
              std::span<const uint64_t> indices) const;

  /** Compute has value of value node lookup data. */
  template <class T>
  size_t hash_value(const T& value)
  {
    return static_cast<size_t>(Kind::VALUE) + std::hash<T>{}(value);
  }

  inline size_t hash_children(size_t hash,
                              size_t size,
                              const Node* children) const
  {
    for (size_t i = 0; i < size; ++i)
    {
      // access node data directly, Node::id() is not inlined
      assert(children[i].d_data);
      hash += s_primes[i % s_primes.size()] * children[i].d_data->get_id();
    }
    return hash;
  }

  inline size_t hash_indices(size_t hash,
                             size_t size,
                             const uint64_t* indices) const
  {
    for (size_t i = 0; i < size; ++i)
    {
      hash += s_primes[i % s_primes.size()] * indices[i];
    }
    return hash;
  }

  /** Number of nodes stored in unique table. */
  size_t d_num_elements = 0;
  /** Hash table slots. */
  std::vector<Slot> d_slots;
};

}  // namespace bzla::node

#endif
