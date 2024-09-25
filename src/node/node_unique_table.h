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
  std::pair<bool, NodeData*> find_or_insert(
      Kind kind,
      const Type& type,
      const std::vector<Node>& children,
      const std::vector<uint64_t>& indices);

  /**
   * Find value with specified criteria. If node does not exist yet, allocates
   * new node data.
   */
  template <class T>
  std::pair<bool, NodeData*> find_or_insert(const Type& type, const T& value)
  {
    size_t hd     = hash_value(value);
    size_t h      = bucket_hash(hd);
    NodeData* cur = d_buckets[h];

    // Check collision chain.
    while (cur)
    {
      if (cur->d_kind == Kind::VALUE && cur->get_type() == type)
      {
        const auto& payload = cur->payload_value<T>();
        if (payload.d_value == value)
        {
          return std::make_pair(false, cur);
        }
      }
      cur = cur->d_next;
    }

    // Create new node and insert
    NodeData* d = NodeData::alloc(value);
    if (needs_resize())
    {
      resize();
      h = bucket_hash(hd);
    }
    assert(d->d_next == nullptr);
    d->d_next    = d_buckets[h];
    d_buckets[h] = d;

    ++d_num_elements;
    return std::make_pair(true, d);
  }

  /** Delete node data from unique table. */
  void erase(const NodeData* d);

 private:
  static constexpr std::array<size_t, 4> s_primes = {
      333444569u, 76891121u, 456790003u, 111130391u};

  /** Check whether unique table needs to be resized. */
  bool needs_resize() const { return d_num_elements >= d_buckets.capacity(); }

  /** Resizes unique table and rehashes node data. */
  void resize();

  /** Hash node data. */
  size_t hash(const NodeData* d) const;

  /** Compute hash value of node lookup data. */
  size_t hash(Kind kind,
              const std::vector<Node>& children,
              const std::vector<uint64_t>& indices) const;

  /** Compare node data against node lookup data. */
  bool equals(const NodeData& data,
              Kind kind,
              const Type& type,
              const std::vector<Node>& children,
              const std::vector<uint64_t>& indices) const;

  /** Compute position in d_buckets based on hash value. */
  size_t bucket_hash(size_t hash, size_t mask = 0) const
  {
    if (mask == 0)
    {
      mask = d_buckets.capacity() - 1;
    }
    return hash & mask;
  }

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
      hash += s_primes[i % s_primes.size()] * children[i].id();
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
  /** Hash table buckets. */
  std::vector<NodeData*> d_buckets;
};

}  // namespace bzla::node

#endif
