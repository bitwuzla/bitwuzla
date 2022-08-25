#ifndef BZLA_NODE_H_INCLUDED
#define BZLA_NODE_H_INCLUDED

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "node/node_kind.h"
#include "type/type.h"

namespace bzla::node {

/* --- Node ---------------------------------------------------------------- */

class NodeData;

class Node
{
  friend class NodeManager;

 public:
  using iterator = const Node*;

  Node() = default;
  ~Node();
  Node(const Node& other);
  Node& operator=(const Node& other);
  Node(Node&& other);
  Node& operator=(Node&& other);

  /** Return id of node. */
  uint64_t get_id() const;

  /** Return node kind. */
  Kind get_kind() const;

  /** Return type of node. */
  const type::Type& get_type() const;

  /** Check whether node is null. */
  bool is_null() const;

  /** Return the number of children. */
  size_t get_num_children() const;

  /**
   * Return child at position `index`.
   *
   * Only valid to call if get_num_children() > 0.
   */
  const Node& operator[](size_t index) const;

  /** Return number of indices. */
  size_t get_num_indices() const;

  /**
   * Return index at position `index`.
   *
   * Only valid to call if get_num_indices() > 0.
   */
  uint64_t get_index(size_t index) const;

  /** Comparison operators. */
  bool operator==(const Node& other) const;
  bool operator!=(const Node& other) const;

  /** Iterator for children. */
  iterator begin() const;
  iterator end() const;

 private:
  Node(NodeData* data);

  NodeData* d_data = nullptr;
};

}  // namespace bzla::node
#endif
