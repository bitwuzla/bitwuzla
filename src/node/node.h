/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_H_INCLUDED
#define BZLA_NODE_NODE_H_INCLUDED

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>

#include "node/node_kind.h"
#include "type/type.h"

namespace bzla {

class BitVector;
class NodeManager;

enum class RoundingMode;
class FloatingPoint;

namespace node {
class NodeData;
class NodeUniqueTable;

/**
 * Node info flags.
 *
 * Indicate whether a node with a given kind is below this node.
 */
struct NodeInfo
{
  uint8_t quantifier : 1;  // Is EXISTS/FORALL node below?
  uint8_t lambda : 1;      // Is LAMBDA node below?

  NodeInfo() : quantifier(0), lambda(0) {}

  void set(const NodeInfo& info)
  {
    quantifier |= info.quantifier;
    lambda |= info.lambda;
  }
};

}  // namespace node

/* --- Node ---------------------------------------------------------------- */

class Node
{
  friend NodeManager;
  friend node::NodeUniqueTable;
  friend bool operator==(const Node& a, const Node& b);
  friend bool operator!=(const Node& a, const Node& b);

 public:
  using iterator = const Node*;
  using reverse_iterator = std::reverse_iterator<const Node*>;

  Node() = default;
  ~Node();
  Node(const Node& other);
  Node& operator=(const Node& other);
  Node(Node&& other);
  Node& operator=(Node&& other);

  /**
   * @return The id of this node.
   */
  uint64_t id() const;

  /**
   * @return The kind of this node.
   */
  node::Kind kind() const;

  /**
   * @return The type of this node.
   */
  const Type& type() const;

  /**
   * @return True if this node is null.
   */
  bool is_null() const { return d_data == nullptr; }

  /**
   * @return True if this node is a value.
   */
  bool is_value() const;

  /**
   * @return True if this node is a first order constant.
   */
  bool is_const() const;

  /**
   * @return True if this node is a variable.
   */
  bool is_variable() const;

  /**
   * @return True if this node is a NOT or BV_NOT node.
   */
  bool is_inverted() const;

  /**
   * @return The number of children.
   */
  size_t num_children() const;

  /**
   * Return child at position `index`.
   *
   * @note Only valid to call if num_children() > 0.
   *
   * @param index The position of the child.
   * @return The child node at position `index`.
   */
  const Node& operator[](size_t index) const;

  /**
   * @return The number of indices of this node.
   */
  size_t num_indices() const;

  /**
   * Return index at position `index`.
   *
   * @note Only valid to call if num_indices() > 0.
   *
   * @param index The position of the index.
   * @return The index.
   */
  uint64_t index(size_t index) const;

  /**
   * Return the indices as a vector.
   *
   * @note This does not return a reference since internally we store an
   *       std::array for the indices and we have to explicitly create a vector
   *       from it.
   *
   * @return The indices.
   */
  std::vector<uint64_t> indices() const;

  /**
   * Get the value represented by this node.
   *
   * @return The value of type T.
   */
  template <class T>
  const T& value() const;

  /**
   * @return Symbol of this node or empty string if node does not have a symbol.
   */
  std::optional<std::reference_wrapper<const std::string>> symbol() const;

  /**
   * @return An iterator to the first child of this node.
   */
  iterator begin() const;

  /**
   * @return An iterator to the end of the children list of this node.
   */
  iterator end() const;

  /**
   * @return Beginning of the reverse iterator.
   */
  reverse_iterator rbegin() const;

  /**
   * @return End of the reverse iterator.
   */
  reverse_iterator rend() const;

  /**
   * Get the string representation of this node.
   * @note Floating-point values are represented in terms of operator `fp`.
   *       Their component bit-vector values can only be printed in binary or
   *       decimal format. If base `16` is configured, the format for
   *       floating-point component bit-vector values defaults to binary format.
   * @param base The base of the string representation of bit-vector values;
   *             `2` for binary, `10` for decimal, and `16` for hexadecimal.
   * @return String representation of this node.
   */
  std::string str(uint8_t base = 2) const;

  /** @return Associated node manager instance. */
  NodeManager* nm();
  const NodeManager* nm() const;

  const node::NodeData* payload() const { return d_data; }

  /** @return Node info flags. */
  const node::NodeInfo& node_info() const;

 private:
  Node(node::NodeData* data);

  /** Node payload. */
  node::NodeData* d_data = nullptr;
};

using ConstNodeRef = std::reference_wrapper<const Node>;

/** Syntactical equality over two nodes. */
bool operator==(const Node& a, const Node& b);
/** Syntactical disequality over two nodes. */
bool operator!=(const Node& a, const Node& b);
/** Compare nodes by node id. */
bool operator<(const Node& a, const Node& b);

/** Print node to stream. */
std::ostream& operator<<(std::ostream& out, const Node& node);

// Node:: value() instantiations for different value types
template <>
const bool& Node::value() const;
template <>
const BitVector& Node::value() const;
template <>
const RoundingMode& Node::value() const;
template <>
const FloatingPoint& Node::value() const;

}  // namespace bzla

namespace std {

template <>
struct hash<bzla::Node>
{
  size_t operator()(const bzla::Node& node) const;
};

template <>
struct hash<bzla::Node*>
{
  size_t operator()(const bzla::Node* node) const;
};

}  // namespace std
#endif
