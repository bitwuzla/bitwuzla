#ifndef BZLA_NODE_NODE_H_INCLUDED
#define BZLA_NODE_NODE_H_INCLUDED

#include <cassert>
#include <cstddef>
#include <cstdint>
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
}  // namespace node

/* --- Node ---------------------------------------------------------------- */

class Node
{
  friend NodeManager;
  friend bool operator==(const Node& a, const Node& b);
  friend bool operator!=(const Node& a, const Node& b);

 public:
  using iterator = const Node*;

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
  bool is_null() const;

  /**
   * @return True if this node is a value.
   */
  bool is_value() const;

  /**
   * @return True if this node is a first order constant.
   */
  bool is_const() const;

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

 private:
  Node(node::NodeData* data);

  /** Node payload. */
  node::NodeData* d_data = nullptr;
};

/** Syntactical equality over two nodes. */
bool operator==(const Node& a, const Node& b);
/** Syntactical disequality over two nodes. */
bool operator!=(const Node& a, const Node& b);
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
