/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_DATA_H_INCLUDED
#define BZLA_NODE_NODE_DATA_H_INCLUDED

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <optional>

#include "bv/bitvector.h"
#include "node/node.h"
#include "type/type.h"

namespace bzla {

namespace node {

enum class Kind;

template <class T>
class NodeDataValue;

/**
 * Node data base class.
 *
 * Used for nodes that do not need additional payload, e.g. Kind::CONSTANT.
 */
class NodeData
{
  friend NodeManager;
  friend struct NodeDataHash;
  friend struct NodeDataKeyEqual;

 public:
  using iterator = const Node*;

  NodeData()          = delete;
  virtual ~NodeData() = default;

  /** Compute hash value. */
  virtual size_t hash() const;

  /**
   * Comparison of two node data objects.
   *
   * @note This method is only used in NodeDataKeyEqual used for hash consing.
   *
   * @param other Other node data to compare to
   * @return True if both objects store the same data.
   */
  virtual bool equals(const NodeData& other) const;

  /**
   * @return The node id.
   */
  uint64_t get_id() const { return d_id; }

  /**
   * @return The node kind.
   */
  Kind get_kind() const { return d_kind; }

  /**
   * @return The node type.
   */
  const Type& get_type() const { return d_type; }

  /**
   * @return True if node data stores children.
   */
  bool has_children() const;

  /**
   * Return child at position `index`.
   *
   * @note: Only valid to call if get_num_children() > 0.
   *
   * @param index The position of the child.
   * @return The child node at position `index`.
   */
  const Node& get_child(size_t index) const;

  /**
   * Return child at position `index`.
   *
   * @note: Only valid to call if get_num_children() > 0.
   *
   * @param index The position of the child.
   * @return The child node at position `index`.
   */
  Node& get_child(size_t index);

  /**
   * @return The number of stored children.
   */
  size_t get_num_children() const;

  /**
   * @return True if node data stores indices.
   */
  bool is_indexed() const;

  /**
   * Get index at position `index`.
   *
   * @note: Only valid to call for indexed operators.
   *
   * @param index The position of the index.
   * @return The index.
   */
  uint64_t get_index(size_t index) const;

  /**
   * @return The number of stored indices.
   */
  size_t get_num_indices() const;

  /**
   * @return True if node data stores arbitrary number of children.
   */
  bool is_nary() const;

  template <class T>
  const T& get_value() const
  {
    assert(get_kind() == Kind::VALUE);
    const auto& data = reinterpret_cast<const NodeDataValue<T>&>(*this);
    return data.d_value;
  }

  /**
   * @return Symbol of this node or empty string if node does not have a symbol.
   */
  std::optional<std::reference_wrapper<const std::string>> get_symbol() const;

  /** Increase the reference count by one. */
  void inc_ref();

  /**
   * Decrease the reference count by one.
   *
   * If reference count becomes zero, this node data object will be
   * automatically garbage collected.
   */
  void dec_ref();

  /**
   * @return An iterator to the first child of this node.
   */
  iterator begin() const;

  /**
   * @return An iterator to the end of the children list of this node.
   */
  iterator end() const;

 protected:
  NodeData(Kind kind);

 private:
  /** Node id. */
  uint64_t d_id = 0;
  /** Node kind. */
  Kind d_kind;
  /** Node type. */
  Type d_type;
  /** Number of references. */
  uint32_t d_refs = 0;
};

/**
 * Node data with a payload of at most `s_max_children` children.
 *
 * Always allocates an std::array of size `s_max_children` to store children.
 */
class NodeDataChildren : public NodeData
{
  friend NodeData;

 public:
  static constexpr size_t s_max_children = 4;

  NodeDataChildren()  = delete;
  ~NodeDataChildren() = default;

  NodeDataChildren(Kind kind, const std::vector<Node>& children);

  size_t hash() const override;
  bool equals(const NodeData& other) const override;

 private:
  /** The number of stored children. */
  uint8_t d_num_children;
  /** Storage for at most `s_max_children` children. */
  std::array<Node, s_max_children> d_children;
};

/**
 * Node data with a payload of at most `s_max_children` children and 2 indices.
 *
 * Always allocates an std::array of size 2 to store indices.
 */
class NodeDataIndexed : public NodeDataChildren
{
  friend NodeData;

 public:
  NodeDataIndexed() = delete;
  NodeDataIndexed(Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices);
  ~NodeDataIndexed() = default;

  size_t hash() const override;
  bool equals(const NodeData& other) const override;

 private:
  /** The number of stored indices. */
  uint8_t d_num_indices = 0;
  /** Storage for at most 2 indices. */
  std::array<uint64_t, 2> d_indices;
};

/**
 * Node data to store an arbitrary number of children.
 */
class NodeDataNary : public NodeData
{
  friend NodeData;

 public:
  NodeDataNary()  = delete;
  ~NodeDataNary() = default;

  NodeDataNary(Kind kind, const std::vector<Node>& children);

  size_t hash() const override;
  bool equals(const NodeData& other) const override;

 private:
  /** Storage for arbitrary number of children. */
  std::vector<Node> d_children;
};

/**
 * Node data template to store arbitrary values.
 */
template <class T>
class NodeDataValue : public NodeData
{
  friend NodeData;

 public:
  NodeDataValue() = delete;
  NodeDataValue(const T& value) : NodeData(Kind::VALUE), d_value(value){};

  ~NodeDataValue() = default;

  size_t hash() const override
  {
    return NodeData::hash() + std::hash<T>{}(d_value);
  }

  bool equals(const NodeData& other) const override
  {
    if (!NodeData::equals(other))
    {
      return false;
    }
    if (get_type() != other.get_type())
    {
      return false;
    }
    const auto& o = reinterpret_cast<const NodeDataValue<T>&>(other);
    return d_value == o.d_value;
  }

 private:
  T d_value;
};

/* ------------------------------------------------------------------------- */

/**
 * Hash struct used for hash consing node data.
 */
struct NodeDataHash
{
  static constexpr std::array<size_t, 4> s_primes = {
      333444569u, 76891121u, 456790003u, 111130391u};
  size_t operator()(const NodeData* d) const;
};

/**
 * Comparison struct used for hash consing node data.
 */
struct NodeDataKeyEqual
{
  bool operator()(const NodeData* d0, const NodeData* d1) const;
};

}  // namespace node
}  // namespace bzla
#endif
