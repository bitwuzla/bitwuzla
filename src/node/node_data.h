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
#include "node/kind_info.h"
#include "node/node.h"
#include "type/type.h"

namespace bzla {

namespace node {

enum class Kind;

template <class T>
class NodeDataValue;

struct PayloadChildren
{
  size_t d_num_children;
  Node d_children[1];
};

struct PayloadIndexed
{
  uint8_t d_num_indices;
  uint64_t d_indices[1];
};

template <class T>
struct PayloadValue
{
  T d_value;
};

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

  static NodeData* alloc(Kind kind,
                         const std::vector<Node>& children,
                         const std::vector<uint64_t>& indices);

  static void dealloc(NodeData* data);

  template <class T>
  static NodeData* alloc(const T& value)
  {
    size_t size         = sizeof(NodeData);
    size_t payload_size = sizeof(T);

    NodeData* data =
        static_cast<NodeData*>(std::calloc(1, size + payload_size));
    if (data == nullptr)
    {
      throw std::bad_alloc();
    }
    data->d_kind = Kind::VALUE;

    auto& payload   = data->payload_value<T>();
    payload.d_value = value;
    data->d_hash    = std::hash<T>{}(value);
    return data;
  }

  NodeData() = delete;
  ~NodeData();

  /** Compute hash value. */
  size_t hash() const;

  /**
   * Comparison of two node data objects.
   *
   * @note This method is only used in NodeDataKeyEqual used for hash consing.
   *
   * @param other Other node data to compare to
   * @return True if both objects store the same data.
   */
  bool equals(const NodeData& other) const;

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
  bool is_nary() const { return KindInfo::is_nary(d_kind); }

  template <class T>
  const T& get_value() const
  {
    assert(get_kind() == Kind::VALUE);
    const auto& payload = payload_value<T>();
    return payload.d_value;
  }

  /**
   * @return Symbol of this node or empty string if node does not have a symbol.
   */
  std::optional<std::reference_wrapper<const std::string>> get_symbol() const;

  /** Increase the reference count by one. */
  void inc_ref() { ++d_refs; }

  /**
   * Decrease the reference count by one.
   *
   * If reference count becomes zero, this node data object will be
   * automatically garbage collected.
   */
  void dec_ref()
  {
    assert(d_refs > 0);
    --d_refs;
    if (d_refs == 0)
    {
      gc();
    }
  }

  /**
   * @return An iterator to the first child of this node.
   */
  iterator begin() const;

  /**
   * @return An iterator to the end of the children list of this node.
   */
  iterator end() const;

  /** @return Associated node manager instance. */
  NodeManager* nm() { return d_nm; }

 private:
  PayloadChildren& payload_children()
  {
    return const_cast<PayloadChildren&>(
        std::as_const(*this).payload_children());
  }

  const PayloadChildren& payload_children() const
  {
    assert(has_children());
    return *reinterpret_cast<const PayloadChildren*>(&d_payload);
  }

  PayloadIndexed& payload_indexed()
  {
    return const_cast<PayloadIndexed&>(std::as_const(*this).payload_indexed());
  }

  const PayloadIndexed& payload_indexed() const
  {
    assert(is_indexed());
    const auto& pc = payload_children();
    size_t offset =
        sizeof(pc.d_num_children) + sizeof(*pc.d_children) * pc.d_num_children;
    return *reinterpret_cast<const PayloadIndexed*>(&d_payload + offset);
  }

  template <class T>
  PayloadValue<T>& payload_value()
  {
    return const_cast<PayloadValue<T>&>(
        std::as_const(*this).payload_value<T>());
  }

  template <class T>
  const PayloadValue<T>& payload_value() const
  {
    assert(d_kind == Kind::VALUE);
    return *reinterpret_cast<const PayloadValue<T>*>(&d_payload);
  }

  /** Garbage collect this node. */
  void gc();

  /** Node id. */
  uint64_t d_id = 0;
  /** Node kind. */
  Kind d_kind;
  /** Node type. */
  Type d_type;
  /** Number of references. */
  uint32_t d_refs = 0;
  /** Associated node manager. */
  NodeManager* d_nm = nullptr;

  // TODO: experiment with on-the-fly computation
  size_t d_hash = 0;

  // TODO: document possible payload and layout
  uint8_t d_payload[1];
};

/* ------------------------------------------------------------------------- */

/**
 * Hash struct used for hash consing node data.
 */
struct NodeDataHash
{
  static constexpr std::array<size_t, 4> s_primes = {
      333444569u, 76891121u, 456790003u, 111130391u};

  size_t operator()(const NodeData* d) const { return d->hash(); }
};

/**
 * Comparison struct used for hash consing node data.
 */
struct NodeDataKeyEqual
{
  bool operator()(const NodeData* d0, const NodeData* d1) const
  {
    return d0->equals(*d1);
  }
};

}  // namespace node
}  // namespace bzla
#endif
