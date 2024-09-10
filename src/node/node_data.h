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

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <optional>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node.h"
#include "type/type.h"

namespace bzla::node {

/** Payload for nodes with arbitrary number of children. */
struct PayloadChildren
{
  size_t d_num_children;
  Node d_children[1];
};

/** Payload for indexed nodes with arbitrary number of children. */
struct PayloadIndexed
{
  size_t d_num_indices;
  uint64_t d_indices[1];
};

/** Payload for values. */
template <class T>
struct PayloadValue
{
  T d_value;
};

/** Payload for constants and variables. */
struct PayloadSymbol
{
  std::optional<std::string> d_symbol;
};

/**
 * Node data base class.
 *
 * Memory for payload will be allocated based on requirements of node kind.
 */
class NodeData
{
  friend NodeManager;
  friend class NodeUniqueTable;

 public:
  using iterator = const Node*;

  /** Allocate node data for constants and variables. */
  static NodeData* alloc(Kind kind, const std::optional<std::string>& symbol);

  /** Allocate node data for nodes with children. */
  static NodeData* alloc(Kind kind,
                         const std::vector<Node>& children,
                         const std::vector<uint64_t>& indices);

  /** Allocate node data for values. */
  template <class T>
  static NodeData* alloc(const T& value)
  {
    size_t size         = sizeof(NodeData);
    size_t payload_size = sizeof(PayloadValue<T>);

    NodeData* data =
        static_cast<NodeData*>(std::calloc(1, size + payload_size));
    if (data == nullptr)
    {
      throw std::bad_alloc();
    }
    data->d_kind = Kind::VALUE;

    auto& payload   = data->payload_value<T>();
    payload.d_value = value;
    return data;
  }

  /** Deallocate node data. */
  static void dealloc(NodeData* data);

  NodeData() = delete;
  ~NodeData();

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

  /**
   * @return Value instance stored by this node data.
   */
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

  /** @return Node info flags. */
  auto& info() { return d_info; }

 private:
  /** @return Children payload of this node. */
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

  /** @return Indices payload of this node. */
  PayloadIndexed& payload_indexed()
  {
    return const_cast<PayloadIndexed&>(std::as_const(*this).payload_indexed());
  }

  const PayloadIndexed& payload_indexed() const
  {
    assert(is_indexed());
    const auto& pc = payload_children();
    // Note: Indices are always stored after children, hence we compute the
    //       offset.
    size_t offset =
        sizeof(pc.d_num_children) + sizeof(*pc.d_children) * pc.d_num_children;
    return *reinterpret_cast<const PayloadIndexed*>(&d_payload + offset);
  }

  /** @return Value payload of this node. */
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

  /** @return Symbol payload of this node. */
  PayloadSymbol& payload_symbol()
  {
    return const_cast<PayloadSymbol&>(std::as_const(*this).payload_symbol());
  }

  const PayloadSymbol& payload_symbol() const
  {
    assert(d_kind == Kind::CONSTANT || d_kind == Kind::VARIABLE);
    return *reinterpret_cast<const PayloadSymbol*>(&d_payload);
  }

  /** Garbage collect this node. */
  void gc();

  /** Associated node manager. */
  NodeManager* d_nm = nullptr;
  /** Next node in unique table collision chain. */
  NodeData* d_next = nullptr;
  /** Node id. */
  uint64_t d_id = 0;
  /** Node type. */
  Type d_type;
  /** Number of references. */
  uint32_t d_refs = 0;
  /** Node kind. */
  Kind d_kind;
  /** Node info flags. */
  NodeInfo d_info;

  /**
   * Payload placeholder.
   *
   * Depending on the node kind, additional memory is allocated to store:
   *  - PayloadChildren (nodes with arbitrary number of children)
   *  - PayloadIndexed  (indexed nodes)
   *  - PayloadValue    (values: bool, BitVector, RoundingMode, FloatingPoint)
   *  - PayloadSymbol   (symbols for constants and variables)
   */
  uint8_t d_payload[1];
};

/* ------------------------------------------------------------------------- */

}  // namespace bzla::node
#endif
