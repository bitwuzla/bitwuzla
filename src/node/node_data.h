#ifndef BZLA__NODE_DATA_H
#define BZLA__NODE_DATA_H

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>

#include "node/node.h"
#include "type/type.h"

namespace bzla::node {

class NodeManager;
enum class Kind;

static constexpr size_t s_max_children = 4;

class NodeData
{
  friend class NodeManager;
  friend struct NodeDataHash;
  friend struct NodeDataKeyEqual;

 public:
  NodeData() = delete;
  NodeData(NodeManager* mgr, Kind kind);
  virtual ~NodeData() = default;

  /** Return node id. */
  uint64_t get_id() const { return d_id; }

  /** Return node kind. */
  Kind get_kind() const { return d_kind; }

  /** Return node type. */
  const type::Type& get_type() const { return d_type; }

  /** Check whether node has children. */
  bool has_children() const;

  /**
   * Return child at position `index`.
   *
   * Only valid to call if get_num_children() > 0.
   */
  const Node& get_child(size_t index) const;
  Node& get_child(size_t index);

  /** Return number of children. */
  size_t get_num_children() const;

  /** Check whether node is indexed. */
  bool is_indexed() const;

  // TODO: get_indices()
  // TODO: specific instantiantions for ExtractLower/ExtractUpper?
  /**
   * Get index at position `index`.
   *
   * Only valid to call for indexed operators.
   */
  uint64_t get_index(size_t index) const;

  /** Return number of indices. */
  size_t get_num_indices() const;

  // TODO: instantiate with
  // - BitVector
  // - FloatingPoint
  // - RoundingMode
  template <class T>
  T& get_value() const;

  // Reference counting
  void inc_ref();
  void dec_ref();

 private:
  NodeManager* d_mgr = nullptr;

  uint64_t d_id = 0;
  Kind d_kind;
  type::Type d_type;
  uint32_t d_refs = 0;
};

class NodeDataChildren : public NodeData
{
  friend class Node;
  friend class NodeData;

 public:
  NodeDataChildren()  = delete;
  ~NodeDataChildren() = default;

  NodeDataChildren(NodeManager* mgr,
                   Kind kind,
                   const std::vector<Node>& children);

 private:
  uint8_t d_num_children;
  std::array<Node, s_max_children> d_children;
};

// class NodeDataArguments : public NodeData
//{
//   friend class NodeData;
//
//   std::vector<Node> d_children;
// };

class NodeDataIndexed : public NodeDataChildren
{
  friend class NodeData;
  friend class NodeDataChildren;

 public:
  NodeDataIndexed() = delete;
  NodeDataIndexed(NodeManager* mgr,
                  Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices);
  ~NodeDataIndexed() = default;

 private:
  uint8_t d_num_indices = 0;
  std::array<uint64_t, 2> d_indices;
};

// template <class T>
// class NodeDataValue : public NodeData
//{
//   friend class NodeData;
//
//  public:
//   NodeDataValue() = delete;
//   NodeDataValue(NodeManager* mgr, const T& value);
//       : NodeData(mgr, Kind::VALUE), d_value(value){};
//
//   ~NodeDataValue() = default;
//
//  private:
//   T d_value;
// };

/* ------------------------------------------------------------------------- */

struct NodeDataHash
{
  static constexpr size_t s_primes[4] = {
      333444569u, 76891121u, 456790003u, 111130391u};
  size_t operator()(const NodeData* d) const;
};

struct NodeDataKeyEqual
{
  bool operator()(const NodeData* d0, const NodeData* d1) const;
};

}  // namespace bzla::node
#endif
