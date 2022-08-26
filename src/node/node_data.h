#ifndef BZLA_NODE_NODE_DATA_H_INCLUDED
#define BZLA_NODE_NODE_DATA_H_INCLUDED

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>

#include "node/node.h"
#include "type/type.h"

namespace bzla::node {

class NodeManager;
enum class Kind;

/**
 * Node data base class.
 *
 * Used for nodes that do not need additional payload, e.g. Kind::CONSTANT.
 */
class NodeData
{
  friend class NodeManager;
  friend struct NodeDataHash;
  friend struct NodeDataKeyEqual;

 public:
  using iterator = const Node*;

  NodeData()          = delete;
  virtual ~NodeData() = default;

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
  const type::Type& get_type() const { return d_type; }

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

  // TODO: instantiate with
  // - BitVector
  // - FloatingPoint
  // - RoundingMode
  template <class T>
  T& get_value() const;

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
  NodeData(NodeManager* mgr, Kind kind);

 private:
  /** The owning node manager. */
  NodeManager* d_mgr = nullptr;
  /** Node id. */
  uint64_t d_id = 0;
  /** Node kind. */
  Kind d_kind;
  /** Node type. */
  type::Type d_type;
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
  friend class NodeData;

 public:
  static constexpr size_t s_max_children = 4;

  NodeDataChildren()  = delete;
  ~NodeDataChildren() = default;

  NodeDataChildren(NodeManager* mgr,
                   Kind kind,
                   const std::vector<Node>& children);

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
  friend class NodeData;

 public:
  NodeDataIndexed() = delete;
  NodeDataIndexed(NodeManager* mgr,
                  Kind kind,
                  const std::vector<Node>& children,
                  const std::vector<uint64_t>& indices);
  ~NodeDataIndexed() = default;

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
  friend class NodeData;

 public:
  NodeDataNary()  = delete;
  ~NodeDataNary() = default;

  NodeDataNary(NodeManager* mgr, Kind kind, const std::vector<Node>& children);

 private:
  /** Storage for arbitrary number of children. */
  std::vector<Node> d_children;
};

/* ------------------------------------------------------------------------- */

/**
 * Hash struct used for hash consing node data.
 */
struct NodeDataHash
{
  static constexpr size_t s_primes[4] = {
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

}  // namespace bzla::node
#endif
