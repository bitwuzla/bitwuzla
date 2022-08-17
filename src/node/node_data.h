#ifndef BZLA__NODE_DATA_H
#define BZLA__NODE_DATA_H

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>

#include "node/node.h"

namespace bzla::node {

class NodeManager;
enum class Kind;

static constexpr size_t s_max_children = 4;

class NodeData
{
  friend class Node;
  friend class NodeManager;
  friend struct NodeDataHash;
  friend struct NodeDataKeyEqual;
  friend class NodeDataChildren;

 public:
  NodeData() = delete;
  NodeData(NodeManager* mgr, Kind kind) : d_mgr(mgr), d_kind(kind){};
  virtual ~NodeData() = default;

  uint64_t get_id() const { return d_id; }
  Kind get_kind() const { return d_kind; }

  const Node& get_child(size_t index) const;
  Node& get_child(size_t index);
  size_t get_num_children() const;

  // TODO: get_indices()
  // TODO: specific instantiantions for ExtractLower/ExtractUpper?
  uint64_t get_index(size_t index) const;
  size_t get_num_indices() const;

  // TODO: instantiate with
  // - BitVector
  // - FloatingPoint
  // - RoundingMode
  template <class T>
  T& get_value() const;

  // iterators

  // Reference counting
  void inc_ref();
  void dec_ref();

 private:
  bool has_children() const;
  bool is_indexed() const;

  NodeManager* d_mgr = nullptr;
  NodeData* d_next   = nullptr;

  uint64_t d_id = 0;
  Kind d_kind;
  // Type d_type;
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
                   const std::initializer_list<Node>& children)
      : NodeData(mgr, kind), d_num_children(children.size())
  {
    assert(d_num_children > 0);
    assert(d_num_children <= s_max_children);
    assert(Kind::UNARY_START < kind);
    assert(kind < Kind::NUM_KINDS);
    uint8_t i = 0;
    for (auto n : children)
    {
      assert(!n.is_null());
      d_children[i++] = n;
    }
    assert(i == d_num_children);
  };

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
                  const std::initializer_list<Node>& children,
                  const std::initializer_list<uint64_t>& indices)
      : NodeDataChildren(mgr, kind, children), d_num_indices(indices.size())
  {
    assert(d_num_indices > 0);
    assert(d_num_indices <= 2);
    uint8_t i = 0;
    for (auto idx : indices)
    {
      d_indices[i] = idx;
    }
    assert(i == d_num_indices);
  };
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
