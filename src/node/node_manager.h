#ifndef BZLA__NODE_MANAGER_H
#define BZLA__NODE_MANAGER_H

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "node/node.h"
#include "node/node_data.h"
#include "node/type.h"

namespace bzla::node {

class NodeManager
{
  friend class NodeData;

 public:
  // Node interface

  // Node mk_const(const Type& t, const std::string& symbol = "");
  // template<class T> Node mk_value(Kind kind, const Type& t, const T value);

  Node mk_node(Kind kind,
               const std::initializer_list<Node>& children,
               const std::initializer_list<uint64_t>& indices = {});

 private:
  void init_id(NodeData* d);

  NodeData* new_data(Kind kind,
                     const std::initializer_list<Node>& children,
                     const std::initializer_list<uint64_t>& indices);

  // NodeData* find_or_create_value(NodeData *lookup);
  NodeData* find_or_create_node(Kind kind,
                                const std::initializer_list<Node>& children,
                                const std::initializer_list<uint64_t>& indices);

  void garbage_collect(NodeData* d);

  uint64_t d_node_id_counter = 1;
  bool d_in_gc_mode          = false;
  std::vector<std::unique_ptr<NodeData>> d_node_data;
  std::unordered_set<NodeData*, NodeDataHash, NodeDataKeyEqual> d_unique_nodes;
};

}  // namespace bzla::node
#endif
