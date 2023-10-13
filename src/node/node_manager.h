/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_NODE_MANAGER_H_INCLUDED
#define BZLA_NODE_NODE_MANAGER_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "node/node.h"
#include "node/node_data.h"
#include "type/type_manager.h"

namespace bzla {

class BitVector;
class FloatingPoint;
enum class RoundingMode;

class NodeManager
{
  friend node::NodeData;

 public:
  /* --- Node interface ---------------------------------------------------- */

  /**
   * Get thread-local node manager singleton.
   */
  static NodeManager& get();

  /**
   * Create constant.
   *
   * @param t The type of the constant.
   * @param symbol The symbol of the constant.
   * @return Constant of type `t`.
   */
  Node mk_const(const Type& t,
                const std::optional<std::string>& symbol = std::nullopt);

  /**
   * Create constant array.
   *
   * @param t The array type of the constant array.
   * @param term The initializer term of the constant array.
   * @return Constant array of type `t` initialized with `term`.
   */
  Node mk_const_array(const Type& t, const Node& term);

  /**
   * Create variable.
   *
   * @param t The type of the variable.
   * @param symbol The symbol of the variable.
   * @return Variable of type `t`.
   */
  Node mk_var(const Type& t,
              const std::optional<std::string>& symbol = std::nullopt);

  /**
   * Create Boolean value.
   *
   * @param value Boolean value to create.
   * @return Node representing given Boolean value.
   */
  Node mk_value(bool value);

  /**
   * Create bit-vector value.
   *
   * @param value Bit-vector value to create.
   * @return Node representing given bit-vector value of given size.
   */
  Node mk_value(const BitVector& value);

  /**
   * Create rounding mode value.
   *
   * @param value Rounding mode value to create.
   * @return Node representing given rounding mode value.
   */
  Node mk_value(const RoundingMode value);

  /**
   * Create floating-point value.
   *
   * @param value Floating-point value to create.
   * @return Node representing given floating-point value.
   */
  Node mk_value(const FloatingPoint& value);

  /**
   * Create node of kind `kind` with given children and indices.
   *
   * @param kind Node kind.
   * @param children The children of the node.
   * @param indices The indices if kind is indexed.
   * @return Node of kind `kind`.
   */
  Node mk_node(node::Kind kind,
               const std::vector<Node>& children,
               const std::vector<uint64_t>& indices = {});

  /**
   * Helper to create an inverted Boolean or bit-vector node.
   * @param node The node to invert.
   * @return The inverted node.
   */
  Node invert_node(const Node& node);

  /* --- Type interface ---------------------------------------------------- */

  /**
   * @return Boolean type.
   */
  Type mk_bool_type();

  /**
   * Create bit-vector type.
   *
   * @param size Size of the bit-vector type.
   * @return Bit-vector type of given size.
   */
  Type mk_bv_type(uint64_t size);

  /**
   * Create floating-point type.
   *
   * @param exp_size Exponent size.
   * @param sig_size Significand size.
   * @return Floating-point type of given format.
   */
  Type mk_fp_type(uint64_t exp_size, uint64_t sig_size);

  /**
   * @return Rounding mode type.
   */
  Type mk_rm_type();

  /**
   * Create array type.
   *
   * @param index Index type.
   * @param element Element type.
   * @return Array type of given index and element type.
   */
  Type mk_array_type(const Type& index, const Type& elem);

  /**
   * Create function type.
   *
   * @param types Codomain types and domain type of function with the domain
   *              type being the last element of the vector.
   * @return Function type of given codmain and domain types.
   */
  Type mk_fun_type(const std::vector<Type>& types);

  /**
   * Create uninterpreted type.
   * @param The symbol of the uninterpreted type.
   * @return Uninterpreted type.
   */
  Type mk_uninterpreted_type(
      const std::optional<std::string>& symbol = std::nullopt);

  /** Type checking of children and indices based on kind. */
  std::pair<bool, std::string> check_type(
      node::Kind kind,
      const std::vector<Node>& children,
      const std::vector<uint64_t>& indices = {});

#ifndef NDEBUG
  /** @return Current maximum node id. */
  uint64_t max_node_id() const { return d_node_id_counter; }
#endif

 private:
  /**
   * Constructor, copy constructor, copy assignment and destructor are private
   * since node manager is a thread-local singleton that should always be
   * acquired via NodeManager::get().
   */
  NodeManager()                              = default;
  ~NodeManager();
  NodeManager(const NodeManager&)            = delete;
  NodeManager& operator=(const NodeManager&) = delete;

  /**
   * Initialize node data.
   *
   * Initializes the given node data with the node id and stores it in the node
   * manager.
   *
   * @param d Node data to initialize.
   */
  void init_id(node::NodeData* d);

  /**
   * Create node data object.
   *
   * Creates node data object based on the given kind (either NodeDataIndexed,
   * NodeDataChildren or NodeDataNary).
   *
   * @param kind The node kind.
   * @param children The children of the node.
   * @param indices The indices of the node.
   * @return Node data.
   */
  node::NodeData* new_data(node::Kind kind,
                           const std::vector<Node>& children,
                           const std::vector<uint64_t>& indices);

  /**
   * Find or insert new node data.
   *
   * @param lookup The node data to look up in d_unique_nodes
   * @return Node data pointer if node already exists and nullptr otherwise.
   */
  node::NodeData* find_or_insert_node(node::NodeData* lookup);

  /** Compute type for a node. */
  Type compute_type(node::Kind kind,
                    const std::vector<Node>& children,
                    const std::vector<uint64_t>& indices = {});

  /**
   * Garbage collect node data.
   *
   * @note This will recursively delete all node data objects for which the
   *       reference count becomes zero.
   *
   * @param d Node data to delete.
   */
  void garbage_collect(node::NodeData* d);

  const std::optional<std::reference_wrapper<const std::string>> get_symbol(
      const node::NodeData* d) const;

  /** Type manager. */
  type::TypeManager d_tm;

  /** Node id counter. */
  uint64_t d_node_id_counter = 1;

  /** Indicates whether node manager is in garbage collection mode. */
  bool d_in_gc_mode = false;

  /** Stores all node data objects, accessible via the node id. */
  std::vector<std::unique_ptr<node::NodeData>> d_node_data;

  /** Lookup data structure for hash consing of node data. */
  std::
      unordered_set<node::NodeData*, node::NodeDataHash, node::NodeDataKeyEqual>
          d_unique_nodes;

  /** Stores symbols for nodes. */
  std::unordered_map<const node::NodeData*, std::string> d_symbol_table;
};

}  // namespace bzla
#endif
