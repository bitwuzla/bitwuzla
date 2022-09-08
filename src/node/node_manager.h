#ifndef BZLA_NODE_NODE_MANAGER_H_INCLUDED
#define BZLA_NODE_NODE_MANAGER_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "node/node.h"
#include "node/node_data.h"
#include "type/type_manager.h"

namespace bzla {

class BitVector;

namespace fp {
enum class RoundingMode;
}

namespace node {

class NodeManager
{
  friend class NodeData;

 public:
  /* --- Node interface ---------------------------------------------------- */

  /**
   * Create constant.
   *
   * @param t The type of the constant.
   * @param symbol The symbol of the constant.
   * @return Constant of type `t`.
   */
  Node mk_const(const type::Type& t, const std::string& symbol = "");

  /**
   * Create variable.
   *
   * @param t The type of the variable.
   * @param symbol The symbol of the variable.
   * @return Variable of type `t`.
   */
  Node mk_var(const type::Type& t, const std::string& symbol = "");

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
  Node mk_value(const fp::RoundingMode value);

  /**
   * Create floating-point value.
   *
   * @param value Floating-point value to create.
   * @return Node representing given floating-point value.
   */
  Node mk_value(const fp::FloatingPoint& value);

  /**
   * Create node of kind `kind` with given children and indices.
   *
   * @param kind Node kind.
   * @param children The children of the node.
   * @param indices The indices if kind is indexed.
   * @return Node of kind `kind`.
   */
  Node mk_node(Kind kind,
               const std::vector<Node>& children,
               const std::vector<uint64_t>& indices = {});

  /* --- Type interface ---------------------------------------------------- */

  /**
   * @return Boolean type.
   */
  type::Type mk_bool_type();

  /**
   * Create bit-vector type.
   *
   * @param size Size of the bit-vector type.
   * @return Bit-vector type of given size.
   */
  type::Type mk_bv_type(uint64_t size);

  /**
   * Create floating-point type.
   *
   * @param exp_size Exponent size.
   * @param sig_size Significand size.
   * @return Floating-point type of given format.
   */
  type::Type mk_fp_type(uint64_t exp_size, uint64_t sig_size);

  /**
   * @return Rounding mode type.
   */
  type::Type mk_rm_type();

  /**
   * Create array type.
   *
   * @param index Index type.
   * @param element Element type.
   * @return Array type of given index and element type.
   */
  type::Type mk_array_type(const type::Type& index, const type::Type& elem);

  /**
   * Create function type.
   *
   * @param types Codomain types and domain type of function with the domain
   *              type being the last element of the vector.
   * @return Function type of given codmain and domain types.
   */
  type::Type mk_fun_type(const std::vector<type::Type>& types);

  /** Type checking of children and indices based on kind. */
  std::pair<bool, std::string> check_type(
      Kind kind,
      const std::vector<Node>& children,
      const std::vector<uint64_t>& indices = {});

 private:
  /**
   * Initialize node data.
   *
   * Initializes the given node data with the node id and stores it in the node
   * manager.
   *
   * @param d Node data to initialize.
   */
  void init_id(NodeData* d);

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
  NodeData* new_data(Kind kind,
                     const std::vector<Node>& children,
                     const std::vector<uint64_t>& indices);

  /**
   * Find or insert new node data.
   *
   * @param lookup The node data to look up in d_unique_nodes
   * @return Node data pointer if node already exists and nullptr otherwise.
   */
  NodeData* find_or_insert_node(NodeData* lookup);

  /** Compute type for a node. */
  type::Type compute_type(Kind kind,
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
  void garbage_collect(NodeData* d);

  /** Type manager. */
  type::TypeManager d_tm;

  /** Node id counter. */
  uint64_t d_node_id_counter = 1;

  /** Indicates whether node manager is in garbage collection mode. */
  bool d_in_gc_mode = false;

  /** Stores all node data objects, accessiable via the node id. */
  std::vector<std::unique_ptr<NodeData>> d_node_data;

  /** Lookup data structure for hash consing of node data. */
  std::unordered_set<NodeData*, NodeDataHash, NodeDataKeyEqual> d_unique_nodes;
};

}  // namespace node
}  // namespace bzla
#endif
