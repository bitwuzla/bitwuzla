#ifndef BZLA__NODE_H
#define BZLA__NODE_H

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <initializer_list>

#include "type/type.h"

namespace bzla::node {

enum class Kind
{
  NULL_NODE = 0,

  VALUE,
  CONSTANT,
  VARIABLE,

  /* --- Unary ------------------------------------------------------------- */
  UNARY_START,
  NOT,
  AND,
  OR,
  BV_EXTRACT,
  FP_ABS,
  FP_IS_INF,
  FP_IS_NAN,
  FP_IS_NEG,
  FP_IS_NORM,
  FP_IS_POS,
  FP_IS_SUBNORM,
  FP_IS_ZERO,
  FP_NEG,
  FP_TO_FP_BV,
  /* --- Binary ------------------------------------------------------------ */
  BINARY_START,
  BV_NOT,
  BV_AND,
  BV_ADD,
  BV_MUL,
  BV_ULT,
  BV_SHL,
  BV_SLT,
  BV_SHR,
  BV_ASHR,
  BV_UDIV,
  BV_UREM,
  BV_CONCAT,
  FP_EQUAL,
  FP_LE,
  FP_LT,
  FP_MIN,
  FP_MAX,
  FP_SQRT,
  FP_REM,
  FP_RTI,
  FP_TO_SBV,
  FP_TO_UBV,
  FP_TO_FP_FP,
  FP_TO_FP_SBV,
  FP_TO_FP_UBV,
  SELECT,
  APPLY,
  FORALL,
  EXISTS,
  LAMBDA,
  /* --- Ternary ----------------------------------------------------------- */
  TERNARY_START,
  ITE,
  FP_ADD,
  FP_MUL,
  FP_DIV,
  STORE,
  /* ----------------------------- quaternary --------------------------- */
  QUATERNARY_START,
  FP_FMA,

  NUM_KINDS,
};

class NodeData;

class Node
{
  friend class NodeManager;

 public:
  using iterator = const Node*;

  Node() = default;
  ~Node();
  Node(const Node& other);
  Node& operator=(const Node& other);
  Node(Node&& other);
  Node& operator=(Node&& other);

  /** Return id of node. */
  uint64_t get_id() const;

  /** Return node kind. */
  Kind get_kind() const;

  /** Return type of node. */
  const type::Type& get_type() const;

  /** Check whether node is null. */
  bool is_null() const;

  /** Return the number of children. */
  size_t get_num_children() const;

  /**
   * Return child at position `index`.
   *
   * Only valid to call if get_num_children() > 0.
   */
  const Node& operator[](size_t index) const;

  /** Comparison operators. */
  bool operator==(const Node& other) const;
  bool operator!=(const Node& other) const;

  /** Iterator for children. */
  iterator begin() const;
  iterator end() const;

 private:
  Node(NodeData* data);

  NodeData* d_data = nullptr;
};

}  // namespace bzla::node
#endif
