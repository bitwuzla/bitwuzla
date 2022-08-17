#ifndef BZLA__NODE_H
#define BZLA__NODE_H

#include <array>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <initializer_list>

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
#ifndef NDEBUG
  Node(Kind kind,
       const std::initializer_list<Node>& children,
       const std::initializer_list<uint64_t>& indices = {});
#endif
  Node(const Node& other);
  Node& operator=(const Node& other);
  Node(Node&& other);
  Node& operator=(Node&& other);

  uint64_t get_id() const;
  Kind get_kind() const;
  bool is_null() const;

  bool operator==(const Node& other) const;
  bool operator!=(const Node& other) const;

  size_t get_num_children() const;
  const Node& operator[](size_t index) const;

  iterator begin() const;
  iterator end() const;

  NodeData* get_data() { return d_data; }
  NodeData* get_data() const { return d_data; }

 private:
  NodeData* d_data = nullptr;
};

}  // namespace bzla::node

#endif
