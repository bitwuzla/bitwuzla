/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_NODE_KIND_INFO_INCLUDED
#define BZLA_NODE_KIND_INFO_INCLUDED

#include <array>

#include "node/node_kind.h"

namespace bzla::node {

/**
 * Struct to storing and accessing information for all kinds.
 */
struct KindInfo
{
  /** @return The number of children for this kind. */
  static uint32_t num_children(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_num_children;
  }

  /** @return The number of indices for this kind. */
  static uint32_t num_indices(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_num_indices;
  }

  /** @return The string representation for this kind. */
  static const char* enum_name(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_enum_name;
  }

  /** @return The SMT-LIBv2 string representation for this kind. */
  static const char* smt2_name(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_smt2_name;
  }

  /** @return Does this kind support an arbitrary number of children? */
  static bool is_nary(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_num_children
           == KindInfo::s_nary;
  }

  /** @return Is given kind left associative. */
  static bool is_left_associative(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_attribute
           == KindAttribute::LEFT_ASSOC;
  }

  /** @return Is given kind right associative. */
  static bool is_right_associative(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_attribute
           == KindAttribute::RIGHT_ASSOC;
  }

  /** @return Is given kind commutative. */
  static bool is_commutative(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].is_commutative;
  }

  /** @return Is given kind chainable (e.g. EQUAL). */
  static bool is_chainable(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_attribute
           == KindAttribute::CHAINABLE;
  }

  /** @return Is given kind pairwise chainable (e.g. DISTINCT). */
  static bool is_pairwise(Kind kind)
  {
    return get().d_info[static_cast<size_t>(kind)].d_attribute
           == KindAttribute::PAIRWISE;
  }

  /** @return Whether given kind is a boolean kind. */
  static bool is_bool(Kind kind)
  {
    return Kind::AND <= kind && kind <= Kind::XOR;
  }

  /** @return Whether given kind is a bit-vector kind. */
  static bool is_bv(Kind kind)
  {
    return Kind::BV_ADD <= kind && kind <= Kind::BV_ZERO_EXTEND;
  }

  /** @return Whether given kind is a floating-point kind. */
  static bool is_fp(Kind kind)
  {
    return Kind::FP_ABS <= kind && kind <= Kind::FP_TO_UBV;
  }

  /** @return Whether given kind is an array kind. */
  static bool is_array(Kind kind)
  {
    return Kind::CONST_ARRAY <= kind && kind <= Kind::STORE;
  }

  /** @return Whether given kind is a function kind. */
  static bool is_fun(Kind kind)
  {
    return kind == Kind::APPLY || kind == Kind::LAMBDA;
  }

  /** @return Whether given kind is a quantifier kind. */
  static bool is_quant(Kind kind)
  {
    return kind == Kind::EXISTS || kind == Kind::FORALL;
  }

  constexpr KindInfo();

  /** Are all kinds initialized? */
  constexpr bool complete() const;

 private:
  static constexpr uint8_t s_nary = UINT8_MAX;

  enum KindAttribute
  {
    NONE,
    LEFT_ASSOC,
    RIGHT_ASSOC,
    CHAINABLE,
    PAIRWISE,
  };

  struct KindData
  {
    uint8_t d_num_children    = 0;
    uint8_t d_num_indices     = 0;
    const char* d_enum_name   = nullptr;
    const char* d_smt2_name   = nullptr;
    KindAttribute d_attribute = KindAttribute::NONE;
    bool is_commutative       = false;
  };

  /** Initialize kind information for given `kind`. */
  constexpr void init(Kind kind,
                      uint8_t num_children,
                      uint8_t num_indices,
                      const char* enum_name,
                      const char* smt2_name   = "",
                      KindAttribute attribute = NONE,
                      bool is_commutative     = false);

  /** Get KindInfo singleton. */
  static const KindInfo& get();

  /** Number of initialized kind info entries. */
  size_t d_num_inited = 0;
  /** The kind info entries. */
  std::array<KindData, static_cast<size_t>(Kind::NUM_KINDS)> d_info;
};

// Note: mingw has linking errors if s_sinfo is declared in in-class definition
// of KindInfo::get() above.
extern const KindInfo s_info;

inline const KindInfo&
KindInfo::get()
{
  return s_info;
}

}  // namespace bzla::node

#endif
