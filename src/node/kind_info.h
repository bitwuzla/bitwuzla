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
  static uint32_t num_children(Kind kind);

  /** @return The number of indices for this kind. */
  static uint32_t num_indices(Kind kind);

  /** @return The string representation for this kind. */
  static const char* enum_name(Kind kind);

  /** @return The SMT-LIBv2 string representation for this kind. */
  static const char* smt2_name(Kind kind);

  /** @return Does this kind support an arbitrary number of children? */
  static bool is_nary(Kind kind);

  /** @return Is given kind left associative. */
  static bool is_left_associative(Kind kind);

  /** @return Is given kind right associative. */
  static bool is_right_associative(Kind kind);

  /** @return Is given kind commutative. */
  static bool is_commutative(Kind kind);

  /** @return Is given kind chainable (e.g. EQUAL). */
  static bool is_chainable(Kind kind);

  /** @return Is given kind pairwise chainable (e.g. DISTINCT). */
  static bool is_pairwise(Kind kind);

  /** @return Whether given kind is a boolean kind. */
  static bool is_bool(Kind kind);

  /** @return Whether given kind is a bit-vector kind. */
  static bool is_bv(Kind kind);

  /** @return Whether given kind is a floating-point kind. */
  static bool is_fp(Kind kind);

  /** @return Whether given kind is an array kind. */
  static bool is_array(Kind kind);

  /** @return Whether given kind is a function kind. */
  static bool is_fun(Kind kind);

  /** @return Whether given kind is a quantifier kind. */
  static bool is_quant(Kind kind);

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

  constexpr KindInfo();

  /** Are all kinds initialized? */
  constexpr bool complete() const;

  /** Get KindInfo singleton. */
  static const KindInfo& get();

  /** Number of initialized kind info entries. */
  size_t d_num_inited = 0;
  /** The kind info entries. */
  std::array<KindData, static_cast<size_t>(Kind::NUM_KINDS)> d_info;
};

}  // namespace bzla::node

#endif
