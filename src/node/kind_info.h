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

  /** @return Is given kind chainable (e.g. EQUAL). */
  static bool is_chainable(Kind kind);

  /** @return Is given kind pairwise chainable (e.g. DISTINCT). */
  static bool is_pairwise(Kind kind);

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
  };

  /** Initialize kind information for given `kind`. */
  constexpr void init(Kind kind,
                      uint8_t num_children,
                      uint8_t num_indices,
                      const char* enum_name,
                      const char* smt2_name   = "",
                      KindAttribute attribute = NONE);

  constexpr KindInfo();

  /** Are all kinds initialized? */
  constexpr bool complete() const;

  /** Get KindInfo singleton. */
  static const KindInfo& get();

  size_t d_num_inited = 0;
  std::array<KindData, static_cast<size_t>(Kind::NUM_KINDS)> d_info;
};

}  // namespace bzla::node

#endif
