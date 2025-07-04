/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_FP_WORD_BLASTER_H_INCLUDED
#define BZLA_SOLVER_FP_WORD_BLASTER_H_INCLUDED

#include <unordered_map>
#include <vector>

#include "backtrack/unordered_set.h"
#include "env.h"
#include "node/node.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/floating_point_symfpu.h"

/* -------------------------------------------------------------------------- */

namespace bzla {

class SolverState;

namespace fp {

class SymFpuSymTraits;

template <bool T>
class SymFpuSymBV;
class SymFpuSymRM;
class SymFpuSymProp;

class WordBlaster
{
 public:
  /**
   * Determine if given node is a leaf node for the word blaster, i.e., a term
   * of floating-point or rounding mode type that belongs to any of the other
   * theories.
   * @param node The node to query.
   */
  static bool is_leaf(const Node& node);

  WordBlaster(Env& env, SolverState& state);
  ~WordBlaster();

  /**
   * Word-blast (if not yet word-blasted) given node.
   *
   * @note First checks if we have already word-blasted node, and word-blasts
   *       it via _wordblast() if not.
   *
   * @param node The node to word-blast.
   * @return The word-blasted node.
   */
  Node word_blast(const Node& node);

  /**
   * Determine whether word_blast() was already called on given node.
   * @param node The node to query the status for.
   * @return True if `node` has already been word-blasted.
   */
  bool is_word_blasted(const Node& node) const;

  /**
   * Determine whether word_blast() was called in a currently active assertion
   * level on given RM/FP const/leaf.
   * @param node   The const/leaf to query the status for.
   * @return True if `node` is an RM/FP const/leaf and has been word-blasted in
   *         any of the currently active assertion levels.
   */
  bool is_cur_word_blasted_const(const Node& node) const;

  /**
   * Word-blast given floating-point or rounding mode constant/leaf (if not
   * word-blasted) and return constraint to ensure validity of the word-blasted
   * representation of the constant/leaf.
   */
  std::pair<Node, bool> valid(const Node& node);

 private:
  using SymUnpackedFloat = ::symfpu::unpackedFloat<SymFpuSymTraits>;
  using UnpackedFloatMap = std::unordered_map<Node, SymUnpackedFloat>;
  using SymFpuSymRMMap   = std::unordered_map<Node, SymFpuSymRM>;
  using SymFpuSymPropMap = std::unordered_map<Node, SymFpuSymProp>;
  using PackedFloatMap   = std::unordered_map<Node, SymFpuSymBV<false>>;
  using SymSBVMap        = std::unordered_map<Node, SymFpuSymBV<true>>;
  using SymUBVMap        = std::unordered_map<Node, SymFpuSymBV<false>>;

  struct Internal;

  /**
   * Helper to word-blast given node.
   * @param node The node to word-blast.
   * @return The word-blasted node.
   */
  Node _word_blast(const Node& node);

  /**
   * Construct (if not already constructed) and get an UF of type
   * (bv_[n], ..., bv_[n]) ->bv_[1] to encode undefined values for a given
   * FP_MIN or FP_MAX node (both min/max are not total).
   *
   * Size n = size of the IEEE BV representation of the children, and the
   * domain size of the UF corresponds to the number of children of the
   * given min/max node.
   *
   * @note UFs introduced for FP_MIN/FP_MAX are cached in `d_min_max_uf_map`.
   *
   * @param node The min/max node.
   * @return The introduced UF.
   */
  const Node& min_max_uf(const Node& node);
  /**
   * Construct (if not already constructed) and get an UF of type
   * (rm, fp_[n,m]) -> bv_[n+m] to encode undefined values for a given
   * FP_TO_SBV or FP_TO_UBV node (both functions are not total).
   *
   * Sizes n = exponent size and m = significand size of the floating-point
   * to convert.
   *
   * @note UFs introduced for FP_TO_SBV/FP_TO_SBV are cached in
   *           `d_sbv_ubv_uf_map`.
   *
   * @param node The to_sbv/to_ubv node.
   * @return The introduced UF.
   */
  const Node& sbv_ubv_uf(const Node& node);

  std::unique_ptr<Internal> d_internal;

  /** Map floating-point type of FP_MIN and FP_MAX to introduced UF. */
  std::unordered_map<Type, Node> d_min_max_uf_map;
  /** Map function type of UF introduced for FP_TO_SBV and FP_TO_UBV to UF. */
  std::unordered_map<Type, Node> d_sbv_ubv_uf_map;

  std::vector<Node> d_additional_assertions;

  /**
   * Cache which constants have been word-blasted in the currently active
   * assertion levels.
   */
  backtrack::unordered_set<Node> d_word_blasted_consts;

  /** The associated environment. */
  Env& d_env;
  /** The associated solver state. */
  SolverState& d_solver_state;
};

/* -------------------------------------------------------------------------- */
}  // namespace fp
}  // namespace bzla

#endif
