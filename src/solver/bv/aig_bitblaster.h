/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_AIG_BITBLASTER_H_INCLUDED
#define BZLA_SOLVER_BV_AIG_BITBLASTER_H_INCLUDED

#include <unordered_set>
#include <unordered_map>

#include "bitblast/aig_bitblaster.h"
#include "node/node.h"

namespace bzla::bv {

class AigBitblaster
{
 public:
  using aig_node_vector = std::vector<bitblast::AigNode>;
  using unordered_aig_node_ref_set =
      std::unordered_set<std::reference_wrapper<const bitblast::AigNode>,
                         std::hash<bitblast::AigNode>>;
  template <class T>
  using unordered_aig_node_ref_map =
      std::unordered_map<std::reference_wrapper<const bitblast::AigNode>,
                         T,
                         std::hash<bitblast::AigNode>>;

  AigBitblaster(bool bool_bv1_mode = false) : d_bool_bv1_mode(bool_bv1_mode) {};

  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term);

  /** Return encoded bits associated with bit-blasted term. */
  const bitblast::AigBitblaster::Bits& bits(const Node& term) const;

  uint64_t num_aig_ands() const { return d_bitblaster.num_aig_ands(); }
  uint64_t num_aig_consts() const { return d_bitblaster.num_aig_consts(); }
  uint64_t num_aig_shared() const { return d_bitblaster.num_aig_shared(); }

  /** @return The associated AIG manager. */
  bitblast::AigManager& amgr() { return d_bitblaster.amgr(); }

  /**
   * Get AigNode by id.
   * @param id The id of the AIG node.
   * @return The AIG node.
   */
  bitblast::AigNode get_node(int64_t id) { return d_bitblaster.get_node(id); }

  /**
   * Record the term each AIG input created from now on is created for, see
   * input_term_id().
   */
  void track_input_terms() { d_track_input_terms = true; }

  /**
   * @return The id of the term the given AIG input was created for, 0 if it
   *         was created while input terms were not tracked.
   */
  uint64_t input_term_id(const bitblast::AigNode& aig) const
  {
    auto it = d_input_term_ids.find(std::abs(aig.get_id()));
    return it == d_input_term_ids.end() ? 0 : it->second;
  }

  const std::unordered_map<Node, bitblast::AigBitblaster::Bits>&
  bitblaster_cache() const
  {
    return d_bitblaster_cache;
  }

 protected:
  bitblast::AigBitblaster::Bits d_empty;

  /** AIG bit-blaster. */
  bitblast::AigBitblaster d_bitblaster;
  /** Cached to store bit-blasted terms and their encoded bits. */
  std::unordered_map<Node, bitblast::AigBitblaster::Bits> d_bitblaster_cache;

  bool d_bool_bv1_mode = false;

  /** @return Fresh AIG inputs of given size, created for `term`. */
  bitblast::AigBitblaster::Bits mk_inputs(const Node& term, uint64_t size);

  /** Indicates whether input terms are tracked. */
  bool d_track_input_terms = false;
  /** Maps AIG input id to the id of the term it was created for. */
  std::unordered_map<int64_t, uint64_t> d_input_term_ids;
};

}  // namespace bzla::bv

#endif
