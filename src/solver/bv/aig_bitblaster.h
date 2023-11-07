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
  using AigNodeRefSet =
      std::unordered_set<std::reference_wrapper<const bitblast::AigNode>,
                         std::hash<bitblast::AigNode>>;

  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term);

  /** Return encoded bits associated with bit-blasted term. */
  const bitblast::AigBitblaster::Bits& bits(const Node& term) const;

  /** Count number of AIG nodes in term. */
  uint64_t count_aig_ands(const Node& term, AigNodeRefSet& cache);

  uint64_t num_aig_ands() const { return d_bitblaster.num_aig_ands(); }
  uint64_t num_aig_consts() const { return d_bitblaster.num_aig_consts(); }
  uint64_t num_aig_shared() const { return d_bitblaster.num_aig_shared(); }

 private:
  bitblast::AigBitblaster::Bits d_empty;

  /** AIG bit-blaster. */
  bitblast::AigBitblaster d_bitblaster;
  /** Cached to store bit-blasted terms and their encoded bits. */
  std::unordered_map<Node, bitblast::AigBitblaster::Bits> d_bitblaster_cache;
};

}  // namespace bzla::bv

#endif
