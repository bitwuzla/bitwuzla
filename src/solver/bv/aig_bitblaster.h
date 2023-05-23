#ifndef BZLA_SOLVER_BV_AIG_BITBLASTER_H_INCLUDED
#define BZLA_SOLVER_BV_AIG_BITBLASTER_H_INCLUDED

#include "bitblast/aig_bitblaster.h"
#include "node/node.h"

namespace bzla::bv {

class AigBitblaster
{
 public:
  /** Recursively bit-blast `term`. */
  void bitblast(const Node& term);

  /** Return encoded bits associated with bit-blasted term. */
  const bb::AigBitblaster::Bits& bits(const Node& term) const;

  uint64_t num_aig_ands() const { return d_bitblaster.num_aig_ands(); }
  uint64_t num_aig_consts() const { return d_bitblaster.num_aig_consts(); }
  uint64_t num_aig_shared() const { return d_bitblaster.num_aig_shared(); }

 private:
  const bb::AigBitblaster::Bits d_empty;

  /** AIG bit-blaster. */
  bb::AigBitblaster d_bitblaster;
  /** Cached to store bit-blasted terms and their encoded bits. */
  std::unordered_map<Node, bb::AigBitblaster::Bits> d_bitblaster_cache;
};

}  // namespace bzla::bv

#endif
