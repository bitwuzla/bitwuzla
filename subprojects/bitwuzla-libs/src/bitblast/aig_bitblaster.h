#ifndef BZLA__BITBLAST_AIG_BITBLASTER_H
#define BZLA__BITBLAST_AIG_BITBLASTER_H

#include "bitblast/aig/aig_manager.h"

namespace bzla::bb {

class AigBitblaster : public BitblasterInterface<AigNode>
{
 public:
  /** @return Number of created AND gates. */
  uint64_t num_aig_ands() const;
  /** @return Number of AIG constants. */
  uint64_t num_aig_consts() const;
  /** @return Number of shared AND gates. */
  uint64_t num_aig_shared() const;
};

}  // namespace bzla::bb

#endif
