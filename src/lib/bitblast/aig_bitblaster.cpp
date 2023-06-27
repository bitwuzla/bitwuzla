#include "bitblast/aig_bitblaster.h"

namespace bzla::bb {

uint64_t
AigBitblaster::num_aig_ands() const
{
  return d_bit_mgr.statistics().num_ands;
}

uint64_t
AigBitblaster::num_aig_consts() const
{
  return d_bit_mgr.statistics().num_consts;
}

uint64_t
AigBitblaster::num_aig_shared() const
{
  return d_bit_mgr.statistics().num_shared;
}

}  // namespace bzla::bb
