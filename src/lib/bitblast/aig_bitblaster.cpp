/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
