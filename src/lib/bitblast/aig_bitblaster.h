/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
