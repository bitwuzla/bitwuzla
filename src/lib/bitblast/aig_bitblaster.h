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
#include "bitblast/aig/aig_node.h"
#include "bitblast/bitblaster.h"

namespace bzla::bitblast {

template <>
class BitInterface<AigNode>
{
 public:
  AigNode mk_false() { return d_amgr.mk_false(); }

  AigNode mk_true() { return d_amgr.mk_true(); }

  AigNode mk_bit() { return d_amgr.mk_const(); }

  AigNode mk_not(const AigNode& a) { return d_amgr.mk_not(a); }

  AigNode mk_and(const AigNode& a, const AigNode& b)
  {
    return d_amgr.mk_and(a, b);
  }

  AigNode mk_or(const AigNode& a, const AigNode& b)
  {
    return mk_not(mk_and(mk_not(a), mk_not(b)));
  }

  AigNode mk_iff(const AigNode& a, const AigNode& b)
  {
    return mk_and(mk_not(mk_and(a, mk_not(b))), mk_not(mk_and(mk_not(a), b)));
  }

  AigNode mk_ite(const AigNode& c, const AigNode& a, const AigNode& b)
  {
    return mk_or(mk_and(c, a), mk_and(mk_not(c), b));
  }

  const auto& statistics() const { return d_amgr.statistics(); }

 private:
  AigManager d_amgr;
};

class AigBitblaster : public BitblasterInterface<AigNode>
{
 public:
  /** @return Number of created AND gates. */
  uint64_t num_aig_ands() const { return d_bit_mgr.statistics().num_ands; }

  /** @return Number of AIG constants. */
  uint64_t num_aig_consts() const { return d_bit_mgr.statistics().num_consts; }

  /** @return Number of shared AND gates. */
  uint64_t num_aig_shared() const { return d_bit_mgr.statistics().num_shared; }
};

}  // namespace bzla::bitblast

#endif
