/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/bv/bv_inverter.h"

#include <cassert>

namespace bzla::bv {

/* --- BvInverter public ---------------------------------------------------- */

BvInverter::BvInverter(Env& env) : d_nm(env.nm()) {}

BvInverter::~BvInverter() {}

Node
BvInverter::ic(Kind kind, const Node& x, const Node& s, const Node& t)
{
  switch (kind)
  {
    case Kind::BV_UGE:
    case Kind::BV_ULE: return d_nm.mk_value(true);

    case Kind::BV_ULT: return ic_bv_ult(x, t);
    case Kind::BV_UGT: return ic_bv_ugt(x, t);

    default: assert(false);
  }
}

/* --- BvInverter private --------------------------------------------------- */

Node
BvInverter::ic_bv_ult(const Node& x, const Node& t)
{
  // IC: t != 0_[w]
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()))});
}

Node
BvInverter::ic_bv_ugt(const Node& x, const Node& t)
{
  // IC: t != ~0_[w]
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_ones(x.type().bv_size()))});
}

}  // namespace bzla::bv
