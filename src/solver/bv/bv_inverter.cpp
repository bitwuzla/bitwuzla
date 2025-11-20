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
    case Kind::BV_SGE:
    case Kind::BV_SLE:
    case Kind::BV_UGE:
    case Kind::BV_ULE: return d_nm.mk_value(true);

    case Kind::BV_SLT: return ic_bv_slt(x, t);
    case Kind::BV_SGT: return ic_bv_sgt(x, t);
    case Kind::BV_ULT: return ic_bv_ult(x, t);
    case Kind::BV_UGT: return ic_bv_ugt(x, t);

    default: assert(false);
  }
}

/* --- BvInverter private --------------------------------------------------- */

Node
BvInverter::ic_bv_slt(const Node& x, const Node& t)
{
  // IC: (distinct t min_signed_[w])
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_min_signed(x.type().bv_size()))});
}

Node
BvInverter::ic_bv_sgt(const Node& x, const Node& t)
{
  // IC: (distinct t max_signed_[w])
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_max_signed(x.type().bv_size()))});
}

Node
BvInverter::ic_bv_ult(const Node& x, const Node& t)
{
  // IC: (distinct t (_ bv0 w))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()))});
}

Node
BvInverter::ic_bv_ugt(const Node& x, const Node& t)
{
  // IC: (distinct t (bvnot (_ bv0 w)))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_ones(x.type().bv_size()))});
}

}  // namespace bzla::bv
