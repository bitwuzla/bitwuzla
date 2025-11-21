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

#include "node/node_kind.h"

namespace bzla::bv {

/* --- BvInverter public ---------------------------------------------------- */

BvInverter::BvInverter(Env& env) : d_nm(env.nm()) {}

BvInverter::~BvInverter() {}

Node
BvInverter::ic(Kind predicate, Kind kind, const std::vector<Node>& nodes)
{
  assert(nodes.size() > 1);
  switch (predicate)
  {
    case Kind::BV_SLT: return ic_bv_slt(kind, nodes);
    case Kind::BV_SLE: return ic_bv_sle(kind, nodes);
    case Kind::BV_SGT: return ic_bv_sgt(kind, nodes);
    case Kind::BV_SGE: return ic_bv_sge(kind, nodes);

    case Kind::BV_ULT: return ic_bv_ult(kind, nodes);
    case Kind::BV_ULE: return ic_bv_ule(kind, nodes);
    case Kind::BV_UGT: return ic_bv_ugt(kind, nodes);
    case Kind::BV_UGE: return ic_bv_uge(kind, nodes);

    case Kind::EQUAL: return ic_equal(kind, nodes);
    case Kind::DISTINCT: return ic_distinct(kind, nodes);

    default: assert(false);
  }
}

/* --- BvInverter private --------------------------------------------------- */

Node
BvInverter::ic_equal(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_eq_mul(s, t);
    default: assert(false);
  }
}

Node
BvInverter::ic_distinct(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_dist_mul(s, t);
    default: assert(false);
  }
}

Node
BvInverter::ic_bv_slt(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_slt_mul(s, t);
    default:
      // IC: (distinct t min_signed_[w])
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_min_signed(s.type().bv_size()))});
  }
}

Node
BvInverter::ic_bv_sle(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_sle_mul(s, t);
    default:
      // IC: true
      return d_nm.mk_value(true);
  }
}

Node
BvInverter::ic_bv_sgt(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_sgt_mul(s, t);
    default:
      // IC: (distinct t max_signed_[w])
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_max_signed(s.type().bv_size()))});
  }
}

Node
BvInverter::ic_bv_sge(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_sge_mul(s, t);
    default:
      // IC: true
      return d_nm.mk_value(true);
  }
}

Node
BvInverter::ic_bv_ult(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_ult_mul(s, t);
    default:
      // IC: (distinct t (_ bv0 w))
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))});
  }
}

Node
BvInverter::ic_bv_ugt(Kind kind, const std::vector<Node>& nodes)
{
  const Node& t = nodes.back();
  const Node& s = nodes[nodes.size() - 2];
  switch (kind)
  {
    case Kind::BV_MUL: assert(nodes.size() == 3); return ic_bv_ugt_mul(s, t);
    default:
      // IC: (distinct t (bvnot (_ bv0 w)))
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_ones(s.type().bv_size()))});
  }
}

/* --- BV_MUL --------------------------------------------------------------- */

Node
BvInverter::ic_eq_mul(const Node& s, const Node& t)
{
  // x * s = t
  // IC: (= (bvand (bvor (bvneg s) s) t) t)
  return d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(
           Kind::BV_AND,
           {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s})}),
       t});
}

Node
BvInverter::ic_dist_mul(const Node& s, const Node& t)
{
  // x * s = t
  // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
  Node zero = d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()));
  return d_nm.mk_node(Kind::OR,
                      {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                       d_nm.mk_node(Kind::DISTINCT, {t, zero})});
}

Node
BvInverter::ic_bv_ult_mul(const Node& s, const Node& t)
{
  // x * s <_u t
  // IC: (distinct t 0_[w])
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))});
}

Node
BvInverter::ic_bv_ule_mul(const Node& s, const Node& t)
{
  (void) s;
  (void) t;
  // x * s <=_u t
  // IC: true
  return d_nm.mk_value(true);
}

Node
BvInverter::ic_bv_ugt_mul(const Node& s, const Node& t)
{
  // x * s >_u t
  // IC: (bvult t (bvor (bvneg s) s))
  return d_nm.mk_node(
      Kind::BV_ULT,
      {t, d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s})});
}

Node
BvInverter::ic_bv_uge_mul(const Node& s, const Node& t)
{
  // x * s >=_u t
  // IC: (bvuge (bvor (bvneg s) s) t)
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}), t});
}

Node
BvInverter::ic_bv_slt_mul(const Node& s, const Node& t)
{
  // x * s <_s t
  // IC: (bvslt (bvand (bvnot (bvneg t)) (bvor (bvneg s) s)) t)
  return d_nm.mk_node(
      Kind::BV_SLT,
      {d_nm.mk_node(
           Kind::BV_AND,
           {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
            d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s})}),
       t});
}

Node
BvInverter::ic_bv_sle_mul(const Node& s, const Node& t)
{
  (void) s;
  (void) t;
  // x * s <=_s t
  // IC: (not (and (= s z) (bvslt t s)))
  return d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(
               Kind::EQUAL,
               {s, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))}),
           d_nm.mk_node(Kind::BV_SLT, {t, s})})});
}

Node
BvInverter::ic_bv_sgt_mul(const Node& s, const Node& t)
{
  // x * s >_s t
  // IC: (bvslt t (bvsub t (bvor (bvor s t) (bvneg s))))  */
  return d_nm.mk_node(
      Kind::BV_SLT,
      {t,
       d_nm.mk_node(Kind::BV_SUB,
                    {t,
                     d_nm.mk_node(Kind::BV_OR,
                                  {d_nm.mk_node(Kind::BV_OR, {s, t}),
                                   d_nm.mk_node(Kind::BV_NEG, {s})})})});
}

Node
BvInverter::ic_bv_sge_mul(const Node& s, const Node& t)
{
  // x * s >=_s t
  // IC: (bvsge (bvand (bvor (bvneg s) s) max) t)
  return d_nm.mk_node(
      Kind::BV_SGE,
      {d_nm.mk_node(
           Kind::BV_AND,
           {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
            d_nm.mk_value(BitVector::mk_max_signed(s.type().bv_size()))}),
       t});
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::bv
