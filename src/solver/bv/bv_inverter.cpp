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
#include "node/node_utils.h"

namespace bzla::bv {

/* --- BvInverter public ---------------------------------------------------- */

BvInverter::BvInverter(Env& env) : d_nm(env.nm()) {}

BvInverter::~BvInverter() {}

Node
BvInverter::ic(Kind predicate,
               Kind kind,
               const std::vector<Node>& nodes,
               size_t idx)
{
  assert(nodes.size() > 1);
  assert(idx < 2);
  switch (kind)
  {
    case Kind::BV_AND: return ic_bv_and(predicate, nodes, idx);
    case Kind::BV_ASHR: return ic_bv_ashr(predicate, nodes, idx);
    case Kind::BV_CONCAT: return ic_bv_concat(predicate, nodes, idx);
    case Kind::BV_MUL: return ic_bv_mul(predicate, nodes, idx);
    case Kind::BV_SHR: return ic_bv_shr(predicate, nodes, idx);
    case Kind::BV_SHL: return ic_bv_shl(predicate, nodes, idx);
    case Kind::BV_SIGN_EXTEND: return ic_bv_sext(predicate, nodes, idx);
    case Kind::BV_UREM: return ic_bv_urem(predicate, nodes, idx);
    case Kind::BV_UDIV: return ic_bv_udiv(predicate, nodes, idx);
    default:
      assert(nodes.size() == 2);
      size_t bw = nodes[idx].type().bv_size();
      switch (predicate)
      {
        case Kind::BV_SLT:
        case Kind::BV_SGT:
          if ((predicate == Kind::BV_SLT && idx == 0)
              || (predicate == Kind::BV_SGT && idx == 1))
          {
            // x <_s t
            // t >_s x
            // IC: (distinct t min_signed_[w])
            return d_nm.mk_node(
                Kind::DISTINCT,
                {nodes[1 - idx], d_nm.mk_value(BitVector::mk_min_signed(bw))});
          }
          // x >_s t
          // t <_s x
          // IC: (distinct t max_signed_[w])
          return d_nm.mk_node(
              Kind::DISTINCT,
              {nodes[1 - idx], d_nm.mk_value(BitVector::mk_max_signed(bw))});
        case Kind::BV_ULT:
        case Kind::BV_UGT:
          if ((predicate == Kind::BV_ULT && idx == 0)
              || (predicate == Kind::BV_UGT && idx == 1))
          {
            // x <_u t
            // t >_u x
            // IC: (distinct t (_ bv0 w))
            return d_nm.mk_node(
                Kind::DISTINCT,
                {nodes[1 - idx], d_nm.mk_value(BitVector::mk_zero(bw))});
          }
          // x >_u t
          // t <_u x
          // IC: (distinct t (bvnot (_ bv0 w)))
          return d_nm.mk_node(
              Kind::DISTINCT,
              {nodes[1 - idx], d_nm.mk_value(BitVector::mk_ones(bw))});

        case Kind::BV_UGE:
          // x >=_u t
        case Kind::BV_ULE:
          // x <=_u t
        case Kind::BV_SGE:
          // x >=_s t
        case Kind::BV_SLE:
          // x <=_s t
        case Kind::DISTINCT:
          // x != t
        case Kind::EQUAL:
          // x = t
          // IC: true
          return d_nm.mk_value(true);

        default: assert(false);
      }
  }
}

/* --- BvInverter private --------------------------------------------------- */

Node
BvInverter::ic_bv_and(Kind predicate,
                      const std::vector<Node>& nodes,
                      size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x & s <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x & s <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x & s >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x & s >=_u t
      // IC: (bvuge s t)
      return d_nm.mk_node(Kind::BV_UGE, {s, t});

    case Kind::BV_SLT:
      // x & s <_s t
      // IC: (bvslt (bvand (bvnot (bvneg t)) s) t)
      return d_nm.mk_node(
          Kind::BV_SLT,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                s}),
           t});

    case Kind::BV_SLE:
      // x & s <=_s t
      // IC: (bvuge s (bvand t min_signed_[w]))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::BV_UGE,
                            {s, d_nm.mk_node(Kind::BV_AND, {t, mins})});
      }

    case Kind::BV_SGT:
      // x & s >_s t
      // IC: (bvslt t (bvand s max_sigend_[w]))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(Kind::BV_SLT,
                            {t, d_nm.mk_node(Kind::BV_AND, {s, maxs})});
      }

    case Kind::BV_SGE:
      // x & s >=_s t
      // IC: (or (= (bvand s t) t) (bvslt t (bvand (bvsub t s) s)))
      return d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {s, t}), t}),
           d_nm.mk_node(
               Kind::BV_SLT,
               {t,
                d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_node(Kind::BV_SUB, {t, s}), s})})});

    case Kind::DISTINCT:
      // x & s != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x & s = t
      // IC: (= (bvand t s) t)
      return d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {t, s}), t});
  }
}

Node
BvInverter::ic_bv_mul(Kind predicate,
                      const std::vector<Node>& nodes,
                      size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x * s <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x * s <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x * s >_u t
      // IC: (bvult t (bvor (bvneg s) s))
      return d_nm.mk_node(
          Kind::BV_ULT,
          {t, d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s})});

    case Kind::BV_UGE:
      // x * s >=_u t
      // IC: (bvuge (bvor (bvneg s) s) t)
      return d_nm.mk_node(
          Kind::BV_UGE,
          {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}), t});

    case Kind::BV_SLT:
      // x * s <_s t
      // IC: (bvslt (bvand (bvnot (bvneg t)) (bvor (bvneg s) s)) t)
      return d_nm.mk_node(
          Kind::BV_SLT,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                d_nm.mk_node(Kind::BV_OR,
                             {d_nm.mk_node(Kind::BV_NEG, {s}), s})}),
           t});

    case Kind::BV_SLE:
      // x * s <=_s t
      // IC: (not (and (= s z) (bvslt t s)))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::NOT,
            {d_nm.mk_node(Kind::AND,
                          {d_nm.mk_node(Kind::EQUAL, {s, zero}),
                           d_nm.mk_node(Kind::BV_SLT, {t, s})})});
      }

    case Kind::BV_SGT:
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

    case Kind::BV_SGE:
      // x * s >=_s t
      // IC: (bvsge (bvand (bvor (bvneg s) s) max_signed_[w]) t)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_OR,
                                        {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
                           maxs}),
             t});
      }

    case Kind::DISTINCT:
      // x * s != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    default:
      assert(predicate == Kind::EQUAL);
      // x * s = t
      // IC: (= (bvand (bvor (bvneg s) s) t) t)
      return d_nm.mk_node(
          Kind::EQUAL,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
                t}),
           t});
  }
}

Node
BvInverter::ic_bv_udiv(Kind predicate,
                       const std::vector<Node>& nodes,
                       size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT: {
      // x / s <_u t
      // IC: (and (bvult 0_[w] s) (bvult 0_[w] t))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::AND,
                            {d_nm.mk_node(Kind::BV_ULT, {zero, s}),
                             d_nm.mk_node(Kind::BV_ULT, {zero, t})});
      }
      // s / x <_u t
      // IC: (and (bvult 0_[w] (bvnot (bvand (bvneg t) s))) (bvult 0_[w] t))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(
               Kind::BV_ULT,
               {zero,
                d_nm.mk_node(
                    Kind::BV_NOT,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {d_nm.mk_node(Kind::BV_NEG, {t}), s})})}),
           d_nm.mk_node(Kind::BV_ULT, {zero, t})});
    }

    case Kind::BV_ULE:
      // x / s <=_u t
      // IC: (bvuge (bvor s t) (bvnot (bvneg s)))
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_OR, {s, t}),
             d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})})});
      }
      // s / x <=_u t
      // IC: (bvult 0_[w] (bvor (bvnot s) t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::BV_ULT,
            {zero,
             d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NOT, {s}), t})});
      }

    case Kind::BV_UGT: {
      // x / s >_u t
      // IC: (bvugt (bvudiv ~0_[w] s) t)
      Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::BV_UGT,
                            {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t});
      }
      // s / x >_u t
      // IC: (bvult t ~0_[w])
      return d_nm.mk_node(Kind::BV_ULT, {t, ones});
    }

    case Kind::BV_UGE:
      // x / s >=_u t
      // IC: (= (bvand (bvudiv (bvmul s t) t) s) s)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(
                 Kind::BV_AND,
                 {d_nm.mk_node(Kind::BV_UDIV,
                               {d_nm.mk_node(Kind::BV_MUL, {s, t}), t}),
                  s}),
             s});
      }
      // s / x >=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_SLT: {
      // x / s <_s t
      // IC: (=> (bvsle t 0_[w]) (bvslt (bvudiv min_signed_[w] s) t))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(
            Kind::IMPLIES,
            {d_nm.mk_node(Kind::BV_SLE, {t, zero}),
             d_nm.mk_node(Kind::BV_SLT,
                          {d_nm.mk_node(Kind::BV_UDIV, {mins, s}), t})});
      }
      // s / x <_s t
      // IC: (or (bvslt s t) (bvsge t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                           d_nm.mk_node(Kind::BV_SGE, {t, zero})});
    }

    case Kind::BV_SLE:
      // x / s <=_s t
      // IC: (or
      //       (= (bvudiv (bvmul s t) s) t)
      //       (=> (bvsle t 0_[w]) (bvslt (bvudiv min_signed_[w] s) t)))
      if (idx == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(
                 Kind::EQUAL,
                 {d_nm.mk_node(Kind::BV_UDIV,
                               {d_nm.mk_node(Kind::BV_MUL, {s, t}), s}),
                  t}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLE, {t, zero}),
                  d_nm.mk_node(Kind::BV_SLT,
                               {d_nm.mk_node(Kind::BV_UDIV, {mins, s}), t})})});
      }
      // s / x <=_s t
      // IC: (or (bvsge t ~0_[w]) (bvsge t s))
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SGE, {t, ones}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT:
      // x / s >_s t
      // IC: (or
      //       (bvsgt (bvudiv ~0_[w] s) t)
      //       (bvsgt (bvudiv max_signed_[w] s) t))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {
                d_nm.mk_node(Kind::BV_SGT,
                             {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t}),
                d_nm.mk_node(Kind::BV_SGT,
                             {d_nm.mk_node(Kind::BV_UDIV, {maxs, s}), t}),
            });
      }
      // s / x >_s t
      // IC: w > 1: (and
      //              (=> (bvsge s 0_[w]) (bvsgt s t))
      //              (=> (bvslt s 0_[w]) (bvsgt (bvlshr s (_ bv1 w)) t)))
      //     w = 1: (bvsgt s t)
      if (bw > 1)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGT, {s, t})}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGT,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})})});
      }
      return d_nm.mk_node(Kind::BV_SGT, {s, t});

    case Kind::BV_SGE:
      // x / s >=_s t
      // IC: (or
      //       (bvsge (bvudiv ~0_[w] s) t)
      //       (bvsge (bvudiv max_signed_[w] s) t))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_UDIV, {ones, s}), t}),
             d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_UDIV, {maxs, s}), t})});
      }
      // s / x >=_s t
      // IC: w > 1: (and
      //              (=> (bvsge s 0_[w]) (bvsge s t))
      //              (=> (bvslt s 0_[w]) (bvsge (bvlshr s (_ bv1 w)) t)))
      //     w = 1: (bvsge s t)
      if (bw > 1)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGE, {s, t})}),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGE,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})})});
      }
      return d_nm.mk_node(Kind::BV_SGE, {s, t});

    case Kind::DISTINCT: {
      // x / s != t
      // IC: (or (distinct s 0_[w]) (distinct t ~0_[w]))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                             d_nm.mk_node(Kind::DISTINCT, {t, ones})});
      }
      // s / x != t
      // IC: w > 1: true
      //     w = 1: (= (bvand s t) 0_[w])
      if (bw > 1)
      {
        return d_nm.mk_value(true);
      }
      return d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_AND, {s, t}), zero});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x / s = t
      // IC: (= (bvudiv (bvmul s t) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_UDIV,
                          {d_nm.mk_node(Kind::BV_MUL, {s, t}), s}),
             t});
      }
      // s / x = t
      // IC: (= (bvudiv s (bvudiv s t)) t)
      return d_nm.mk_node(
          Kind::EQUAL,
          {d_nm.mk_node(Kind::BV_UDIV,
                        {s, d_nm.mk_node(Kind::BV_UDIV, {s, t})}),
           t});
  }
}

Node
BvInverter::ic_bv_urem(Kind predicate,
                       const std::vector<Node>& nodes,
                       size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x mod s <_u t
      // s mod x <_u t
      // IC: (distinct t 0_[w])
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x mod s <=_u t
      // s mod x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x mod s >_u t
      // IC: (bvult t (bvnot (bvneg s)))
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {t, d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})})});
      }
      // s mod x >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x mod s >=_u t
      // IC: (bvuge (bvnot (bvneg s)) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})}), t});
      }
      // s mod x >=_u t
      // IC: (or (bvuge (bvand (bvsub (bvadd t t) s) s) t) (bvult t s))
      return d_nm.mk_node(
          Kind::OR,
          {
              d_nm.mk_node(
                  Kind::BV_UGE,
                  {d_nm.mk_node(
                       Kind::BV_AND,
                       {d_nm.mk_node(Kind::BV_SUB,
                                     {d_nm.mk_node(Kind::BV_ADD, {t, t}), s}),
                        s}),
                   t}),
              d_nm.mk_node(Kind::BV_ULT, {t, s}),
          });

    case Kind::BV_SLT:
      // x mod s <_s t
      // IC: (bvslt (bvnot t) (bvor (bvneg s) (bvneg t)))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::BV_SLT,
                            {d_nm.mk_node(Kind::BV_NOT, {t}),
                             d_nm.mk_node(Kind::BV_OR,
                                          {d_nm.mk_node(Kind::BV_NEG, {s}),
                                           d_nm.mk_node(Kind::BV_NEG, {t})})});
      }
      // s mod x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {
                                d_nm.mk_node(Kind::BV_SLT, {s, t}),
                                d_nm.mk_node(Kind::BV_SLT, {zero, t}),
                            });
      }

    case Kind::BV_SLE:
      // x mod s <=_s t
      // IC: (bvslt ~0_[w] (bvand (bvneg s) t))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {ones,
             d_nm.mk_node(Kind::BV_AND, {d_nm.mk_node(Kind::BV_NEG, {s}), t})});
      }
      // s mod x <=_s t
      // IC: (or (bvult t min) (bvsge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {t, mins}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT: {
      // x mod s >_s t
      // IC: (and
      //       (and
      //         (=> (bvsgt s 0_[w]) (bvslt t (bvnot (bvneg s))))
      //         (=> (bvsle s 0_[w]) (distinct t max_signed_[w])))
      //       (or (distinct t 0_[w]) (distinct s (_ bv1 w))))
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      Node one  = d_nm.mk_value(BitVector::mk_one(bw));
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::AND,
                 {
                     d_nm.mk_node(
                         Kind::IMPLIES,
                         {d_nm.mk_node(Kind::BV_SGT, {s, zero}),
                          d_nm.mk_node(Kind::BV_SLT,
                                       {t,
                                        d_nm.mk_node(Kind::BV_NOT,
                                                     {d_nm.mk_node(Kind::BV_NEG,
                                                                   {s})})})}),
                     d_nm.mk_node(Kind::IMPLIES,
                                  {d_nm.mk_node(Kind::BV_SLE, {s, zero}),
                                   d_nm.mk_node(Kind::DISTINCT, {t, maxs})}),
                 }),
             d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {s, one})})});
      }
      // s mod x >_s t
      // IC: (and
      //       (=> (bvsge s 0_[w]) (bvsgt s t))
      //       (=> (bvslt s 0_[w])
      //           (bvsgt (bvlshr (bvsub s (_ bv1 w)) (_ bv1 w)) t)))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGT, {s, t})}),
           d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                d_nm.mk_node(
                    Kind::BV_SGT,
                    {d_nm.mk_node(Kind::BV_SHR,
                                  {d_nm.mk_node(Kind::BV_DEC, {s}), one}),
                     t})})});
    }

    case Kind::BV_SGE: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x mod s >=_s t
      // IC: (or (bvslt t s) (bvsge 0_[w] s))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {t, s}),
                             d_nm.mk_node(Kind::BV_SGE, {zero, s})});
      }
      // s mod x >=_s t
      // IC: (and
      //       (=> (bvsge s 0_[w]) (bvsge s t))
      //       (=> (and (bvslt s 0_[w]) (bvsge t 0_[w])) (bvugt (bvsub s t) t)))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGE, {s, t})}),
           d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::AND,
                             {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                              d_nm.mk_node(Kind::BV_SGE, {t, zero})}),
                d_nm.mk_node(Kind::BV_UGT,
                             {d_nm.mk_node(Kind::BV_SUB, {s, t}), t})})});
    }

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x mod s != t
      // IC: (or (distinct s (_ bv1 w)) (distinct t 0_[w]))
      if (idx == 0)
      {
        Node one = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(Kind::OR,
                            {
                                d_nm.mk_node(Kind::DISTINCT, {s, one}),
                                d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                            });
      }
      // s mod x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x mod s = t
      // IC: (bvuge (bvnot (bvneg s)) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_UGE,
            {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})}), t});
      }
      // s mod x = t
      // IC: (bvuge (bvand (bvsub (bvadd t t) s) s) t)
      return d_nm.mk_node(
          Kind::BV_UGE,
          {d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_SUB,
                                      {d_nm.mk_node(Kind::BV_ADD, {t, t}), s}),
                         s}),
           t});
  }
}

namespace {
Node
_ic_shift_for_all_i(NodeManager& nm, Kind predicate, Kind kind, Node s, Node t)
{
  std::vector<Node> args;
  uint64_t bw = s.type().bv_size();
  for (uint64_t i = 0; i <= bw; ++i)
  {
    args.push_back(nm.mk_node(
        predicate,
        {nm.mk_node(kind, {s, nm.mk_value(BitVector::from_ui(bw, i))}), t}));
  }
  return utils::mk_nary(nm, Kind::OR, args);
}
}  // namespace

Node
BvInverter::ic_bv_shr(Kind predicate,
                      const std::vector<Node>& nodes,
                      size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x >> s <_u t
      // s >> x <_u t
      // IC: (distinct t 0_[w])
      return d_nm.mk_node(Kind::DISTINCT, {t, zero});
    }

    case Kind::BV_ULE:
      // x >> s <=_u t
      // s >> x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x >> s >_u t
      // IC: (bvult t (bvlshr (bvnot s) s))
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {t,
             d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_node(Kind::BV_NOT, {s}), s})});
      }
      // s >> x >_u t
      // IC: (bvult t s)
      return d_nm.mk_node(Kind::BV_ULT, {t, s});

    case Kind::BV_UGE:
      // x >> s >=_u t
      // IC: (= (bvlshr (bvshl t s) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
             t});
      }
      // s >> x >=_u t
      // IC: (bvuge s t)
      return d_nm.mk_node(Kind::BV_UGE, {s, t});

    case Kind::BV_SLT:
      // x >> s <_s t
      // IC: (bvslt (bvlshr (bvnot (bvneg t)) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_SLT,
            {d_nm.mk_node(
                 Kind::BV_SHR,
                 {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {t})}),
                  s}),
             t});
      }
      // s >> x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                             d_nm.mk_node(Kind::BV_SLT, {zero, t})});
      }

    case Kind::BV_SLE:
      // x >> s <=_s t
      // IC: (bvsge t (bvlshr t s))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::BV_SGE,
                            {t, d_nm.mk_node(Kind::BV_SHR, {t, s})});
      }
      // s >> x <=_s t
      // IC: (or (bvult t min_signed_[w]) (bvsge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {t, mins}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT:
      // x >> s >_s t
      // IC: (bvslt t (bvlshr (bvshl max_signed_[w] s) s))
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {t,
             d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), s})});
      }
      // s >> x >_s t
      // IC: (and
      //       (=> (bvslt s 0_[w]) (bvsgt (bvlshr s 1_[w]) t))
      //       (=> (bvsge s 0_[w]) (bvsgt s t)))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node one  = d_nm.mk_value(BitVector::mk_one(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                  d_nm.mk_node(Kind::BV_SGT,
                               {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                           d_nm.mk_node(Kind::BV_SGT, {s, t})})});
      }

    case Kind::BV_SGE: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x >> s >=_s t
      // IC: (=> (not (= s 0_[w])) (bvsge (bvlshr ~0_[w] s) t))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::IMPLIES,
            {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
             d_nm.mk_node(Kind::BV_SGE,
                          {d_nm.mk_node(Kind::BV_SHR, {ones, s}), t})});
      }
      // s >> x >=_s t
      // IC: (and
      //       (=> (bvslt s 0_[w]) (bvsge (bvlshr s 1_[w]) t))
      //       (=> (bvsge s 0_[w]) (bvsge s t)))
      Node one = d_nm.mk_value(BitVector::mk_one(bw));
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(
               Kind::IMPLIES,
               {d_nm.mk_node(Kind::BV_SLT, {s, zero}),
                d_nm.mk_node(Kind::BV_SGE,
                             {d_nm.mk_node(Kind::BV_SHR, {s, one}), t})}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::BV_SGE, {s, zero}),
                         d_nm.mk_node(Kind::BV_SGE, {s, t})})});
    }

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      Node w    = d_nm.mk_value(BitVector::from_ui(bw, bw));
      // x >> s != t
      // IC: (or (distinct t 0_[w]) (bvult s w_[w]))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, w})});
      }
      // s >> x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x >> s = t
      // IC: (= (bvlshr (bvshl t s) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHR,
                          {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
             t});
      }
      // s >> x = t
      // IC: (or (= (bvlshr s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_SHR, s, t);
  }
}

Node
BvInverter::ic_bv_ashr(Kind predicate,
                       const std::vector<Node>& nodes,
                       size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x >>a s <_u t
      // IC: (distinct t 0_[w])
      if (idx == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }
      // s >>a x <_u t
      // IC: (and (or (bvult s t) (bvsge s 0_[w])) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::BV_ULT, {s, t}),
                           d_nm.mk_node(Kind::BV_SGE, {s, zero})}),
             d_nm.mk_node(Kind::DISTINCT, {t, zero})});
      }

    case Kind::BV_ULE:
      // x >>a s <=_u t
      // IC: true
      if (idx == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x <=_u t
      // IC: (or (bvult s min_signed_[w]) (bvuge t s))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_ULT, {s, mins}),
                             d_nm.mk_node(Kind::BV_UGE, {t, s})});
      }

    case Kind::BV_UGT:
      // x >>a s >_u t
      // IC: (bvult t ~0_[w])
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_ULT, {t, ones});
      }
      // s >>a x >_u t
      // IC: (or (bvslt s (bvlshr s (bvnot t))) (bvult t s))
      return d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_node(Kind::BV_SLT,
                        {s,
                         d_nm.mk_node(Kind::BV_SHR,
                                      {s, d_nm.mk_node(Kind::BV_NOT, {t})})}),
           d_nm.mk_node(Kind::BV_ULT, {t, s})});

    case Kind::BV_UGE:
      // x >>a s >=_u t
      // IC: true
      if (idx == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x >=_u t
      // IC: (not (and (bvult s (bvnot s)) (bvult s t)))
      return d_nm.mk_node(
          Kind::NOT,
          {d_nm.mk_node(
              Kind::AND,
              {d_nm.mk_node(Kind::BV_ULT, {s, d_nm.mk_node(Kind::BV_NOT, {s})}),
               d_nm.mk_node(Kind::BV_ULT, {s, t})})});

    case Kind::BV_SLT:
      // x >>a s <_s t
      // IC: (bvslt (bvashr min_signed_[w] s) t)
      if (idx == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
        return d_nm.mk_node(Kind::BV_SLT,
                            {d_nm.mk_node(Kind::BV_ASHR, {mins, s}), t});
      }
      // s >>a x <_s t
      // IC: (or (bvslt s t) (bvslt 0_[w] t))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SLT, {s, t}),
                             d_nm.mk_node(Kind::BV_SLT, {zero, t})});
      }

    case Kind::BV_SLE:
      // x >>
      // IC: (bvsge t (bvnot (bvlshr max_signed_[w] s)))
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {t,
             d_nm.mk_node(Kind::BV_NOT,
                          {d_nm.mk_node(Kind::BV_SHR, {maxs, s})})});
      }
      // s >>a x <=_s t
      // IC: (or (bvsge t 0_[w]) (bvsge t s))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::BV_SGE, {t, zero}),
                             d_nm.mk_node(Kind::BV_SGE, {t, s})});
      }

    case Kind::BV_SGT: {
      Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
      // x >>a s >_s t
      // IC: (bvslt t (bvlshr max_signed_[w] s)))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::BV_SLT,
                            {t, d_nm.mk_node(Kind::BV_SHR, {maxs, s})});
      }
      // s >>a x >_s t
      // IC: (and
      //       (bvslt t (bvand s max_signed_[w]))
      //       (bvslt t (bvor s max_signed_[w])))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_SLT,
                        {t, d_nm.mk_node(Kind::BV_AND, {s, maxs})}),
           d_nm.mk_node(Kind::BV_SLT,
                        {t, d_nm.mk_node(Kind::BV_OR, {s, maxs})})});
    }

    case Kind::BV_SGE: {
      // x >>a s >=_s t
      // IC: (bvsge (bvlshr max_signed_[w] s) t)
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(Kind::BV_SGE,
                            {d_nm.mk_node(Kind::BV_SHR, {maxs, s}), t});
      }
      // s >>a x >=_s t
      // IC: (not (and (bvult t (bvnot t)) (bvslt s t)))
      return d_nm.mk_node(
          Kind::NOT,
          {d_nm.mk_node(
              Kind::AND,
              {d_nm.mk_node(Kind::BV_ULT, {t, d_nm.mk_node(Kind::BV_NOT, {t})}),
               d_nm.mk_node(Kind::BV_SLT, {s, t})})});
    }

    case Kind::DISTINCT: {
      // x >>a s != t
      // IC: true
      if (idx == 0)
      {
        return d_nm.mk_value(true);
      }
      // s >>a x != t
      // IC: (and
      //       (or (not (= t 0_[w])) (not (= s 0_[w])))
      //       (or (not (= t ~0_[w])) (not (= s ~0_[w]))))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {s, zero})}),
             d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {t, ones}),
                           d_nm.mk_node(Kind::DISTINCT, {s, ones})})});
      }
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x >>a s = t
      // IC: (and
      //       (=> (bvult s w_[w]) (= (bvashr (bvshl t s) s) t))
      //       (=> (bvuge s w_[w]) (or (= t ~0_[w]) (= t 0_[w])))
      //      )
      if (idx == 0)
      {
        Node w    = d_nm.mk_value(BitVector::from_ui(bw, bw));
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(
                 Kind::IMPLIES,
                 {
                     d_nm.mk_node(Kind::BV_ULT, {s, w}),
                     d_nm.mk_node(
                         Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_ASHR,
                                       {d_nm.mk_node(Kind::BV_SHL, {t, s}), s}),
                          t}),
                 }),
             d_nm.mk_node(
                 Kind::IMPLIES,
                 {d_nm.mk_node(Kind::BV_UGE, {s, w}),
                  d_nm.mk_node(Kind::OR,
                               {d_nm.mk_node(Kind::EQUAL, {t, ones}),
                                d_nm.mk_node(Kind::EQUAL, {t, zero})})})});
      }
      // s >>a x = t
      // IC: (or (= (bvashr s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_ASHR, s, t);
  }
}

Node
BvInverter::ic_bv_shl(Kind predicate,
                      const std::vector<Node>& nodes,
                      size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw   = s.type().bv_size();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x << s <_u t
      // s << x <_u t
      // IC: (not (= t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }

    case Kind::BV_ULE:
      // x << s <=_u t
      // s << x <=_u t
      // IC: true
      return d_nm.mk_value(true);

    case Kind::BV_UGT:
      // x << s >_u t
      // IC: (bvult t (bvshl ~0_[w] s))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_ULT,
                            {t, d_nm.mk_node(Kind::BV_SHL, {ones, s})});
      }
      // s << x >_u t
      // IC: (or (bvugt (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_UGT, Kind::BV_SHL, s, t);

    case Kind::BV_UGE:
      // x << s >=_u t
      // IC: (bvuge (bvshl ~0_[w] s) t)
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw));
        return d_nm.mk_node(Kind::BV_UGE,
                            {d_nm.mk_node(Kind::BV_SHL, {ones, s}), t});
      }
      // s << x >=_u t
      // IC: (or (bvuge (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_UGE, Kind::BV_SHL, s, t);

    case Kind::BV_SLT: {
      Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
      // x << s <_s t
      // IC: (bvslt (bvshl (bvlshr min_signed_[w] s) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_SLT,
            {d_nm.mk_node(Kind::BV_SHL,
                          {d_nm.mk_node(Kind::BV_SHR, {mins, s}), s}),
             t});
      }
      // s << x <_s t
      // IC: (bvult (bvshl min_signed_[w] s) (bvadd t min_signed_[w]))
      return d_nm.mk_node(Kind::BV_ULT,
                          {d_nm.mk_node(Kind::BV_SHL, {mins, s}),
                           d_nm.mk_node(Kind::BV_ADD, {t, mins})});
    }

    case Kind::BV_SLE: {
      Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw));
      // x << s <=_s t
      // IC: (bvult (bvlshr t (bvlshr t s)) min_signed_[w])
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_ULT,
            {d_nm.mk_node(Kind::BV_SHR,
                          {t, d_nm.mk_node(Kind::BV_SHR, {t, s})}),
             mins});
      }
      // s << x <=_s t
      // IC: (bvult (bvlshr t s) min_signed_[w])
      return d_nm.mk_node(Kind::BV_ULT,
                          {d_nm.mk_node(Kind::BV_SHR, {t, s}), mins});
    }

    case Kind::BV_SGT:
      // x << s >_s t
      // IC: (bvslt t (bvand (bvshl max_signed_[w] s) max_signed_[w]))
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SLT,
            {t,
             d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), maxs})});
      }
      // s << x >_s t
      // IC: (or (bvsgt (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_SGT, Kind::BV_SHL, s, t);

    case Kind::BV_SGE:
      // x << s >=_s t
      // IC: (bvsge (bvand (bvshl max_signed_[w] s) max_signed_[w]) t)
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {d_nm.mk_node(Kind::BV_AND,
                          {d_nm.mk_node(Kind::BV_SHL, {maxs, s}), maxs}),
             t});
      }
      // s << x >=_s t
      // IC: (or (bvsge (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::BV_SGE, Kind::BV_SHL, s, t);

    case Kind::DISTINCT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw));
      // x << s != t
      // IC: (or (distinct t 0_[w]) (bvult s w_[w]))
      if (idx == 0)
      {
        Node w = d_nm.mk_value(BitVector::from_ui(bw, bw));
        return d_nm.mk_node(Kind::OR,
                            {d_nm.mk_node(Kind::DISTINCT, {t, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, w})});
      }
      // s << x != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      return d_nm.mk_node(Kind::OR,
                          {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                           d_nm.mk_node(Kind::DISTINCT, {t, zero})});
    }

    default:
      assert(predicate == Kind::EQUAL);
      // x << s = t
      // IC: (= (bvshl (bvlshr t s) s) t)
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::EQUAL,
            {d_nm.mk_node(Kind::BV_SHL,
                          {d_nm.mk_node(Kind::BV_SHR, {t, s}), s}),
             t});
      }
      // s << x = t
      // IC: (or (= (bvshl s i) t) ...)
      //     for i in 0..w
      return _ic_shift_for_all_i(d_nm, Kind::EQUAL, Kind::BV_SHL, s, t);
  }
}

Node
BvInverter::ic_bv_concat(Kind predicate,
                         const std::vector<Node>& nodes,
                         size_t idx)
{
  assert(nodes.size() == 3);
  const Node& x = nodes[idx];
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  uint64_t bw_x = x.type().bv_size();
  uint64_t bw_s = s.type().bv_size();
  uint64_t bw_t = t.type().bv_size();
  Node t_x, t_s;
  if (idx == 0)
  {
    // t_x = t[bw(t) - 1: bw(t) - bw(x)]
    // t_s = t[bw(s) - 1: 0]
    t_x = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_t - 1, bw_t - bw_x});
    t_s = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_s - 1, 0});
  }
  else
  {
    // t_x = t[bw(x) - 1: 0]
    // t_s = t[bw(t) - 1: bw(t) - bw(s)]
    t_x = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_x - 1, 0});
    t_s = d_nm.mk_node(Kind::BV_EXTRACT, {t}, {bw_t - 1, bw_t - bw_s});
  }

  switch (predicate)
  {
    case Kind::BV_ULT: {
      Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
      // x :: s <_u t
      // IC: (=> (= t_x 0_[bw(x)]) (bvult s t_s))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, zero}),
                             d_nm.mk_node(Kind::BV_ULT, {s, t_s})});
      }
      // s :: x <_u t
      // IC: (and
      //       (bvule s t_s)
      //       (=> (= s t_s) (distinct t_x 0_[bw(x)]))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_ULE, {s, t_s}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                         d_nm.mk_node(Kind::DISTINCT, {t_x, zero})})});
    }

    case Kind::BV_ULE:
      // x :: s <=_u t
      // IC: (=> (= t_x 0_[bw(x)]) (bvule s t_s))
      if (idx == 0)
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, zero}),
                             d_nm.mk_node(Kind::BV_ULE, {s, t_s})});
      }
      // s :: x <=_u t
      // IC: (bvule s t_s)
      return d_nm.mk_node(Kind::BV_ULE, {s, t_s});

    case Kind::BV_UGT: {
      Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
      // x :: s >_u t
      // IC: (=> (= t_x ~0_[bw(x)]) (bvugt s t_s))
      if (idx == 0)
      {
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, ones}),
                             d_nm.mk_node(Kind::BV_UGT, {s, t_s})});
      }
      // s :: x >_u t
      // IC: (and (bvuge s t_s) (=> (= s t_s) (distinct t_x ~0_[bw(x)])))
      return d_nm.mk_node(
          Kind::AND,
          {d_nm.mk_node(Kind::BV_UGE, {s, t_s}),
           d_nm.mk_node(Kind::IMPLIES,
                        {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                         d_nm.mk_node(Kind::DISTINCT, {t_x, ones})})});
    }

    case Kind::BV_UGE:
      // x :: s >=_u t
      // IC: (=> (= t_x ~0_[bw(x)]) (bvuge s t_s))
      if (idx == 0)
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, ones}),
                             d_nm.mk_node(Kind::BV_UGE, {s, t_s})});
      }
      // s :: x >=_u t
      // IC: (bvuge s t_s)
      return d_nm.mk_node(Kind::BV_UGE, {s, t_s});

    case Kind::BV_SLT:
      // x :: s <_s t
      // IC: (=> (= t_x min_signed_[bw(x)]) (bvult s t_s))
      if (idx == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, mins}),
                             d_nm.mk_node(Kind::BV_ULT, {s, t_s})});
      }
      // s :: x <_s t
      // IC: (and (bvsle s t_s) (=> (= s t_s) (distinct t_x 0_[bw(x)])))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_x));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::BV_SLE, {s, t_s}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                           d_nm.mk_node(Kind::DISTINCT, {t_x, zero})})});
      }

    case Kind::BV_SLE:
      // x :: s <=_s t
      // IC: (=> (= t_x min_signed_[bw(x)]) (bvule s t_s))
      if (idx == 0)
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, mins}),
                             d_nm.mk_node(Kind::BV_ULE, {s, t_s})});
      }
      // s :: x <=_s t
      // IC: (bvsle s t_s)
      return d_nm.mk_node(Kind::BV_SLE, {s, t_s});

    case Kind::BV_SGT:
      // x :: s >_s t
      // IC: (=> (= t_x max_signed_[bw(x)]) (bvugt s t_s))
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, maxs}),
                             d_nm.mk_node(Kind::BV_UGT, {s, t_s})});
      }
      // s :: x >_s t
      // IC: (and (bvsge s t_s) (=> (= s t_s) (distinct t_x ~0_[bw(x)])))
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_x));
        return d_nm.mk_node(
            Kind::AND,
            {d_nm.mk_node(Kind::BV_SGE, {s, t_s}),
             d_nm.mk_node(Kind::IMPLIES,
                          {d_nm.mk_node(Kind::EQUAL, {s, t_s}),
                           d_nm.mk_node(Kind::DISTINCT, {t_x, ones})})});
      }

    case Kind::BV_SGE:
      // x :: s >=_s t
      // IC: (=> (= t_x max_signed_[bw(x)]) (bvuge s t_s))
      if (idx == 0)
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(Kind::IMPLIES,
                            {d_nm.mk_node(Kind::EQUAL, {t_x, maxs}),
                             d_nm.mk_node(Kind::BV_UGE, {s, t_s})});
      }
      // s :: x >=_s t
      // IC: (bvuge s t_s)
      return d_nm.mk_node(Kind::BV_SGE, {s, t_s});

    case Kind::DISTINCT:
      // x :: s != t
      // s :: x != t
      // IC: true
      return d_nm.mk_value(true);

    default:
      assert(predicate == Kind::EQUAL);
      // x :: s = t
      // s :: x = t
      // IC: (= s t_s)
      return d_nm.mk_node(Kind::EQUAL, {s, t_s});
  }
}

Node
BvInverter::ic_bv_sext(Kind predicate,
                       const std::vector<Node>& nodes,
                       size_t idx)
{
  assert(nodes.size() == 2);
  const Node& x = nodes[idx];
  const Node& t = nodes[1 - idx];
  uint64_t bw_t = t.type().bv_size();
  uint64_t bw_x = x.type().bv_size();
  uint64_t n    = bw_t - bw_x;
  switch (predicate)
  {
    case Kind::BV_ULT:
    case Kind::BV_UGT:
      // x<n> <_u t
      // t >_u x<n>
      // IC: (distinct t 0_[w])
      if ((predicate == Kind::BV_ULT && idx == 0)
          || (predicate == Kind::BV_UGT && idx == 1))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(bw_t));
        return d_nm.mk_node(Kind::DISTINCT, {t, zero});
      }
      // x<n> >_u t
      // t <_u x<n>
      // IC: (distinct t ~0_[w])
      {
        Node ones = d_nm.mk_value(BitVector::mk_ones(bw_t));
        return d_nm.mk_node(Kind::DISTINCT, {t, ones});
      }

    case Kind::BV_SGT:
    case Kind::BV_SLT:
      // x<n> <_s t
      // t    >_s x<n>
      // IC: (bvslt ((_ sign_extend n) min_signed_[bw(x)]) t)
      if ((predicate == Kind::BV_SLT && idx == 0)
          || (predicate == Kind::BV_SGT && idx == 1))
      {
        Node mins = d_nm.mk_value(BitVector::mk_min_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SLT, {d_nm.mk_node(Kind::BV_SIGN_EXTEND, {mins}, {n}), t});
      }
      // x<n> >_s t
      // t    <_s x<n>
      // IC: (bvslt t ((_ zero_extend n) max_signed_[bw(x)]))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SLT, {t, d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})});
      }

    case Kind::BV_SLE:
    case Kind::BV_SGE:
      // x<n> <=_s t
      // t    <=_s x<n>
      // IC: (bvsge t (bvnot ((_ zero_extend n) max_signed_[bw(x)])))
      if ((predicate == Kind::BV_SLE && idx == 0)
          || (predicate == Kind::BV_SGE && idx == 1))
      {
        Node maxs = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        return d_nm.mk_node(
            Kind::BV_SGE,
            {t,
             d_nm.mk_node(Kind::BV_NOT,
                          {d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})})});
      }
      // x<n> >=_s t
      // t    <=_s x<n>
      // IC: (or
      //       (or (= ((_ extract u l) t) 0_[n + 1])
      //           (= ((_ extract u l) t) ~0_[n + 1]))
      //       (bvslt t ((_ zero_extend n) max_signed_[bw(x)])))
      //       with u = w - 1
      //            l = w - 1 - n
      {
        Node maxs  = d_nm.mk_value(BitVector::mk_max_signed(bw_x));
        Node zero  = d_nm.mk_value(BitVector::mk_zero(n + 1));
        Node ones  = d_nm.mk_value(BitVector::mk_ones(n + 1));
        uint64_t u = bw_t - 1;
        uint64_t l = bw_t - 1 - n;
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(
                 Kind::OR,
                 {d_nm.mk_node(
                      Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), zero}),
                  d_nm.mk_node(
                      Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), ones})}),
             d_nm.mk_node(
                 Kind::BV_SLT,
                 {t, d_nm.mk_node(Kind::BV_ZERO_EXTEND, {maxs}, {n})})});
      }

    case Kind::BV_ULE:
      // x<n> <=_u t
      // IC: true
    case Kind::BV_UGE:
      // x<n> >=_u t
      // IC: true
    case Kind::DISTINCT:
      // x<n> != t
      return d_nm.mk_value(true);

    default:
      assert(predicate == Kind::EQUAL);
      // x<n> = t
      // IC: (or
      //       (= ((_ extract u l) t) 0_[n + 1])
      //       (= ((_ extract u l) t) ~0_[n + 1]))
      //       with u = w - 1
      //            l = w - 1 - n
      {
        Node zero  = d_nm.mk_value(BitVector::mk_zero(n + 1));
        Node ones  = d_nm.mk_value(BitVector::mk_ones(n + 1));
        uint64_t u = bw_t - 1;
        uint64_t l = bw_t - 1 - n;
        return d_nm.mk_node(
            Kind::OR,
            {d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), zero}),
             d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {u, l}), ones

                          })});
      }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::bv
