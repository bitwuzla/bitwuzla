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
BvInverter::ic(Kind predicate,
               Kind kind,
               const std::vector<Node>& nodes,
               size_t idx)
{
  assert(nodes.size() > 1);
  assert(idx < 2);
  switch (kind)
  {
    case Kind::BV_MUL: return ic_bv_mul(predicate, nodes, idx);
    case Kind::BV_UREM: return ic_bv_urem(predicate, nodes, idx);
    default: assert(false);
  }
  assert(nodes.size() == 2);
  switch (predicate)
  {
    case Kind::BV_SLT:
      // x <_s t
      // IC: (distinct t min_signed_[w])
      return d_nm.mk_node(Kind::DISTINCT,
                          {nodes[1 - idx],
                           d_nm.mk_value(BitVector::mk_min_signed(
                               nodes[idx].type().bv_size()))});

    case Kind::BV_SGT:
      // x >_s t
      // IC: (distinct t max_signed_[w])
      return d_nm.mk_node(Kind::DISTINCT,
                          {nodes[1 - idx],
                           d_nm.mk_value(BitVector::mk_max_signed(
                               nodes[idx].type().bv_size()))});

    case Kind::BV_ULT:
      // x <_u t
      // IC: (distinct t (_ bv0 w))
      return d_nm.mk_node(
          Kind::DISTINCT,
          {nodes[1 - idx],
           d_nm.mk_value(BitVector::mk_zero(nodes[idx].type().bv_size()))});

    case Kind::BV_UGT:
      // x >_u t
      // IC: (distinct t (bvnot (_ bv0 w)))
      return d_nm.mk_node(
          Kind::DISTINCT,
          {nodes[1 - idx],
           d_nm.mk_value(BitVector::mk_ones(nodes[idx].type().bv_size()))});

    case Kind::BV_UGE:
      // x >=_u t
    case Kind::BV_ULE:
      // x <=_u t
    case Kind::BV_SGE:
      // x >=_s t
    case Kind::BV_SLE:
      // x <=_s t
      // IC: true
      return d_nm.mk_value(true);

    default: assert(false);
  }
}

/* --- BvInverter private --------------------------------------------------- */

Node
BvInverter::ic_bv_mul(Kind predicate,
                      const std::vector<Node>& nodes,
                      size_t idx)
{
  assert(nodes.size() == 3);
  const Node& s = nodes[1 - idx];
  const Node& t = nodes.back();
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x * s <_u t
      // IC: (distinct t 0_[w])
      return d_nm.mk_node(
          Kind::DISTINCT,
          {t, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))});

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
      return d_nm.mk_node(
          Kind::NOT,
          {d_nm.mk_node(
              Kind::AND,
              {d_nm.mk_node(
                   Kind::EQUAL,
                   {s, d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()))}),
               d_nm.mk_node(Kind::BV_SLT, {t, s})})});

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
      // IC: (bvsge (bvand (bvor (bvneg s) s) max) t)
      return d_nm.mk_node(
          Kind::BV_SGE,
          {d_nm.mk_node(
               Kind::BV_AND,
               {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}),
                d_nm.mk_value(BitVector::mk_max_signed(s.type().bv_size()))}),
           t});

    case Kind::DISTINCT:
      // x * s != t
      // IC: (or (distinct s 0_[w]) (distinct t 0_[w]))
      {
        Node zero = d_nm.mk_value(BitVector::mk_zero(s.type().bv_size()));
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
          {d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_OR,
                                      {d_nm.mk_node(Kind::BV_NEG, {s}), s})}),
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
  Node zero     = d_nm.mk_value(BitVector::mk_zero(bw));
  Node one      = d_nm.mk_value(BitVector::mk_one(bw));
  Node ones     = d_nm.mk_value(BitVector::mk_one(bw));
  switch (predicate)
  {
    case Kind::BV_ULT:
      // x mod s <_u t
      // s mod x <_u t
      // IC: (distinct t 0_[w])
      return d_nm.mk_node(Kind::DISTINCT, {t, zero});

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
      return d_nm.mk_node(Kind::OR,
                          {
                              d_nm.mk_node(Kind::BV_SLT, {s, t}),
                              d_nm.mk_node(Kind::BV_SLT, {zero, t}),
                          });

    case Kind::BV_SLE:
      // x mod s <=_s t
      // IC: (bvslt ~0_[w] (bvand (bvneg s) t))
      if (idx == 0)
      {
        return d_nm.mk_node(
            Kind::BV_SLT,
            {ones,
             d_nm.mk_node(Kind::BV_AND, {d_nm.mk_node(Kind::BV_NEG, {s}), t})});
      }
      // s mod x <=_s t
      // IC: (or (bvult t min) (bvsge t s))
      return d_nm.mk_node(
          Kind::OR,
          {d_nm.mk_node(Kind::BV_ULT,
                        {t, d_nm.mk_value(BitVector::mk_min_signed(bw))}),
           d_nm.mk_node(Kind::BV_SGE, {t, s})});

    case Kind::BV_SGT:
      // x mod s >_s t
      // IC: (and
      //       (and
      //         (=> (bvsgt s 0_[w]) (bvslt t (bvnot (bvneg s))))
      //         (=> (bvsle s 0_[w]) (distinct t max_signed_[w])))
      //       (or (distinct t 0_[w]) (distinct s (_ bv1 w))))
      if (idx == 0)
      {
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
                     d_nm.mk_node(
                         Kind::IMPLIES,
                         {d_nm.mk_node(Kind::BV_SLE, {s, zero}),
                          d_nm.mk_node(
                              Kind::DISTINCT,
                              {t,
                               d_nm.mk_value(BitVector::mk_max_signed(bw))})}),
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

    case Kind::BV_SGE:
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

    case Kind::DISTINCT:
      // x mod s != t
      // IC: (or (distinct s (_ bv1 w)) (distinct t 0_[w]))
      if (idx == 0)
      {
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

/* -------------------------------------------------------------------------- */

}  // namespace bzla::bv
