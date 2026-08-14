/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/abstract/abstraction_lemmas.h"

#include "node/node_manager.h"

namespace bzla::abstract {

using namespace node;

LemmaKind
lemma_kind_value(node::Kind k)
{
  if (k == Kind::BV_ADD)
  {
    return LemmaKind::ADD_VALUE;
  }
  else if (k == Kind::BV_MUL)
  {
    return LemmaKind::MUL_VALUE;
  }
  else if (k == Kind::BV_UDIV)
  {
    return LemmaKind::UDIV_VALUE;
  }
  else
  {
    assert(k == Kind::BV_UREM);
    return LemmaKind::UREM_VALUE;
  }
}

bool
is_lemma_kind_value(LemmaKind k)
{
  return k == LemmaKind::ADD_VALUE || k == LemmaKind::MUL_VALUE
         || k == LemmaKind::UDIV_VALUE || k == LemmaKind::UREM_VALUE;
}

std::ostream&
operator<<(std::ostream& os, LemmaKind kind)
{
  switch (kind)
  {
    case LemmaKind::MUL3_IC: os << "MUL3_IC"; break;
    case LemmaKind::MUL4_ODD: os << "MUL4_ODD"; break;
    case LemmaKind::MUL1_POW2: os << "MUL1_POW2"; break;
    case LemmaKind::MUL2_NEG_POW2: os << "MUL2_NEG_POW2"; break;
    case LemmaKind::MUL5: os << "MUL5"; break;
    case LemmaKind::MUL6: os << "MUL6"; break;
    case LemmaKind::MUL7: os << "MUL7"; break;
    case LemmaKind::MUL8: os << "MUL8"; break;
    case LemmaKind::MUL9: os << "MUL9"; break;
    case LemmaKind::MUL10: os << "MUL10"; break;
    case LemmaKind::MUL11: os << "MUL11"; break;
    case LemmaKind::MUL12: os << "MUL12"; break;
    case LemmaKind::MUL13: os << "MUL13"; break;
    case LemmaKind::MUL14: os << "MUL14"; break;
    case LemmaKind::MUL15: os << "MUL15"; break;
    case LemmaKind::MUL16: os << "MUL16"; break;
    case LemmaKind::MUL17: os << "MUL17"; break;
    case LemmaKind::MUL18: os << "MUL18"; break;
    case LemmaKind::MUL19: os << "MUL19"; break;
    case LemmaKind::MUL_VALUE: os << "MUL_VALUE"; break;

    case LemmaKind::UDIV1_POW2: os << "UDIV1_POW2"; break;
    case LemmaKind::UDIV2: os << "UDIV2"; break;
    case LemmaKind::UDIV3: os << "UDIV3"; break;
    case LemmaKind::UDIV4: os << "UDIV4"; break;
    case LemmaKind::UDIV5: os << "UDIV5"; break;
    case LemmaKind::UDIV6: os << "UDIV6"; break;
    case LemmaKind::UDIV7: os << "UDIV7"; break;
    case LemmaKind::UDIV8: os << "UDIV8"; break;
    case LemmaKind::UDIV9: os << "UDIV9"; break;
    case LemmaKind::UDIV10: os << "UDIV10"; break;
    case LemmaKind::UDIV11: os << "UDIV11"; break;
    case LemmaKind::UDIV12: os << "UDIV12"; break;
    case LemmaKind::UDIV13: os << "UDIV13"; break;
    case LemmaKind::UDIV14: os << "UDIV14"; break;
    case LemmaKind::UDIV15: os << "UDIV15"; break;
    case LemmaKind::UDIV16: os << "UDIV16"; break;
    case LemmaKind::UDIV17: os << "UDIV17"; break;
    case LemmaKind::UDIV18: os << "UDIV18"; break;
    case LemmaKind::UDIV19: os << "UDIV19"; break;
    case LemmaKind::UDIV20: os << "UDIV20"; break;
    case LemmaKind::UDIV21: os << "UDIV21"; break;
    case LemmaKind::UDIV22: os << "UDIV22"; break;
    case LemmaKind::UDIV23: os << "UDIV23"; break;
    case LemmaKind::UDIV24: os << "UDIV24"; break;
    case LemmaKind::UDIV25: os << "UDIV25"; break;
    case LemmaKind::UDIV26: os << "UDIV26"; break;
    case LemmaKind::UDIV27: os << "UDIV27"; break;
    case LemmaKind::UDIV28: os << "UDIV28"; break;
    case LemmaKind::UDIV29: os << "UDIV29"; break;
    case LemmaKind::UDIV30: os << "UDIV30"; break;
    case LemmaKind::UDIV31: os << "UDIV31"; break;
    case LemmaKind::UDIV32: os << "UDIV32"; break;
    case LemmaKind::UDIV33: os << "UDIV33"; break;
    case LemmaKind::UDIV34: os << "UDIV34"; break;
    case LemmaKind::UDIV35: os << "UDIV35"; break;
    case LemmaKind::UDIV36: os << "UDIV36"; break;
    case LemmaKind::UDIV37: os << "UDIV37"; break;
    case LemmaKind::UDIV_VALUE: os << "UDIV_VALUE"; break;

    case LemmaKind::UREM1_POW2: os << "UREM1_POW2"; break;
    case LemmaKind::UREM2: os << "UREM2"; break;
    case LemmaKind::UREM3: os << "UREM3"; break;
    case LemmaKind::UREM4: os << "UREM4"; break;
    case LemmaKind::UREM5: os << "UREM5"; break;
    case LemmaKind::UREM6: os << "UREM6"; break;
    case LemmaKind::UREM7: os << "UREM7"; break;
    case LemmaKind::UREM8: os << "UREM8"; break;
    case LemmaKind::UREM9: os << "UREM9"; break;
    case LemmaKind::UREM10: os << "UREM10"; break;
    case LemmaKind::UREM11: os << "UREM11"; break;
    case LemmaKind::UREM12: os << "UREM12"; break;
    case LemmaKind::UREM13: os << "UREM13"; break;
    case LemmaKind::UREM14: os << "UREM14"; break;
    case LemmaKind::UREM15: os << "UREM15"; break;
    case LemmaKind::UREM_VALUE: os << "UREM_VALUE"; break;

    case LemmaKind::ADD_ZERO: os << "ADD_ZERO"; break;
    case LemmaKind::ADD_SAME: os << "ADD_SAME"; break;
    case LemmaKind::ADD_INV: os << "ADD_INV"; break;
    case LemmaKind::ADD_OVFL: os << "ADD_OVFL"; break;
    case LemmaKind::ADD_NOOVFL: os << "ADD_NOOVFL"; break;
    case LemmaKind::ADD_OR: os << "ADD_OR"; break;
    case LemmaKind::ADD_REF6: os << "ADD_REF6"; break;
    case LemmaKind::ADD_REF7: os << "ADD_REF7"; break;
    case LemmaKind::ADD_REF8: os << "ADD_REF8"; break;
    case LemmaKind::ADD_REF9: os << "ADD_REF9"; break;
    case LemmaKind::ADD_REF10: os << "ADD_REF10"; break;
    case LemmaKind::ADD_REF11: os << "ADD_REF11"; break;
    case LemmaKind::ADD_REF12: os << "ADD_REF12"; break;
    case LemmaKind::ADD_VALUE: os << "ADD_VALUE"; break;

    case LemmaKind::BITBLAST_FULL: os << "BITBLAST_FULL"; break;
    case LemmaKind::BITBLAST_INC: os << "BITBLAST_INC"; break;
    case LemmaKind::BITBLAST_BV_MUL: os << "BITBLAST_BV_MUL"; break;
    case LemmaKind::BITBLAST_BV_MUL_SQUARE: os << "BITBLAST_BV_MUL_SQUARE"; break;
    case LemmaKind::BITBLAST_BV_UDIV: os << "BITBLAST_BV_UDIV"; break;
    case LemmaKind::BITBLAST_BV_UREM: os << "BITBLAST_BV_UREM"; break;
    case LemmaKind::ITE_EXPAND: os << "ITE_EXPAND"; break;
    case LemmaKind::ITE_REFINE: os << "ITE_REFINE"; break;
    case LemmaKind::ASSERTION: os << "ASSERTION"; break;
  }
  return os;
}

/* --- Abstraction Lemmas --------------------------------------------------- */

template <>
Node
Lemma<LemmaKind::MUL3_IC>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  (void) x;
  Node lhs = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_node(Kind::BV_OR, {d_nm.mk_node(Kind::BV_NEG, {s}), s}), t});
  return d_nm.mk_node(Kind::EQUAL, {lhs, t});
}

template <>
Node
Lemma<LemmaKind::MUL4_ODD>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  return d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {0, 0}),
       d_nm.mk_node(Kind::BV_AND,
                    {
                        d_nm.mk_node(Kind::BV_EXTRACT, {x}, {0, 0}),
                        d_nm.mk_node(Kind::BV_EXTRACT, {s}, {0, 0}),
                    })});
}

template <>
Node
Lemma<LemmaKind::MUL1_POW2>::instance(const Node& val_x,
                                      const Node& val_s,
                                      const Node& val_t,
                                      const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  (void) val_s;
  (void) val_t;
  if (val_x.is_value() && val_x.value<BitVector>().is_power_of_two())
  {
    const auto& val_pow2 = val_x.value<BitVector>();
    Node shift_by        = d_nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = d_nm.mk_node(Kind::EQUAL, {x, val_x});
    return d_nm.mk_node(
        Kind::IMPLIES,
        {eq,
         d_nm.mk_node(Kind::EQUAL,
                      {t, d_nm.mk_node(Kind::BV_SHL, {s, shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::MUL2_NEG_POW2>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_s;
  (void) val_t;
  BitVector val_pow2;
  if (val_x.is_value() && !val_x.value<BitVector>().is_min_signed()
      && (val_pow2 = val_x.value<BitVector>().bvneg()).is_power_of_two())
  {
    Node shift_by = d_nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = d_nm.mk_node(Kind::EQUAL, {x, val_x});
    return d_nm.mk_node(
        Kind::IMPLIES,
        {eq,
         d_nm.mk_node(
             Kind::EQUAL,
             {t,
              d_nm.mk_node(Kind::BV_SHL,
                           {d_nm.mk_node(Kind::BV_NEG, {s}), shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::MUL5>::instance(const Node& x,
                                 const Node& s,
                                 const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::NOT,
      {d_nm.mk_node(
          Kind::EQUAL,
          {s,
           d_nm.mk_node(
               Kind::BV_NOT,
               {d_nm.mk_node(
                   Kind::BV_OR,
                   {t,
                    d_nm.mk_node(
                        Kind::BV_AND,
                        {one, d_nm.mk_node(Kind::BV_OR, {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL6>::instance(const Node& x,
                                 const Node& s,
                                 const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_node(Kind::BV_AND, {x, t}),
       d_nm.mk_node(Kind::BV_OR, {s, d_nm.mk_node(Kind::BV_NOT, {t})})});
}

template <>
Node
Lemma<LemmaKind::MUL7>::instance(const Node& x,
                                 const Node& s,
                                 const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  // (not (= t (bvshl (bvor s #b0001) (bvshl t x))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::DISTINCT,
                      {t,
                       d_nm.mk_node(Kind::BV_SHL,
                                    {d_nm.mk_node(Kind::BV_OR, {s, one}),
                                     d_nm.mk_node(Kind::BV_SHL, {t, x})})});
}

template <>
Node
Lemma<LemmaKind::MUL8>::instance(const Node& x,
                                 const Node& s,
                                 const Node& t) const
{
  // (= s (bvshl s (bvand x (bvlshr #b0001 t))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::EQUAL,
      {s,
       d_nm.mk_node(
           Kind::BV_SHL,
           {s,
            d_nm.mk_node(Kind::BV_AND,
                         {x, d_nm.mk_node(Kind::BV_SHR, {one, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL9>::instance(const Node& x,
                                 const Node& s,
                                 const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() != 2);
  // (bvuge t (bvand #b0001 (bvlshr (bvand x s) #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {t,
       d_nm.mk_node(
           Kind::BV_AND,
           {one,
            d_nm.mk_node(Kind::BV_SHR,
                         {d_nm.mk_node(Kind::BV_AND, {x, s}), one})})});
}

template <>
Node
Lemma<LemmaKind::MUL10>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= x (bvxor #b0001 (bvshl x (bvxor s t)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_XOR,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {x, d_nm.mk_node(Kind::BV_XOR, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL13>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= x (bvsub (bvshl x (bvadd s t)) #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(
           Kind::BV_SUB,
           {d_nm.mk_node(Kind::BV_SHL, {x, d_nm.mk_node(Kind::BV_ADD, {s, t})}),
            one})});
}

template <>
Node
Lemma<LemmaKind::MUL15>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= s (bvadd #b0001 (bvshl s (bvsub t x)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {s,
       d_nm.mk_node(Kind::BV_ADD,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {s, d_nm.mk_node(Kind::BV_SUB, {t, x})})})});
}

template <>
Node
Lemma<LemmaKind::MUL16>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= s (bvsub #b0001 (bvshl s (bvsub t x)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {s,
       d_nm.mk_node(Kind::BV_SUB,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {s, d_nm.mk_node(Kind::BV_SUB, {t, x})})})});
}

template <>
Node
Lemma<LemmaKind::MUL17>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= s (bvadd #b0001 (bvshl s (bvsub x t)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {s,
       d_nm.mk_node(Kind::BV_ADD,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {s, d_nm.mk_node(Kind::BV_SUB, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL19>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_NOT,
                    {d_nm.mk_node(Kind::BV_SHL,
                                  {x, d_nm.mk_node(Kind::BV_ADD, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL18>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t,
       d_nm.mk_node(Kind::BV_OR, {one, d_nm.mk_node(Kind::BV_ADD, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::MUL11>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t,
       d_nm.mk_node(Kind::BV_OR,
                    {one,
                     d_nm.mk_node(Kind::BV_NOT,
                                  {d_nm.mk_node(Kind::BV_XOR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL12>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::DISTINCT,
                      {t,
                       d_nm.mk_node(Kind::BV_OR,
                                    {d_nm.mk_node(Kind::BV_NOT, {one}),
                                     d_nm.mk_node(Kind::BV_XOR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::MUL14>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_SUB,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {x, d_nm.mk_node(Kind::BV_SUB, {s, t})})})});
}

// Unsigned division lemmas

template <>
Node
Lemma<LemmaKind::UDIV1_POW2>::instance(const Node& val_x,
                                       const Node& val_s,
                                       const Node& val_t,
                                       const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) val_x;
  (void) val_t;
  if (val_s.is_value() && val_s.value<BitVector>().is_power_of_two())
  {
    const auto& val_pow2 = val_s.value<BitVector>();
    Node shift_by        = d_nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = d_nm.mk_node(Kind::EQUAL, {s, val_s});
    return d_nm.mk_node(
        Kind::IMPLIES,
        {eq,
         d_nm.mk_node(Kind::EQUAL,
                      {t, d_nm.mk_node(Kind::BV_SHR, {x, shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::UDIV37>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (=> (= s #b0001) (= t x))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::EQUAL, {s, one}), d_nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UDIV2>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (and (= s x) (distinct s #b0000)) (= t #b0001))
  Node one  = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));

  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::AND,
                                    {d_nm.mk_node(Kind::EQUAL, {s, x}),
                                     d_nm.mk_node(Kind::DISTINCT, {s, zero})}),
                       d_nm.mk_node(Kind::EQUAL, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UDIV3>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (= s #b0000) (= t (bvnot #b0000)))
  Node ones = d_nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::EQUAL, {s, zero}),
                       d_nm.mk_node(Kind::EQUAL, {t, ones})}

  );
}

template <>
Node
Lemma<LemmaKind::UDIV4>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (and (= x #b0000) (distinct s #b0000)) (= t #b0000))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::AND,
                                    {d_nm.mk_node(Kind::EQUAL, {x, zero}),
                                     d_nm.mk_node(Kind::DISTINCT, {s, zero})}),
                       d_nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UDIV5>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (distinct s #b0000) (bvule t x))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                       d_nm.mk_node(Kind::BV_ULE, {t, x})}

  );
}

template <>
Node
Lemma<LemmaKind::UDIV6>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (let ((_let_1 (bvnot #b0000)))
  //  (=> (and (= s _let_1) (distinct x _let_1)) (= t #b0000)))
  Node ones = d_nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));

  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::AND,
                                    {d_nm.mk_node(Kind::EQUAL, {s, ones}),
                                     d_nm.mk_node(Kind::DISTINCT, {x, ones})}),
                       d_nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UDIV7>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {
                                      d_nm.mk_node(Kind::BV_NEG, {s}),
                                      d_nm.mk_node(Kind::BV_NEG, {t}),
                                  })})});
}

template <>
Node
Lemma<LemmaKind::UDIV8>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (bvult (bvneg (bvor s #b0001)) t))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_NEG, {d_nm.mk_node(Kind::BV_OR, {s, one})}), t

      });
}

template <>
Node
Lemma<LemmaKind::UDIV9>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (= t (bvneg (bvand s (bvnot x)))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(Kind::BV_AND,
                                  {s, d_nm.mk_node(Kind::BV_NOT, {x})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV10>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= (bvor s t) (bvand x (bvnot #b0001))))
  Node m = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()).ibvnot());
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_node(Kind::BV_OR, {s, t}), d_nm.mk_node(Kind::BV_AND, {x, m})

      });
}

template <>
Node
Lemma<LemmaKind::UDIV11>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= (bvor s #b0001) (bvand x (bvnot t))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_node(Kind::BV_OR, {s, one}),
       d_nm.mk_node(Kind::BV_AND, {x, d_nm.mk_node(Kind::BV_NOT, {t})})});
}

template <>
Node
Lemma<LemmaKind::UDIV12>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvand x (bvneg t)) (bvand s t)))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_AND, {x, d_nm.mk_node(Kind::BV_NEG, {t})}),
       d_nm.mk_node(Kind::BV_AND, {s, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV13>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult s (bvlshr x t)))
  return d_nm.mk_node(Kind::BV_UGE, {s, d_nm.mk_node(Kind::BV_SHR, {x, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV14>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvshl (bvlshr s (bvshl s t)) #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(
           Kind::BV_SHL,
           {d_nm.mk_node(Kind::BV_SHR, {s, d_nm.mk_node(Kind::BV_SHL, {s, t})}),
            one})});
}

template <>
Node
Lemma<LemmaKind::UDIV15>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvlshr (bvshl t #b0001) (bvshl t s))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::BV_UGE,
                      {x,
                       d_nm.mk_node(Kind::BV_SHR,
                                    {d_nm.mk_node(Kind::BV_SHL, {t, one}),
                                     d_nm.mk_node(Kind::BV_SHL, {t, s})})});
}

template <>
Node
Lemma<LemmaKind::UDIV16>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult t (bvshl (bvlshr x s) #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {t,
       d_nm.mk_node(Kind::BV_SHL, {d_nm.mk_node(Kind::BV_SHR, {x, s}), one})});
}

template <>
Node
Lemma<LemmaKind::UDIV17>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvand (bvor x t) (bvshl s #b0001))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::BV_UGE,
                      {x,
                       d_nm.mk_node(Kind::BV_AND,
                                    {d_nm.mk_node(Kind::BV_OR, {x, t}),
                                     d_nm.mk_node(Kind::BV_SHL, {s, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV18>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvand (bvor x s) (bvshl t #b0001))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::BV_UGE,
                      {x,
                       d_nm.mk_node(Kind::BV_AND,
                                    {d_nm.mk_node(Kind::BV_OR, {x, s}),
                                     d_nm.mk_node(Kind::BV_SHL, {t, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV19>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= (bvlshr x t) (bvor s t)))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_node(Kind::BV_SHR, {x, t}), d_nm.mk_node(Kind::BV_OR, {s, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV20>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= s (bvnot (bvlshr s (bvlshr t #b0001)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {s,
       d_nm.mk_node(
           Kind::BV_NOT,
           {d_nm.mk_node(Kind::BV_SHR,
                         {s, d_nm.mk_node(Kind::BV_SHR, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV21>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  (void) s;
  // (not (= x (bvnot (bvand x (bvshl t #b0001)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(
           Kind::BV_NOT,
           {d_nm.mk_node(Kind::BV_AND,
                         {x, d_nm.mk_node(Kind::BV_SHL, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV22>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult t (bvlshr (bvshl x #b0001) s)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {t,
       d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_node(Kind::BV_SHL, {x, one}), s})});
}

template <>
Node
Lemma<LemmaKind::UDIV23>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvshl s (bvnot (bvor x t)))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(
           Kind::BV_SHL,
           {s,
            d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_OR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV24>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvshl t (bvnot (bvor x s)))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(
           Kind::BV_SHL,
           {t,
            d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV25>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvxor t (bvlshr t (bvlshr s #b0001)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(
           Kind::BV_XOR,
           {t,
            d_nm.mk_node(Kind::BV_SHR,
                         {t, d_nm.mk_node(Kind::BV_SHR, {s, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV26>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvxor s (bvlshr s (bvlshr t #b0001)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(
           Kind::BV_XOR,
           {s,
            d_nm.mk_node(Kind::BV_SHR,
                         {s, d_nm.mk_node(Kind::BV_SHR, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV27>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvshl s (bvnot (bvxor x t)))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(Kind::BV_SHL,
                    {s,
                     d_nm.mk_node(Kind::BV_NOT,
                                  {d_nm.mk_node(Kind::BV_XOR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV28>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult x (bvshl t (bvnot (bvxor x s)))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x,
       d_nm.mk_node(Kind::BV_SHL,
                    {t,
                     d_nm.mk_node(Kind::BV_NOT,
                                  {d_nm.mk_node(Kind::BV_XOR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV29>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= x (bvadd t (bvor s (bvadd x s)))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_ADD,
                    {t,
                     d_nm.mk_node(Kind::BV_OR,
                                  {s, d_nm.mk_node(Kind::BV_ADD, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV30>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 2);
  (void) s;
  // (not (= x (bvadd t (bvadd #b0001 (bvshl #b0001 x)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(
           Kind::BV_ADD,
           {t,
            d_nm.mk_node(Kind::BV_ADD,
                         {one, d_nm.mk_node(Kind::BV_SHL, {one, x})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV31>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult s (bvlshr (bvadd x t) t)))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {s, d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_node(Kind::BV_ADD, {x, t}), t})});
}

template <>
Node
Lemma<LemmaKind::UDIV32>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 1);
  // (not (= x (bvadd t (bvadd t (bvor x s)))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_ADD,
                    {t,
                     d_nm.mk_node(Kind::BV_ADD,
                                  {t, d_nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV33>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvxor s (bvor x t)) (bvxor t #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_XOR, {s, d_nm.mk_node(Kind::BV_OR, {x, t})}),
       d_nm.mk_node(Kind::BV_XOR, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UDIV34>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult t (bvlshr x (bvsub s #b0001))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {t,
       d_nm.mk_node(Kind::BV_SHR, {x, d_nm.mk_node(Kind::BV_SUB, {s, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV35>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvsub s #b0001) (bvlshr x t)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(Kind::BV_UGE,
                      {d_nm.mk_node(Kind::BV_SUB, {s, one}),
                       d_nm.mk_node(Kind::BV_SHR, {x, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV36>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() != 2);
  (void) s;
  // (not (= x (bvsub #b0001 (bvshl x (bvsub x t)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(Kind::BV_SUB,
                    {one,
                     d_nm.mk_node(Kind::BV_SHL,
                                  {x, d_nm.mk_node(Kind::BV_SUB, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UREM1_POW2>::instance(const Node& val_x,
                                       const Node& val_s,
                                       const Node& val_t,
                                       const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) val_x;
  (void) val_t;
  if (val_s.is_value() && val_s.value<BitVector>().is_power_of_two())
  {
    const auto& val_pow2 = val_s.value<BitVector>();
    uint64_t ctz         = val_pow2.count_trailing_zeros();
    Node shift_by = d_nm.mk_value(BitVector::from_ui(val_pow2.size(), ctz));
    Node eq       = d_nm.mk_node(Kind::EQUAL, {s, val_s});
    Node rem;
    if (ctz == 0)
    {
      rem = d_nm.mk_value(BitVector::mk_zero(val_pow2.size()));
    }
    else
    {
      rem = d_nm.mk_node(Kind::BV_ZERO_EXTEND,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {ctz - 1, 0})},
                         {val_pow2.size() - ctz});
    }
    return d_nm.mk_node(Kind::IMPLIES,
                        {eq, d_nm.mk_node(Kind::EQUAL, {t, rem})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::UREM2>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (distinct s #b0000) (bvult t s))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::DISTINCT, {s, zero}),
                       d_nm.mk_node(Kind::BV_ULT, {t, s})});
}

template <>
Node
Lemma<LemmaKind::UREM3>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  (void) s;
  // (=> (= x #b0000) (= t #b0000))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::EQUAL, {x, zero}),
                       d_nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UREM4>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (= s #b0000) (= t x))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::EQUAL, {s, zero}),
                       d_nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UREM5>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (= s x) (= t #b0000))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::EQUAL, {s, x}),
                       d_nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UREM6>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (=> (bvult x s) (= t x))
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::BV_ULT, {x, s}), d_nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UREM7>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  (void) x;
  // (bvuge (bvnot (bvneg s)) t)
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NEG, {s})}), t});
}

template <>
Node
Lemma<LemmaKind::UREM8>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (= x (bvand x (bvor s (bvor t (bvneg s)))))
  return d_nm.mk_node(
      Kind::EQUAL,
      {x,
       d_nm.mk_node(
           Kind::BV_AND,
           {x,
            d_nm.mk_node(
                Kind::BV_OR,
                {s,
                 d_nm.mk_node(Kind::BV_OR,
                              {t, d_nm.mk_node(Kind::BV_NEG, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::UREM9>::instance(const Node& x,
                                  const Node& s,
                                  const Node& t) const
{
  // (not (bvult x (bvor t (bvand x s))))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {x, d_nm.mk_node(Kind::BV_OR, {t, d_nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::UREM10>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= #b0001 (bvand t (bvnot (bvor x s)))))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::DISTINCT,
      {one,
       d_nm.mk_node(
           Kind::BV_AND,
           {t,
            d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UREM11>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (= t (bvor (bvnot x) (bvneg s))))
  return d_nm.mk_node(Kind::DISTINCT,
                      {t,
                       d_nm.mk_node(Kind::BV_OR,
                                    {d_nm.mk_node(Kind::BV_NOT, {x}),
                                     d_nm.mk_node(Kind::BV_NEG, {s})})});
}

template <>
Node
Lemma<LemmaKind::UREM12>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvand t (bvor x s)) (bvand t #b0001)))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_AND, {t, d_nm.mk_node(Kind::BV_OR, {x, s})}),
       d_nm.mk_node(Kind::BV_AND, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UREM13>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // Lemma is only valid with the asserted restriction. This is assertion is
  // mainly for documentation purposes since we globally restrict the minimum
  // abstraction size to 3 (via minimum value configuration of option
  // abstraction_bv_size).
  assert(x.type().bv_size() > 2);
  (void) s;
  // (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {x,
       d_nm.mk_node(
           Kind::BV_OR,
           {d_nm.mk_node(Kind::BV_NEG, {x}),
            d_nm.mk_node(Kind::BV_NEG, {d_nm.mk_node(Kind::BV_NOT, {t})})})});
}

template <>
Node
Lemma<LemmaKind::UREM14>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvadd x (bvneg s)) t))
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_ADD, {x, d_nm.mk_node(Kind::BV_NEG, {s})}), t});
}

template <>
Node
Lemma<LemmaKind::UREM15>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (not (bvult (bvxor (bvneg s) (bvor x s)) t))
  return d_nm.mk_node(Kind::BV_UGE,
                      {d_nm.mk_node(Kind::BV_XOR,
                                    {d_nm.mk_node(Kind::BV_NEG, {s}),
                                     d_nm.mk_node(Kind::BV_OR, {x, s})}),
                       t});
}

template <>
Node
Lemma<LemmaKind::ADD_ZERO>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= s #b000) (= t x))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(Kind::IMPLIES,
                      {d_nm.mk_node(Kind::EQUAL, {s, zero}),
                       d_nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::ADD_SAME>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= x s) (= ((_ extract 0 0) t) #b0))
  Node zero = d_nm.mk_value(BitVector::mk_zero(1));
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::EQUAL, {x, s}),
       d_nm.mk_node(Kind::EQUAL,
                    {d_nm.mk_node(Kind::BV_EXTRACT, {t}, {0, 0}), zero})});
}

template <>
Node
Lemma<LemmaKind::ADD_INV>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  // (=> (= s (bvnot x)) (= t #b1111))
  Node ones = d_nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::EQUAL, {s, d_nm.mk_node(Kind::BV_NOT, {x})}),
       d_nm.mk_node(Kind::EQUAL, {t, ones})});
}

template <>
Node
Lemma<LemmaKind::ADD_OVFL>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (and (= (msb x) #b1) (= (msb s) #b1)) (bvult t (bvand x s)))
  Node one        = d_nm.mk_value(BitVector::mk_one(1));
  uint64_t msb    = x.type().bv_size() - 1;
  Node msb_x      = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb});
  Node msb_s      = d_nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb});
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::AND,
                    {d_nm.mk_node(Kind::EQUAL, {msb_x, one}),
                     d_nm.mk_node(Kind::EQUAL, {msb_s, one})}),
       d_nm.mk_node(Kind::BV_ULT, {t, d_nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_NOOVFL>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (=> (and (= (msb x) #b0) (= (msb s) #b0)) (bvuge t (bvor x s)))
  Node zero       = d_nm.mk_value(BitVector::mk_zero(1));
  uint64_t msb    = x.type().bv_size() - 1;
  Node msb_x      = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb});
  Node msb_s      = d_nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb});
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::AND,
                    {d_nm.mk_node(Kind::EQUAL, {msb_x, zero}),
                     d_nm.mk_node(Kind::EQUAL, {msb_s, zero})}),
       d_nm.mk_node(Kind::BV_UGE, {t, d_nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_OR>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (=> (= (bvand x s) #b000) (= t (bvor x s)))
  Node zero = d_nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::IMPLIES,
      {d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {x, s}), zero}),
       d_nm.mk_node(Kind::EQUAL, {t, d_nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF6>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (= #b0000 (bvand x (bvand s (bvand t #b0001))))
  return d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(BitVector::mk_zero(x.type().bv_size())),
       d_nm.mk_node(
           Kind::BV_AND,
           {x,
            d_nm.mk_node(Kind::BV_AND,
                         {s,
                          d_nm.mk_node(Kind::BV_AND,
                                       {t,
                                        d_nm.mk_value(BitVector::mk_one(
                                            x.type().bv_size()))})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF7>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor s t)) (bvand x #b0001))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_AND, {one, d_nm.mk_node(Kind::BV_OR, {s, t})}),
       d_nm.mk_node(Kind::BV_AND, {x, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF8>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor x t)) (bvand s #b0001))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_AND, {one, d_nm.mk_node(Kind::BV_OR, {x, t})}),
       d_nm.mk_node(Kind::BV_AND, {s, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF9>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor x s)) (bvand t #b0001))
  Node one = d_nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return d_nm.mk_node(
      Kind::BV_UGE,
      {d_nm.mk_node(Kind::BV_AND, {one, d_nm.mk_node(Kind::BV_OR, {x, s})}),
       d_nm.mk_node(Kind::BV_AND, {t, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF10>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct #b0001 (bvor t (bvnot (bvand x s))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_value(BitVector::mk_one(x.type().bv_size())),
       d_nm.mk_node(Kind::BV_OR,
                    {t,
                     d_nm.mk_node(Kind::BV_NOT,
                                  {d_nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF11>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct t (bvnot (bvor t (bvand x s))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {t,
       d_nm.mk_node(Kind::BV_NOT,
                    {d_nm.mk_node(Kind::BV_OR,
                                  {t, d_nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF12>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct #b0001 (bvor x (bvor s (bvnot t))))
  return d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_value(BitVector::mk_one(x.type().bv_size())),
       d_nm.mk_node(
           Kind::BV_OR,
           {x,
            d_nm.mk_node(Kind::BV_OR, {s, d_nm.mk_node(Kind::BV_NOT, {t})})})});
}
}  // namespace bzla::abstract
