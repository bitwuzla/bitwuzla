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
    case LemmaKind::MUL_ZERO: os << "MUL_ZERO"; break;
    case LemmaKind::MUL_ONE: os << "MUL_ONE"; break;
    case LemmaKind::MUL_IC: os << "MUL_IC"; break;
    case LemmaKind::MUL_NEG: os << "MUL_NEG"; break;
    case LemmaKind::MUL_ODD: os << "MUL_ODD"; break;
    case LemmaKind::MUL_POW2: os << "MUL_POW2"; break;
    case LemmaKind::MUL_NEG_POW2: os << "MUL_NEG_POW2"; break;
    case LemmaKind::MUL_REF1: os << "MUL_REF1"; break;
    case LemmaKind::MUL_REF2: os << "MUL_REF2"; break;
    case LemmaKind::MUL_REF3: os << "MUL_REF3"; break;
    case LemmaKind::MUL_REF4: os << "MUL_REF4"; break;
    case LemmaKind::MUL_REF5: os << "MUL_REF5"; break;
    case LemmaKind::MUL_REF6: os << "MUL_REF6"; break;
    case LemmaKind::MUL_REF7: os << "MUL_REF7"; break;
    case LemmaKind::MUL_REF8: os << "MUL_REF8"; break;
    case LemmaKind::MUL_REF9: os << "MUL_REF9"; break;
    case LemmaKind::MUL_REF10: os << "MUL_REF10"; break;
    case LemmaKind::MUL_REF11: os << "MUL_REF11"; break;
    case LemmaKind::MUL_REF12: os << "MUL_REF12"; break;
    case LemmaKind::MUL_REF13: os << "MUL_REF13"; break;
    case LemmaKind::MUL_REF14: os << "MUL_REF14"; break;
    case LemmaKind::MUL_REF15: os << "MUL_REF15"; break;
    case LemmaKind::MUL_REF16: os << "MUL_REF16"; break;
    case LemmaKind::MUL_REF17: os << "MUL_REF17"; break;
    case LemmaKind::MUL_REF18: os << "MUL_REF18"; break;
    case LemmaKind::MUL_NOOVFL1: os << "MUL_NOOVFL1"; break;
    case LemmaKind::MUL_NOOVFL2: os << "MUL_NOOVFL2"; break;
    case LemmaKind::MUL_NOOVFL3: os << "MUL_NOOVFL3"; break;
    case LemmaKind::MUL_NOOVFL4: os << "MUL_NOOVFL4"; break;
    case LemmaKind::MUL_NOOVFL5: os << "MUL_NOOVFL5"; break;
    case LemmaKind::MUL_NOOVFL_REF1: os << "MUL_NOOVFL_REF1"; break;
    case LemmaKind::MUL_NOOVFL_REF2: os << "MUL_NOOVFL_REF2"; break;
    case LemmaKind::MUL_NOOVFL_REF3: os << "MUL_NOOVFL_REF3"; break;
    case LemmaKind::MUL_NOOVFL_REF4: os << "MUL_NOOVFL_REF4"; break;
    case LemmaKind::MUL_NOOVFL_REF5: os << "MUL_NOOVFL_REF5"; break;
    case LemmaKind::MUL_NOOVFL_REF6: os << "MUL_NOOVFL_REF6"; break;
    case LemmaKind::MUL_NOOVFL_REF7: os << "MUL_NOOVFL_REF7"; break;
    case LemmaKind::MUL_NOOVFL_REF8: os << "MUL_NOOVFL_REF8"; break;
    case LemmaKind::MUL_NOOVFL_REF9: os << "MUL_NOOVFL_REF9"; break;
    case LemmaKind::MUL_NOOVFL_REF10: os << "MUL_NOOVFL_REF10"; break;
    case LemmaKind::MUL_NOOVFL_REF11: os << "MUL_NOOVFL_REF11"; break;
    case LemmaKind::MUL_NOOVFL_REF12: os << "MUL_NOOVFL_REF12"; break;
    case LemmaKind::MUL_NOOVFL_REF13: os << "MUL_NOOVFL_REF13"; break;
    case LemmaKind::MUL_NOOVFL_REF14: os << "MUL_NOOVFL_REF14"; break;
    case LemmaKind::MUL_NOOVFL_REF15: os << "MUL_NOOVFL_REF15"; break;
    case LemmaKind::MUL_NOOVFL_REF16: os << "MUL_NOOVFL_REF16"; break;
    case LemmaKind::MUL_NOOVFL_REF17: os << "MUL_NOOVFL_REF17"; break;
    case LemmaKind::MUL_NOOVFL_REF18: os << "MUL_NOOVFL_REF18"; break;
    case LemmaKind::MUL_NOOVFL_REF19: os << "MUL_NOOVFL_REF19"; break;
    case LemmaKind::MUL_NOOVFL_REF20: os << "MUL_NOOVFL_REF20"; break;
    case LemmaKind::MUL_NOOVFL_REF21: os << "MUL_NOOVFL_REF21"; break;
    case LemmaKind::MUL_NOOVFL_REF22: os << "MUL_NOOVFL_REF22"; break;
    case LemmaKind::MUL_NOOVFL_REF23: os << "MUL_NOOVFL_REF23"; break;
    case LemmaKind::MUL_NOOVFL_REF24: os << "MUL_NOOVFL_REF24"; break;
    case LemmaKind::MUL_NOOVFL_REF25: os << "MUL_NOOVFL_REF25"; break;
    case LemmaKind::MUL_NOOVFL_REF26: os << "MUL_NOOVFL_REF26"; break;
    case LemmaKind::MUL_NOOVFL_REF27: os << "MUL_NOOVFL_REF27"; break;
    case LemmaKind::MUL_NOOVFL_REF28: os << "MUL_NOOVFL_REF28"; break;
    case LemmaKind::MUL_NOOVFL_REF29: os << "MUL_NOOVFL_REF29"; break;
    case LemmaKind::MUL_OVFL_REF1: os << "MUL_OVFL_REF1"; break;
    case LemmaKind::MUL_OVFL_REF2: os << "MUL_OVFL_REF2"; break;
    case LemmaKind::MUL_OVFL_REF3: os << "MUL_OVFL_REF3"; break;
    case LemmaKind::MUL_OVFL_REF4: os << "MUL_OVFL_REF4"; break;
    case LemmaKind::MUL_OVFL_REF5: os << "MUL_OVFL_REF5"; break;
    case LemmaKind::MUL_OVFL_REF6: os << "MUL_OVFL_REF6"; break;
    case LemmaKind::MUL_OVFL_REF7: os << "MUL_OVFL_REF7"; break;
    case LemmaKind::MUL_OVFL_REF8: os << "MUL_OVFL_REF8"; break;
    case LemmaKind::MUL_OVFL_REF9: os << "MUL_OVFL_REF9"; break;
    case LemmaKind::MUL_OVFL_REF10: os << "MUL_OVFL_REF10"; break;
    case LemmaKind::MUL_OVFL_REF11: os << "MUL_OVFL_REF11"; break;
    case LemmaKind::MUL_OVFL_REF12: os << "MUL_OVFL_REF12"; break;
    case LemmaKind::MUL_OVFL_REF13: os << "MUL_OVFL_REF13"; break;
    case LemmaKind::MUL_OVFL_REF14: os << "MUL_OVFL_REF14"; break;
    case LemmaKind::MUL_OVFL_REF15: os << "MUL_OVFL_REF15"; break;
    case LemmaKind::MUL_OVFL_REF16: os << "MUL_OVFL_REF16"; break;
    case LemmaKind::MUL_OVFL_REF17: os << "MUL_OVFL_REF17"; break;
    case LemmaKind::MUL_OVFL_REF18: os << "MUL_OVFL_REF18"; break;
    case LemmaKind::MUL_OVFL_REF19: os << "MUL_OVFL_REF19"; break;
    case LemmaKind::MUL_OVFL_REF20: os << "MUL_OVFL_REF20"; break;
    case LemmaKind::MUL_OVFL_REF21: os << "MUL_OVFL_REF21"; break;
    case LemmaKind::MUL_OVFL_REF22: os << "MUL_OVFL_REF22"; break;
    case LemmaKind::MUL_OVFL_REF23: os << "MUL_OVFL_REF23"; break;
    case LemmaKind::MUL_OVFL_REF24: os << "MUL_OVFL_REF24"; break;
    case LemmaKind::MUL_OVFL_REF25: os << "MUL_OVFL_REF25"; break;
    case LemmaKind::MUL_OVFL_REF26: os << "MUL_OVFL_REF26"; break;
    case LemmaKind::MUL_OVFL_REF27: os << "MUL_OVFL_REF27"; break;
    case LemmaKind::MUL_OVFL_REF28: os << "MUL_OVFL_REF28"; break;
    case LemmaKind::MUL_OVFL_REF29: os << "MUL_OVFL_REF29"; break;
    case LemmaKind::MUL_OVFL_REF30: os << "MUL_OVFL_REF30"; break;
    case LemmaKind::MUL_OVFL_REF31: os << "MUL_OVFL_REF31"; break;
    case LemmaKind::MUL_OVFL_REF32: os << "MUL_OVFL_REF32"; break;
    case LemmaKind::MUL_OVFL_REF33: os << "MUL_OVFL_REF33"; break;
    case LemmaKind::MUL_OVFL_REF34: os << "MUL_OVFL_REF34"; break;
    case LemmaKind::MUL_OVFL_REF35: os << "MUL_OVFL_REF35"; break;
    case LemmaKind::MUL_OVFL_REF36: os << "MUL_OVFL_REF36"; break;
    case LemmaKind::MUL_OVFL_REF37: os << "MUL_OVFL_REF37"; break;
    case LemmaKind::MUL_OVFL_REF38: os << "MUL_OVFL_REF38"; break;
    case LemmaKind::MUL_OVFL_REF39: os << "MUL_OVFL_REF39"; break;
    case LemmaKind::MUL_OVFL_REF40: os << "MUL_OVFL_REF40"; break;
    case LemmaKind::MUL_OVFL_REF41: os << "MUL_OVFL_REF41"; break;
    case LemmaKind::MUL_OVFL_REF42: os << "MUL_OVFL_REF42"; break;
    case LemmaKind::MUL_OVFL_REF43: os << "MUL_OVFL_REF43"; break;
    case LemmaKind::MUL_OVFL_REF44: os << "MUL_OVFL_REF44"; break;
    case LemmaKind::MUL_OVFL_REF45: os << "MUL_OVFL_REF45"; break;
    case LemmaKind::MUL_OVFL_REF46: os << "MUL_OVFL_REF46"; break;
    case LemmaKind::MUL_OVFL_REF47: os << "MUL_OVFL_REF47"; break;
    case LemmaKind::MUL_OVFL_REF48: os << "MUL_OVFL_REF48"; break;
    case LemmaKind::MUL_OVFL_REF49: os << "MUL_OVFL_REF49"; break;
    case LemmaKind::MUL_VALUE: os << "MUL_VALUE"; break;

    case LemmaKind::UDIV_POW2: os << "UDIV_POW2"; break;
    case LemmaKind::UDIV_REF1: os << "UDIV_REF1"; break;
    case LemmaKind::UDIV_REF2: os << "UDIV_REF2"; break;
    case LemmaKind::UDIV_REF3: os << "UDIV_REF3"; break;
    case LemmaKind::UDIV_REF4: os << "UDIV_REF4"; break;
    case LemmaKind::UDIV_REF5: os << "UDIV_REF5"; break;
    case LemmaKind::UDIV_REF6: os << "UDIV_REF6"; break;
    case LemmaKind::UDIV_REF7: os << "UDIV_REF7"; break;
    case LemmaKind::UDIV_REF8: os << "UDIV_REF8"; break;
    case LemmaKind::UDIV_REF9: os << "UDIV_REF9"; break;
    case LemmaKind::UDIV_REF10: os << "UDIV_REF10"; break;
    case LemmaKind::UDIV_REF11: os << "UDIV_REF11"; break;
    case LemmaKind::UDIV_REF12: os << "UDIV_REF12"; break;
    case LemmaKind::UDIV_REF13: os << "UDIV_REF13"; break;
    case LemmaKind::UDIV_REF14: os << "UDIV_REF14"; break;
    case LemmaKind::UDIV_REF15: os << "UDIV_REF15"; break;
    case LemmaKind::UDIV_REF16: os << "UDIV_REF16"; break;
    case LemmaKind::UDIV_REF17: os << "UDIV_REF17"; break;
    case LemmaKind::UDIV_REF18: os << "UDIV_REF18"; break;
    case LemmaKind::UDIV_REF19: os << "UDIV_REF19"; break;
    case LemmaKind::UDIV_REF20: os << "UDIV_REF20"; break;
    case LemmaKind::UDIV_REF21: os << "UDIV_REF21"; break;
    case LemmaKind::UDIV_REF22: os << "UDIV_REF22"; break;
    case LemmaKind::UDIV_REF23: os << "UDIV_REF23"; break;
    case LemmaKind::UDIV_REF24: os << "UDIV_REF24"; break;
    case LemmaKind::UDIV_REF25: os << "UDIV_REF25"; break;
    case LemmaKind::UDIV_REF26: os << "UDIV_REF26"; break;
    case LemmaKind::UDIV_REF27: os << "UDIV_REF27"; break;
    case LemmaKind::UDIV_REF28: os << "UDIV_REF28"; break;
    case LemmaKind::UDIV_REF29: os << "UDIV_REF29"; break;
    case LemmaKind::UDIV_REF30: os << "UDIV_REF30"; break;
    case LemmaKind::UDIV_REF31: os << "UDIV_REF31"; break;
    case LemmaKind::UDIV_REF32: os << "UDIV_REF32"; break;
    case LemmaKind::UDIV_REF33: os << "UDIV_REF33"; break;
    case LemmaKind::UDIV_REF34: os << "UDIV_REF34"; break;
    case LemmaKind::UDIV_REF35: os << "UDIV_REF35"; break;
    case LemmaKind::UDIV_REF36: os << "UDIV_REF36"; break;
    case LemmaKind::UDIV_REF37: os << "UDIV_REF37"; break;
    case LemmaKind::UDIV_REF38: os << "UDIV_REF38"; break;
    case LemmaKind::UDIV_VALUE: os << "UDIV_VALUE"; break;

    case LemmaKind::UREM_POW2: os << "UREM_POW2"; break;
    case LemmaKind::UREM_REF1: os << "UREM_REF1"; break;
    case LemmaKind::UREM_REF2: os << "UREM_REF2"; break;
    case LemmaKind::UREM_REF3: os << "UREM_REF3"; break;
    case LemmaKind::UREM_REF4: os << "UREM_REF4"; break;
    case LemmaKind::UREM_REF5: os << "UREM_REF5"; break;
    case LemmaKind::UREM_REF6: os << "UREM_REF6"; break;
    case LemmaKind::UREM_REF7: os << "UREM_REF7"; break;
    case LemmaKind::UREM_REF8: os << "UREM_REF8"; break;
    case LemmaKind::UREM_REF9: os << "UREM_REF9"; break;
    case LemmaKind::UREM_REF10: os << "UREM_REF10"; break;
    case LemmaKind::UREM_REF11: os << "UREM_REF11"; break;
    case LemmaKind::UREM_REF12: os << "UREM_REF12"; break;
    case LemmaKind::UREM_REF13: os << "UREM_REF13"; break;
    case LemmaKind::UREM_REF14: os << "UREM_REF14"; break;
    case LemmaKind::UREM_VALUE: os << "UREM_VALUE"; break;

    case LemmaKind::ADD_ZERO: os << "ADD_ZERO"; break;
    case LemmaKind::ADD_SAME: os << "ADD_SAME"; break;
    case LemmaKind::ADD_INV: os << "ADD_INV"; break;
    case LemmaKind::ADD_OVFL: os << "ADD_OVFL1"; break;
    case LemmaKind::ADD_NOOVFL: os << "ADD_OVFL2"; break;
    case LemmaKind::ADD_OR: os << "ADD_OR"; break;
    case LemmaKind::ADD_REF1: os << "ADD_REF1"; break;
    case LemmaKind::ADD_REF2: os << "ADD_REF2"; break;
    case LemmaKind::ADD_REF3: os << "ADD_REF3"; break;
    case LemmaKind::ADD_REF4: os << "ADD_REF4"; break;
    case LemmaKind::ADD_REF5: os << "ADD_REF5"; break;
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
Lemma<LemmaKind::MUL_ZERO>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  size_t size     = x.type().bv_size();
  Node zero       = nm.mk_value(BitVector::mk_zero(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, zero}), nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::MUL_ONE>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  size_t size     = x.type().bv_size();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, one}), nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::MUL_IC>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  (void) x;
  NodeManager& nm = NodeManager::get();
  Node lhs        = nm.mk_node(
      Kind::BV_AND,
      {nm.mk_node(Kind::BV_OR, {nm.mk_node(Kind::BV_NEG, {s}), s}), t});
  return nm.mk_node(Kind::EQUAL, {lhs, t});
}

template <>
Node
Lemma<LemmaKind::MUL_NEG>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node ones       = nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, ones}),
       nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_NEG, {x})})});
}

template <>
Node
Lemma<LemmaKind::MUL_ODD>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::EQUAL,
                    {nm.mk_node(Kind::BV_EXTRACT, {t}, {0, 0}),
                     nm.mk_node(Kind::BV_AND,
                                {
                                    nm.mk_node(Kind::BV_EXTRACT, {x}, {0, 0}),
                                    nm.mk_node(Kind::BV_EXTRACT, {s}, {0, 0}),
                                })});
}

template <>
Node
Lemma<LemmaKind::MUL_POW2>::instance(const Node& val_x,
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
    NodeManager& nm      = NodeManager::get();
    const auto& val_pow2 = val_x.value<BitVector>();
    Node shift_by        = nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = nm.mk_node(Kind::EQUAL, {x, val_x});
    return nm.mk_node(
        Kind::IMPLIES,
        {eq,
         nm.mk_node(Kind::EQUAL,
                    {t, nm.mk_node(Kind::BV_SHL, {s, shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::MUL_NEG_POW2>::instance(const Node& val_x,
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
    NodeManager& nm = NodeManager::get();
    Node shift_by   = nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = nm.mk_node(Kind::EQUAL, {x, val_x});
    return nm.mk_node(
        Kind::IMPLIES,
        {eq,
         nm.mk_node(Kind::EQUAL,
                    {t,
                     nm.mk_node(Kind::BV_SHL,
                                {nm.mk_node(Kind::BV_NEG, {s}), shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::MUL_REF1>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::NOT,
      {nm.mk_node(
          Kind::EQUAL,
          {s,
           nm.mk_node(
               Kind::BV_NOT,
               {nm.mk_node(
                   Kind::BV_OR,
                   {t,
                    nm.mk_node(Kind::BV_AND,
                               {one, nm.mk_node(Kind::BV_OR, {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF2>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {s,
       nm.mk_node(
           Kind::BV_AND,
           {t,
            nm.mk_node(Kind::BV_NEG,
                       {nm.mk_node(Kind::BV_OR,
                                   {t, nm.mk_node(Kind::BV_NOT, {x})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF3>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_node(Kind::BV_AND, {x, t}),
       nm.mk_node(Kind::BV_OR, {s, nm.mk_node(Kind::BV_NOT, {t})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF4>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {one,
       nm.mk_node(
           Kind::BV_NOT,
           {nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_AND, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF5>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {t,
       nm.mk_node(
           Kind::BV_NOT,
           {nm.mk_node(
               Kind::BV_OR,
               {t,
                nm.mk_node(Kind::BV_OR,
                           {one, nm.mk_node(Kind::BV_AND, {x, s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF6>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {s, nm.mk_node(Kind::BV_SHL, {nm.mk_node(Kind::BV_SHR, {t, x}), one})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF7>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::EQUAL,
      {x,
       nm.mk_node(Kind::BV_SHL,
                  {x,
                   nm.mk_node(Kind::BV_AND,
                              {s, nm.mk_node(Kind::BV_SHR, {one, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF8>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::BV_UGE,
                    {x,
                     nm.mk_node(Kind::BV_SHR,
                                {nm.mk_node(Kind::BV_NEG, {t}),
                                 nm.mk_node(Kind::BV_NOT, {s})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF9>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {x, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_SHR, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF10>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHR,
           {t, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_NEG, {s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF11>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_SHR, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF12>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_NOT,
           {nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_ADD, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF13>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {t, nm.mk_node(Kind::BV_OR, {one, nm.mk_node(Kind::BV_ADD, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF14>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {t,
       nm.mk_node(
           Kind::BV_OR,
           {one,
            nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_XOR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF15>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::DISTINCT,
                    {t,
                     nm.mk_node(Kind::BV_OR,
                                {nm.mk_node(Kind::BV_NOT, {one}),
                                 nm.mk_node(Kind::BV_XOR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF16>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_ADD,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_SUB, {t, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF17>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_ADD,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_SUB, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_REF18>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_SUB,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_SUB, {s, t})})})});
}

namespace {
Node
mul_noovfl_condition(const Node& val_x,
                     const Node& val_s,
                     const Node& x,
                     const Node& s)
{
  uint64_t clz_x = val_x.value<BitVector>().count_leading_zeros();
  uint64_t clz_s = val_s.value<BitVector>().count_leading_zeros();

  uint64_t size = val_x.type().bv_size();
  if (clz_x + clz_s >= size)
  {
    NodeManager& nm = NodeManager::get();
    Node ub_x       = nm.mk_value(BitVector::mk_one(size).ibvshl(size - clz_x));
    Node ub_s       = nm.mk_value(BitVector::mk_one(size).ibvshl(size - clz_s));
    return nm.mk_node(Kind::AND,
                      {nm.mk_node(Kind::BV_ULT, {x, ub_x}),
                       nm.mk_node(Kind::BV_ULT, {s, ub_s})});
  }
  return Node();
}

Node
mul_ovfl_condition(const Node& val_x,
                   const Node& val_s,
                   const Node& x,
                   const Node& s)
{
  uint64_t clz_x = val_x.value<BitVector>().count_leading_zeros();
  uint64_t clz_s = val_s.value<BitVector>().count_leading_zeros();

  uint64_t size = val_x.type().bv_size();
  if (clz_x + clz_s < size - 1)
  {
    NodeManager& nm = NodeManager::get();
    Node ub_x = nm.mk_value(BitVector::mk_one(size).ibvshl(size - clz_x - 1));
    Node ub_s = nm.mk_value(BitVector::mk_one(size).ibvshl(size - clz_s - 1));
    return nm.mk_node(Kind::AND,
                      {nm.mk_node(Kind::BV_UGT, {x, ub_x}),
                       nm.mk_node(Kind::BV_UGT, {s, ub_s})});
  }
  return Node();
}
}  // namespace

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL1>::instance(const Node& val_x,
                                        const Node& val_s,
                                        const Node& val_t,
                                        const Node& x,
                                        const Node& s,
                                        const Node& t) const
{
  (void) val_t;
  // (=> (noovfl) (bvuge (bvneg x) (bvneg t)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::IMPLIES,
                    {noovfl,
                     nm.mk_node(Kind::BV_UGE,
                                {nm.mk_node(Kind::BV_NEG, {x}),
                                 nm.mk_node(Kind::BV_NEG, {t})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL2>::instance(const Node& val_x,
                                        const Node& val_s,
                                        const Node& val_t,
                                        const Node& x,
                                        const Node& s,
                                        const Node& t) const
{
  (void) val_t;
  // (=> (noovfl) (bvuge (bvneg s) (bvand x t)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::IMPLIES,
                    {noovfl,
                     nm.mk_node(Kind::BV_UGE,
                                {nm.mk_node(Kind::BV_NEG, {s}),
                                 nm.mk_node(Kind::BV_AND, {x, t})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL3>::instance(const Node& val_x,
                                        const Node& val_s,
                                        const Node& val_t,
                                        const Node& x,
                                        const Node& s,
                                        const Node& t) const
{
  (void) val_t;
  // (=> (noovfl) (bvuge t (bvand x (bvneg s))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {t, nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_NEG, {s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL4>::instance(const Node& val_x,
                                        const Node& val_s,
                                        const Node& val_t,
                                        const Node& x,
                                        const Node& s,
                                        const Node& t) const
{
  (void) val_t;
  (void) t;
  // (=> (noovfl) (bvuge (bvor #b0001 (bvnot x)) s))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {nm.mk_node(Kind::BV_OR, {one, nm.mk_node(Kind::BV_NOT, {x})}),
            s})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL5>::instance(const Node& val_x,
                                        const Node& val_s,
                                        const Node& val_t,
                                        const Node& x,
                                        const Node& s,
                                        const Node& t) const
{
  (void) val_t;
  // (=> (noovfl) (not (= x (bvor s (bvnot (bvor x t))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_OR,
                       {s,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_OR, {x, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF1>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;
  // (=>
  //   (and (bvule x (bvshl 1 bw/2)) (bvule s (bvshl 1 bw/2)))
  //   (not (bvult (bvneg x) (bvor (bvneg t) (bvand x s))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::BV_UGE,
                  {nm.mk_node(Kind::BV_NEG, {x}),
                   nm.mk_node(Kind::BV_OR,
                              {nm.mk_node(Kind::BV_NEG, {t}),
                               nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF2>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge t (bvneg (bvand (bvneg x) (bvneg s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {t,
            nm.mk_node(Kind::BV_NEG,
                       {nm.mk_node(Kind::BV_AND,
                                   {nm.mk_node(Kind::BV_NEG, {x}),
                                    nm.mk_node(Kind::BV_NEG, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF3>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (= t (bvand t (bvor x (bvneg x)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::EQUAL,
           {t,
            nm.mk_node(Kind::BV_AND,
                       {t,
                        nm.mk_node(Kind::BV_OR,
                                   {x, nm.mk_node(Kind::BV_NEG, {x})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF4>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (= t (bvor t (bvand x (bvand s #b0001)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::EQUAL,
           {t,
            nm.mk_node(
                Kind::BV_OR,
                {t,
                 nm.mk_node(Kind::BV_AND,
                            {x, nm.mk_node(Kind::BV_AND, {s, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF5>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvneg s) (bvor (bvneg t) (bvand x s))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::BV_UGE,
                  {nm.mk_node(Kind::BV_NEG, {s}),
                   nm.mk_node(Kind::BV_OR,
                              {nm.mk_node(Kind::BV_NEG, {t}),
                               nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF6>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvneg s) (bvneg (bvand t (bvnot s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {nm.mk_node(Kind::BV_NEG, {s}),
            nm.mk_node(Kind::BV_NEG,
                       {nm.mk_node(Kind::BV_AND,
                                   {t, nm.mk_node(Kind::BV_NOT, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF7>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvneg x) (bvneg (bvand t (bvnot x)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {nm.mk_node(Kind::BV_NEG, {x}),
            nm.mk_node(Kind::BV_NEG,
                       {nm.mk_node(Kind::BV_AND,
                                   {t, nm.mk_node(Kind::BV_NOT, {x})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF8>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge #b0001 (bvand x (bvand t (bvneg (bvor x s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {one,
            nm.mk_node(Kind::BV_AND,
                       {x,
                        nm.mk_node(Kind::BV_AND,
                                   {t,
                                    nm.mk_node(Kind::BV_NEG,
                                               {nm.mk_node(Kind::BV_OR,
                                                           {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF9>::instance(const Node& val_x,
                                            const Node& val_s,
                                            const Node& val_t,
                                            const Node& x,
                                            const Node& s,
                                            const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct s (bvor x (bvnot (bvor t (bvand s #b0001))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {s,
            nm.mk_node(Kind::BV_OR,
                       {x,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_OR,
                                               {t,
                                                nm.mk_node(Kind::BV_AND,
                                                           {s, one})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF10>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvand t (bvneg x)) (bvand x s)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::BV_UGE,
                  {nm.mk_node(Kind::BV_AND, {t, nm.mk_node(Kind::BV_NEG, {x})}),
                   nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF11>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct s (bvnot (bvor t (bvand #b0001 (bvor x s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {s,
            nm.mk_node(
                Kind::BV_NOT,
                {nm.mk_node(
                    Kind::BV_OR,
                    {t,
                     nm.mk_node(Kind::BV_AND,
                                {one, nm.mk_node(Kind::BV_OR, {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF12>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (distinct t (bvor #b0001 (bvneg (bvnot (bvor x s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {t,
            nm.mk_node(Kind::BV_OR,
                       {one,
                        nm.mk_node(Kind::BV_NEG,
                                   {nm.mk_node(Kind::BV_NOT,
                                               {nm.mk_node(Kind::BV_OR,
                                                           {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF13>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvneg s) (bvand x t)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::IMPLIES,
                    {noovfl,
                     nm.mk_node(Kind::BV_UGE,
                                {nm.mk_node(Kind::BV_NEG, {s}),
                                 nm.mk_node(Kind::BV_AND, {x, t})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF14>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge (bvand t (bvneg x)) (bvand s t)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::BV_UGE,
                  {nm.mk_node(Kind::BV_AND, {t, nm.mk_node(Kind::BV_NEG, {x})}),
                   nm.mk_node(Kind::BV_AND, {s, t})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF15>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct x (bvnot (bvor t (bvand #b0001 (bvor x s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_NOT,
                {nm.mk_node(
                    Kind::BV_OR,
                    {t,
                     nm.mk_node(Kind::BV_AND,
                                {one, nm.mk_node(Kind::BV_OR, {x, s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF16>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct x (bvor s (bvnot (bvor x (bvor t #b0001))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_OR,
                {s,
                 nm.mk_node(Kind::BV_NOT,
                            {nm.mk_node(
                                Kind::BV_OR,
                                {x, nm.mk_node(Kind::BV_OR, {t, one})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF17>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct x (bvor s (bvnot (bvor t (bvand x #b0001))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_OR,
                       {s,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_OR,
                                               {t,
                                                nm.mk_node(Kind::BV_AND,
                                                           {x, one})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF18>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;
  (void) t;

  // (=>
  //   noovfl_condition
  //   (distinct #b0001 (bvnot (bvand (bvneg x) (bvor x s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(Kind::BV_NOT,
                       {nm.mk_node(Kind::BV_AND,
                                   {nm.mk_node(Kind::BV_NEG, {x}),
                                    nm.mk_node(Kind::BV_OR, {x, s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF19>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=>
  //   noovfl_condition
  //   (distinct #b0001 (bvor x (bvnot (bvand t (bvneg s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(
                Kind::BV_OR,
                {x,
                 nm.mk_node(
                     Kind::BV_NOT,
                     {nm.mk_node(Kind::BV_AND,
                                 {t, nm.mk_node(Kind::BV_NEG, {s})})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF20>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;
  (void) t;

  // (=>
  //   noovfl_condition
  //   (distinct #b0001 (bvnot (bvand (bvneg s) (bvor x s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(Kind::BV_NOT,
                       {nm.mk_node(Kind::BV_AND,
                                   {nm.mk_node(Kind::BV_NEG, {s}),
                                    nm.mk_node(Kind::BV_OR, {x, s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF21>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge s (bvlshr t (bvnot (bvneg x)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {s,
            nm.mk_node(Kind::BV_SHR,
                       {t,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_NEG, {x})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF22>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge x (bvlshr t (bvnot (bvneg s))))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {x,
            nm.mk_node(Kind::BV_SHR,
                       {t,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_NEG, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF23>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;
  (void) t;

  // (=> noovfl_condition (distinct x (bvshl (bvnot #b0001) (bvlshr x s))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::DISTINCT,
                  {x,
                   nm.mk_node(Kind::BV_SHL,
                              {nm.mk_node(Kind::BV_NOT, {one}),
                               nm.mk_node(Kind::BV_SHR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF24>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (distinct x (bvadd t (bvnot (bvshl x t)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_ADD,
                       {t,
                        nm.mk_node(Kind::BV_NOT,
                                   {nm.mk_node(Kind::BV_SHL, {x, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF25>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (distinct x (bvnot (bvshl x (bvadd s t)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_NOT,
                       {nm.mk_node(Kind::BV_SHL,
                                   {x, nm.mk_node(Kind::BV_ADD, {s, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF26>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (bvuge x (bvlshr t (bvadd t (bvnot s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::BV_UGE,
           {x,
            nm.mk_node(Kind::BV_SHR,
                       {t,
                        nm.mk_node(Kind::BV_ADD,
                                   {t, nm.mk_node(Kind::BV_NOT, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF27>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (distinct t (bvor #b0001 (bvadd x s))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::DISTINCT,
                  {t,
                   nm.mk_node(Kind::BV_OR,
                              {one, nm.mk_node(Kind::BV_ADD, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF28>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;

  // (=> noovfl_condition (distinct #b0001 (bvor (bvnot t) (bvxor x s)))))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(Kind::DISTINCT,
                  {one,
                   nm.mk_node(Kind::BV_OR,
                              {nm.mk_node(Kind::BV_NOT, {t}),
                               nm.mk_node(Kind::BV_XOR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_NOOVFL_REF29>::instance(const Node& val_x,
                                             const Node& val_s,
                                             const Node& val_t,
                                             const Node& x,
                                             const Node& s,
                                             const Node& t) const
{
  (void) val_t;
  (void) t;

  // (=>
  //   noovfl_condition
  //   (distinct x (bvlshr (bvsub (bvlshr x s) #b0001) #b0001)))
  Node noovfl = mul_noovfl_condition(val_x, val_s, x, s);
  if (noovfl.is_null())
  {
    return Node();
  }
  uint64_t size   = x.type().bv_size();
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {noovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_SHR,
                       {nm.mk_node(Kind::BV_SUB,
                                   {nm.mk_node(Kind::BV_SHR, {x, s}), one}),
                        one})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF1>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (= (bvand (bvor (bvneg s) s) t) t))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::EQUAL,
                  {nm.mk_node(Kind::BV_AND,
                              {nm.mk_node(Kind::BV_OR,
                                          {nm.mk_node(Kind::BV_NEG, {s}), s}),
                               t}),
                   t})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF5>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (bvuge (bvand x t) (bvand s #b0001)))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::IMPLIES,
                    {ovfl,
                     nm.mk_node(Kind::BV_UGE,
                                {nm.mk_node(Kind::BV_AND, {x, t}),
                                 nm.mk_node(Kind::BV_AND, {s, one})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF6>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvand x (bvshl t #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {x,
                   nm.mk_node(Kind::BV_AND,
                              {x, nm.mk_node(Kind::BV_SHL, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF7>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvand s (bvor #b0001 (bvand x t)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_AND,
                {s,
                 nm.mk_node(Kind::BV_OR,
                            {one, nm.mk_node(Kind::BV_AND, {x, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF8>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (bvuge (bvand s t) (bvand x #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::IMPLIES,
                    {ovfl,
                     nm.mk_node(Kind::BV_UGE,
                                {nm.mk_node(Kind::BV_AND, {s, t}),
                                 nm.mk_node(Kind::BV_AND, {x, one})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF9>::instance(const Node& val_x,
                                          const Node& val_s,
                                          const Node& val_t,
                                          const Node& x,
                                          const Node& s,
                                          const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s)  (distinct #b0001 (bvand s (bvxor x t))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(Kind::BV_AND, {s, nm.mk_node(Kind::BV_XOR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF10>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvxor s (bvneg (bvnot t)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_XOR,
                       {s,
                        nm.mk_node(Kind::BV_NEG,
                                   {nm.mk_node(Kind::BV_NOT, {t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF11>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvlshr t (bvand #b0001 (bvxor x s)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_SHR,
                {t,
                 nm.mk_node(Kind::BV_AND,
                            {one, nm.mk_node(Kind::BV_XOR, {x, s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF12>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct t (bvshl s (bvand x #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {t,
                   nm.mk_node(Kind::BV_SHL,
                              {s, nm.mk_node(Kind::BV_AND, {x, one})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF13>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (= x (bvor x (bvand t #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::EQUAL,
                  {x,
                   nm.mk_node(Kind::BV_OR,
                              {x, nm.mk_node(Kind::BV_AND, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF14>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct #b0001 (bvand x (bvor s t))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_OR, {s, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF15>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvneg (bvand s (bvxor t #b0001)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_NEG,
                {nm.mk_node(Kind::BV_AND,
                            {s, nm.mk_node(Kind::BV_XOR, {t, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF16>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvxor s (bvor t (bvxor s #b0001)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_XOR,
                {s,
                 nm.mk_node(Kind::BV_OR,
                            {t, nm.mk_node(Kind::BV_XOR, {s, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF17>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct t (bvor s (bvneg x))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {t, nm.mk_node(Kind::BV_OR, {s, nm.mk_node(Kind::BV_NEG, {x})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF18>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct t (bvor x (bvneg s))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {t, nm.mk_node(Kind::BV_OR, {x, nm.mk_node(Kind::BV_NEG, {s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF20>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct t (bvshl x (bvand s #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {t,
                   nm.mk_node(Kind::BV_SHL,
                              {x, nm.mk_node(Kind::BV_AND, {s, one})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF21>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvneg (bvshl t (bvand s #b0001)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_NEG,
                {nm.mk_node(Kind::BV_SHL,
                            {t, nm.mk_node(Kind::BV_AND, {s, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF22>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct t (bvor #b0001 (bvand x s))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {t,
                   nm.mk_node(Kind::BV_OR,
                              {one, nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF24>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvlshr t (bvlshr s #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {x,
                   nm.mk_node(Kind::BV_SHR,
                              {t, nm.mk_node(Kind::BV_SHR, {s, one})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF26>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvneg (bvlshr t (bvneg s)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_NEG,
                       {nm.mk_node(Kind::BV_SHR,
                                   {t, nm.mk_node(Kind::BV_NEG, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF28>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvand s (bvxor #b0001 (bvneg t)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(Kind::BV_AND,
                       {s,
                        nm.mk_node(Kind::BV_XOR,
                                   {one, nm.mk_node(Kind::BV_NEG, {t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF29>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct #b0001 (bvand s (bvor x t))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {one,
            nm.mk_node(Kind::BV_AND, {s, nm.mk_node(Kind::BV_OR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF31>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct s (bvshl x (bvnot t))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {s, nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_NOT, {t})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF34>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvor t (bvxor x (bvor s #b0001)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_OR,
                {t,
                 nm.mk_node(Kind::BV_XOR,
                            {x, nm.mk_node(Kind::BV_OR, {s, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF40>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvxor s (bvor #b0001 (bvand x t)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_XOR,
                {s,
                 nm.mk_node(Kind::BV_OR,
                            {one, nm.mk_node(Kind::BV_AND, {x, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF43>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvxor s (bvor t (bvxor x #b0001)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_XOR,
                {s,
                 nm.mk_node(Kind::BV_OR,
                            {t, nm.mk_node(Kind::BV_XOR, {x, one})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF47>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct x (bvxor s (bvor #b0001 (bvand s t)))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(
           Kind::DISTINCT,
           {x,
            nm.mk_node(
                Kind::BV_XOR,
                {x,
                 nm.mk_node(Kind::BV_OR,
                            {one, nm.mk_node(Kind::BV_AND, {s, t})})})})});
}

template <>
Node
Lemma<LemmaKind::MUL_OVFL_REF49>::instance(const Node& val_x,
                                           const Node& val_s,
                                           const Node& val_t,
                                           const Node& x,
                                           const Node& s,
                                           const Node& t) const
{
  (void) val_t;

  // (=> (bvumulo x s) (distinct s (bvand x (bvxor t #b0001))))
  Node ovfl = mul_ovfl_condition(val_x, val_s, x, s);
  if (ovfl.is_null())
  {
    return Node();
  }

  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {ovfl,
       nm.mk_node(Kind::DISTINCT,
                  {s,
                   nm.mk_node(Kind::BV_AND,
                              {x, nm.mk_node(Kind::BV_OR, {t, one})})})});
}

// Unsigned division lemmas

template <>
Node
Lemma<LemmaKind::UDIV_POW2>::instance(const Node& val_x,
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
    NodeManager& nm      = NodeManager::get();
    const auto& val_pow2 = val_s.value<BitVector>();
    Node shift_by        = nm.mk_value(
        BitVector::from_ui(val_pow2.size(), val_pow2.count_trailing_zeros()));
    Node eq = nm.mk_node(Kind::EQUAL, {s, val_s});
    return nm.mk_node(
        Kind::IMPLIES,
        {eq,
         nm.mk_node(Kind::EQUAL,
                    {t, nm.mk_node(Kind::BV_SHR, {x, shift_by})})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::UDIV_REF1>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (= s #b0001) (= t x))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, one}), nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF2>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (and (= s x) (distinct s #b0000)) (= t #b0001))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));

  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::AND,
                                {nm.mk_node(Kind::EQUAL, {s, x}),
                                 nm.mk_node(Kind::DISTINCT, {s, zero})}),
                     nm.mk_node(Kind::EQUAL, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF3>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (= s #b0000) (= t (bvnot #b0000)))
  NodeManager& nm = NodeManager::get();
  Node ones       = nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, zero}), nm.mk_node(Kind::EQUAL, {t, ones})}

  );
}

template <>
Node
Lemma<LemmaKind::UDIV_REF4>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (and (= x #b0000) (distinct s #b0000)) (= t #b0000))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::AND,
                                {nm.mk_node(Kind::EQUAL, {x, zero}),
                                 nm.mk_node(Kind::DISTINCT, {s, zero})}),
                     nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF5>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (distinct s #b0000) (bvule t x))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::DISTINCT, {s, zero}), nm.mk_node(Kind::BV_ULE, {t, x})}

  );
}

template <>
Node
Lemma<LemmaKind::UDIV_REF6>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (let ((_let_1 (bvnot #b0000)))
  //  (=> (and (= s _let_1) (distinct x _let_1)) (= t #b0000)))
  NodeManager& nm = NodeManager::get();
  Node ones       = nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));

  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::AND,
                                {nm.mk_node(Kind::EQUAL, {s, ones}),
                                 nm.mk_node(Kind::DISTINCT, {x, ones})}),
                     nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF7>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (not (bvult x (bvneg (bvand (bvneg s) (bvneg t)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::BV_UGE,
                    {x,
                     nm.mk_node(Kind::BV_NEG,
                                {nm.mk_node(Kind::BV_AND,
                                            {
                                                nm.mk_node(Kind::BV_NEG, {s}),
                                                nm.mk_node(Kind::BV_NEG, {t}),
                                            })})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF8>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (not (bvult (bvneg (bvor s #b0001)) t))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_NEG, {nm.mk_node(Kind::BV_OR, {s, one})}), t

      });
}

template <>
Node
Lemma<LemmaKind::UDIV_REF9>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (not (= t (bvneg (bvand s (bvnot x)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {t,
       nm.mk_node(
           Kind::BV_NEG,
           {nm.mk_node(Kind::BV_AND, {s, nm.mk_node(Kind::BV_NOT, {x})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF10>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= (bvor s t) (bvand x (bvnot #b0001))))
  NodeManager& nm = NodeManager::get();
  Node m          = nm.mk_value(BitVector::mk_one(x.type().bv_size()).ibvnot());
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_node(Kind::BV_OR, {s, t}), nm.mk_node(Kind::BV_AND, {x, m})

      });
}

template <>
Node
Lemma<LemmaKind::UDIV_REF11>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= (bvor s #b0001) (bvand x (bvnot t))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_node(Kind::BV_OR, {s, one}),
       nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_NOT, {t})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF12>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvand x (bvneg t)) (bvand s t)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_NEG, {t})}),
       nm.mk_node(Kind::BV_AND, {s, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF13>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult s (bvlshr x t)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::BV_UGE, {s, nm.mk_node(Kind::BV_SHR, {x, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF14>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvshl (bvlshr s (bvshl s t)) #b0001)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {nm.mk_node(Kind::BV_SHR, {s, nm.mk_node(Kind::BV_SHL, {s, t})}),
            one})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF15>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvlshr (bvshl t #b0001) (bvshl t s))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::BV_UGE,
                    {x,
                     nm.mk_node(Kind::BV_SHR,
                                {nm.mk_node(Kind::BV_SHL, {t, one}),
                                 nm.mk_node(Kind::BV_SHL, {t, s})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF16>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult t (bvshl (bvlshr x s) #b0001)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {t, nm.mk_node(Kind::BV_SHL, {nm.mk_node(Kind::BV_SHR, {x, s}), one})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF17>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvand (bvor x t) (bvshl s #b0001))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::BV_UGE,
                    {x,
                     nm.mk_node(Kind::BV_AND,
                                {nm.mk_node(Kind::BV_OR, {x, t}),
                                 nm.mk_node(Kind::BV_SHL, {s, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF18>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvand (bvor x s) (bvshl t #b0001))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(Kind::BV_UGE,
                    {x,
                     nm.mk_node(Kind::BV_AND,
                                {nm.mk_node(Kind::BV_OR, {x, s}),
                                 nm.mk_node(Kind::BV_SHL, {t, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF19>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= (bvlshr x t) (bvor s t)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_node(Kind::BV_SHR, {x, t}), nm.mk_node(Kind::BV_OR, {s, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF20>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= s (bvnot (bvlshr s (bvlshr t #b0001)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {s,
       nm.mk_node(Kind::BV_NOT,
                  {nm.mk_node(Kind::BV_SHR,
                              {s, nm.mk_node(Kind::BV_SHR, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF21>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (= x (bvnot (bvand x (bvshl t #b0001)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(Kind::BV_NOT,
                  {nm.mk_node(Kind::BV_AND,
                              {x, nm.mk_node(Kind::BV_SHL, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF22>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (bvult x (bvshl x (bvlshr t (bvshl t #b0001)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(Kind::BV_SHL,
                  {x,
                   nm.mk_node(Kind::BV_SHR,
                              {t, nm.mk_node(Kind::BV_SHL, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF23>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult t (bvlshr (bvshl x #b0001) s)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {t, nm.mk_node(Kind::BV_SHR, {nm.mk_node(Kind::BV_SHL, {x, one}), s})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF24>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvshl s (bvnot (bvor x t)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {s, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_OR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF25>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvshl t (bvnot (bvor x s)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {t, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF26>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvxor t (bvlshr t (bvlshr s #b0001)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(Kind::BV_XOR,
                  {t,
                   nm.mk_node(Kind::BV_SHR,
                              {t, nm.mk_node(Kind::BV_SHR, {s, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF27>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvxor s (bvlshr s (bvlshr t #b0001)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(Kind::BV_XOR,
                  {s,
                   nm.mk_node(Kind::BV_SHR,
                              {s, nm.mk_node(Kind::BV_SHR, {t, one})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF28>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult x (bvshl s (bvnot (bvxor x t)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {s, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_XOR, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF29>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  //  UDIV_REF29, // (not (bvult x (bvshl t (bvnot (bvxor x s)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x,
       nm.mk_node(
           Kind::BV_SHL,
           {t, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_XOR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF30>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= x (bvadd t (bvor s (bvadd x s)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_ADD,
           {t,
            nm.mk_node(Kind::BV_OR, {s, nm.mk_node(Kind::BV_ADD, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF31>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (= x (bvadd t (bvadd #b0001 (bvshl #b0001 x)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(Kind::BV_ADD,
                  {t,
                   nm.mk_node(Kind::BV_ADD,
                              {one, nm.mk_node(Kind::BV_SHL, {one, x})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF32>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult s (bvlshr (bvadd x t) t)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {s, nm.mk_node(Kind::BV_SHR, {nm.mk_node(Kind::BV_ADD, {x, t}), t})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF33>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= x (bvadd t (bvadd t (bvor x s)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_ADD,
           {t,
            nm.mk_node(Kind::BV_ADD, {t, nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF34>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvxor s (bvor x t)) (bvxor t #b0001)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_XOR, {s, nm.mk_node(Kind::BV_OR, {x, t})}),
       nm.mk_node(Kind::BV_XOR, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF35>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (= x (bvsub #b0001 (bvshl x (bvadd x t)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_SUB,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_ADD, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF36>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult t (bvlshr x (bvsub s #b0001))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {t, nm.mk_node(Kind::BV_SHR, {x, nm.mk_node(Kind::BV_SUB, {s, one})})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF37>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvsub s #b0001) (bvlshr x t)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_SUB, {s, one}), nm.mk_node(Kind::BV_SHR, {x, t})});
}

template <>
Node
Lemma<LemmaKind::UDIV_REF38>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (= x (bvsub #b0001 (bvshl x (bvsub x t)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_SUB,
           {one,
            nm.mk_node(Kind::BV_SHL, {x, nm.mk_node(Kind::BV_SUB, {x, t})})})});
}

template <>
Node
Lemma<LemmaKind::UREM_POW2>::instance(const Node& val_x,
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
    NodeManager& nm      = NodeManager::get();
    const auto& val_pow2 = val_s.value<BitVector>();
    uint64_t ctz         = val_pow2.count_trailing_zeros();
    Node shift_by = nm.mk_value(BitVector::from_ui(val_pow2.size(), ctz));
    Node eq       = nm.mk_node(Kind::EQUAL, {s, val_s});
    Node rem;
    if (ctz == 0)
    {
      rem = nm.mk_value(BitVector::mk_zero(val_pow2.size()));
    }
    else
    {
      rem = nm.mk_node(Kind::BV_ZERO_EXTEND,
                       {nm.mk_node(Kind::BV_EXTRACT, {x}, {ctz - 1, 0})},
                       {val_pow2.size() - ctz});
    }
    return nm.mk_node(Kind::IMPLIES, {eq, nm.mk_node(Kind::EQUAL, {t, rem})});
  }
  return Node();
}

template <>
Node
Lemma<LemmaKind::UREM_REF1>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (distinct s #b0000) (bvule t s))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::DISTINCT, {s, zero}),
                     nm.mk_node(Kind::BV_ULE, {t, s})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF2>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  (void) s;
  // (=> (= x #b0000) (= t #b0000))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {x, zero}), nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF3>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (= s #b0000) (= t x))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, zero}), nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF4>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (= s x) (= t #b0000))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, x}), nm.mk_node(Kind::EQUAL, {t, zero})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF5>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (=> (bvult x s) (= t x))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::BV_ULT, {x, s}), nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF6>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  (void) x;
  // (bvuge (bvnot (bvneg s)) t)
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_NEG, {s})}), t});
}

template <>
Node
Lemma<LemmaKind::UREM_REF7>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (= x (bvand x (bvor s (bvor t (bvneg s)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::EQUAL,
      {x,
       nm.mk_node(
           Kind::BV_AND,
           {x,
            nm.mk_node(Kind::BV_OR,
                       {s,
                        nm.mk_node(Kind::BV_OR,
                                   {t, nm.mk_node(Kind::BV_NEG, {s})})})})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF8>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (not (bvult x (bvor t (bvand x s))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {x, nm.mk_node(Kind::BV_OR, {t, nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF9>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (not (= #b0001 (bvand t (bvnot (bvor x s)))))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {one,
       nm.mk_node(
           Kind::BV_AND,
           {t, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_OR, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF10>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (= t (bvor (bvnot x) (bvneg s))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::DISTINCT,
                    {t,
                     nm.mk_node(Kind::BV_OR,
                                {nm.mk_node(Kind::BV_NOT, {x}),
                                 nm.mk_node(Kind::BV_NEG, {s})})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF11>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvand t (bvor x s)) (bvand t #b0001)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_AND, {t, nm.mk_node(Kind::BV_OR, {x, s})}),
       nm.mk_node(Kind::BV_AND, {t, one})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF12>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  (void) s;
  // (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {x,
       nm.mk_node(
           Kind::BV_OR,
           {nm.mk_node(Kind::BV_NEG, {x}),
            nm.mk_node(Kind::BV_NEG, {nm.mk_node(Kind::BV_NOT, {t})})})});
}

template <>
Node
Lemma<LemmaKind::UREM_REF13>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvadd x (bvneg s)) t))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_ADD, {x, nm.mk_node(Kind::BV_NEG, {s})}), t});
}

template <>
Node
Lemma<LemmaKind::UREM_REF14>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (not (bvult (bvxor (bvneg s) (bvor x s)) t))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::BV_UGE,
                    {nm.mk_node(Kind::BV_XOR,
                                {nm.mk_node(Kind::BV_NEG, {s}),
                                 nm.mk_node(Kind::BV_OR, {x, s})}),
                     t});
}

template <>
Node
Lemma<LemmaKind::ADD_ZERO>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= s #b000) (= t x))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, zero}), nm.mk_node(Kind::EQUAL, {t, x})});
}

template <>
Node
Lemma<LemmaKind::ADD_SAME>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= x s) (= t[0] #b0))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(1));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {x, s}),
       nm.mk_node(Kind::EQUAL,
                  {nm.mk_node(Kind::BV_EXTRACT, {t}, {0, 0}), zero})});
}

template <>
Node
Lemma<LemmaKind::ADD_INV>::instance(const Node& x,
                                    const Node& s,
                                    const Node& t) const
{
  // (=> (= s (bvnot x)) (= t #b1111))
  NodeManager& nm = NodeManager::get();
  Node ones       = nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, nm.mk_node(Kind::BV_NOT, {x})}),
       nm.mk_node(Kind::EQUAL, {t, ones})});
}

template <>
Node
Lemma<LemmaKind::ADD_OVFL>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (and (= (msb x) #b1) (= (msb s) #b1)) (bvult t (bvand x s)))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(1));
  uint64_t msb    = x.type().bv_size() - 1;
  Node msb_x      = nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb});
  Node msb_s      = nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb});
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::AND,
                  {nm.mk_node(Kind::EQUAL, {msb_x, one}),
                   nm.mk_node(Kind::EQUAL, {msb_s, one})}),
       nm.mk_node(Kind::BV_ULT, {t, nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_NOOVFL>::instance(const Node& x,
                                       const Node& s,
                                       const Node& t) const
{
  // (=> (and (= (msb x) #b0) (= (msb s) #b0)) (bvuge t (bvor x s)))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(1));
  uint64_t msb    = x.type().bv_size() - 1;
  Node msb_x      = nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb});
  Node msb_s      = nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb});
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::AND,
                  {nm.mk_node(Kind::EQUAL, {msb_x, zero}),
                   nm.mk_node(Kind::EQUAL, {msb_s, zero})}),
       nm.mk_node(Kind::BV_UGE, {t, nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_OR>::instance(const Node& x,
                                   const Node& s,
                                   const Node& t) const
{
  // (=> (= (bvand x s) #b000) (= t (bvor x s)))
  NodeManager& nm = NodeManager::get();
  Node zero       = nm.mk_value(BitVector::mk_zero(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {nm.mk_node(Kind::BV_AND, {x, s}), zero}),
       nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF1>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= s x) (= ((_ extract 0 0) t) #b0))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::EQUAL, {s, x}),
                     nm.mk_node(Kind::EQUAL,
                                {nm.mk_node(Kind::BV_EXTRACT, {t}, {0, 0}),
                                 nm.mk_value(BitVector::mk_zero(1))})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF2>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= s (bvnot x)) (= t (bvnot #b0000)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, nm.mk_node(Kind::BV_NOT, {x})}),
       nm.mk_node(Kind::EQUAL,
                  {t, nm.mk_value(BitVector::mk_ones(x.type().bv_size()))})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF3>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=> (= (bvand x s) #b0000) (= t (bvor x s)))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL,
                  {nm.mk_node(Kind::BV_AND, {x, s}),
                   nm.mk_value(BitVector::mk_zero(x.type().bv_size()))}),
       nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF4>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=>
  //   (and
  //     (= ((_ extract msb msb) x) #b0) (= ((_ extract msb msb) s) #b0))
  //     (bvuge t (bvor x s)))
  NodeManager& nm = NodeManager::get();
  uint64_t msb    = x.type().bv_size() - 1;
  Node bvfalse    = nm.mk_value(BitVector::mk_false());
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::AND,
                  {nm.mk_node(Kind::EQUAL,
                              {nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb}),
                               bvfalse}),
                   nm.mk_node(Kind::EQUAL,
                              {nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb}),
                               bvfalse})}),
       nm.mk_node(Kind::BV_UGE, {t, nm.mk_node(Kind::BV_OR, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF5>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (=>
  //   (and (= ((_ extract msb msb) x) #b1) (= ((_ extract msb msb) s) #b1))
  //   (bvult t (bvand x s)))
  NodeManager& nm = NodeManager::get();
  uint64_t msb    = x.type().bv_size() - 1;
  Node bvtrue     = nm.mk_value(BitVector::mk_true());
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(
           Kind::AND,
           {nm.mk_node(Kind::EQUAL,
                       {nm.mk_node(Kind::BV_EXTRACT, {x}, {msb, msb}), bvtrue}),
            nm.mk_node(
                Kind::EQUAL,
                {nm.mk_node(Kind::BV_EXTRACT, {s}, {msb, msb}), bvtrue})}),
       nm.mk_node(Kind::BV_ULT, {t, nm.mk_node(Kind::BV_AND, {x, s})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF6>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (= #b0000 (bvand x (bvand s (bvand t #b0001))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::EQUAL,
      {nm.mk_value(BitVector::mk_zero(x.type().bv_size())),
       nm.mk_node(Kind::BV_AND,
                  {x,
                   nm.mk_node(Kind::BV_AND,
                              {s,
                               nm.mk_node(Kind::BV_AND,
                                          {t,
                                           nm.mk_value(BitVector::mk_one(
                                               x.type().bv_size()))})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF7>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor s t)) (bvand x #b0001))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_AND, {one, nm.mk_node(Kind::BV_OR, {s, t})}),
       nm.mk_node(Kind::BV_AND, {x, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF8>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor x t)) (bvand s #b0001))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_AND, {one, nm.mk_node(Kind::BV_OR, {x, t})}),
       nm.mk_node(Kind::BV_AND, {s, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF9>::instance(const Node& x,
                                     const Node& s,
                                     const Node& t) const
{
  // (bvuge (bvand #b0001 (bvor x s)) (bvand t #b0001))
  NodeManager& nm = NodeManager::get();
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::BV_UGE,
      {nm.mk_node(Kind::BV_AND, {one, nm.mk_node(Kind::BV_OR, {x, s})}),
       nm.mk_node(Kind::BV_AND, {t, one})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF10>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct #b0001 (bvor t (bvnot (bvand x s))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_value(BitVector::mk_one(x.type().bv_size())),
       nm.mk_node(
           Kind::BV_OR,
           {t, nm.mk_node(Kind::BV_NOT, {nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF11>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct t (bvnot (bvor t (bvand x s))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {t,
       nm.mk_node(
           Kind::BV_NOT,
           {nm.mk_node(Kind::BV_OR, {t, nm.mk_node(Kind::BV_AND, {x, s})})})});
}

template <>
Node
Lemma<LemmaKind::ADD_REF12>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  // (distinct #b0001 (bvor x (bvor s (bvnot t))))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_value(BitVector::mk_one(x.type().bv_size())),
       nm.mk_node(
           Kind::BV_OR,
           {x, nm.mk_node(Kind::BV_OR, {s, nm.mk_node(Kind::BV_NOT, {t})})})});
}
}  // namespace bzla::abstract
