#include "solver/bv/abstraction_lemmas.h"

#include "node/node_manager.h"

namespace bzla::bv::abstraction {

using namespace node;

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
    case LemmaKind::MUL_VALUE: os << "MUL_VALUE"; break;

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

    case LemmaKind::BITBLAST: os << "BITBLAST"; break;
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

// Unsigned division lemmas

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
  Node one        = nm.mk_value(BitVector::mk_one(x.type().bv_size()));
  return nm.mk_node(
      Kind::DISTINCT,
      {nm.mk_node(Kind::BV_OR, {s, one}),
       nm.mk_node(Kind::BV_AND, {x, nm.mk_node(Kind::BV_NOT, {t})})});
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
Lemma<LemmaKind::UREM_REF1>::instance(const Node& x,
                                      const Node& s,
                                      const Node& t) const
{
  //  UREM_REF1,   // (=> (distinct s #b0000) (bvule t s))
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
  //  UREM_REF2,   // (=> (= x #b0000) (= t #b0000))
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
  //  UREM_REF3,   // (=> (= s #b0000) (= t x))
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
  //  UREM_REF4,   // (=> (= s x) (= t #b0000))
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
  //  UREM_REF5,   // (=> (bvult x s) (= t x))
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
  //  UREM_REF6,   // (bvuge (bvnot (bvneg s)) t)
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
  //  UREM_REF7,   // (not (distinct x (bvand x (bvor s (bvor t (bvneg s))))))
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
  //  UREM_REF8,   // (not (bvult x (bvor t (bvand x s))))
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
  //  UREM_REF9,   // (not (= #b0001 (bvand t (bvnot (bvor x s)))))
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
  //  UREM_REF10,  // (not (= t (bvor (bvnot x) (bvneg s))))
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
  //  UREM_REF11,  // (not (bvult (bvand t (bvor x s)) (bvand t #b0001)))
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
  // UREM_REF12,  // (not (= x (bvor (bvneg x) (bvneg (bvnot t)))))
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
  // UREM_REF13,  // (not (bvult (bvadd x (bvneg s)) t))
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
  // UREM_REF14,  // (not (bvult (bvxor (bvneg s) (bvor x s)) t))
  NodeManager& nm = NodeManager::get();
  return nm.mk_node(Kind::BV_UGE,
                    {nm.mk_node(Kind::BV_XOR,
                                {nm.mk_node(Kind::BV_NEG, {s}),
                                 nm.mk_node(Kind::BV_OR, {x, s})}),
                     t});
}

}  // namespace bzla::bv::abstraction
