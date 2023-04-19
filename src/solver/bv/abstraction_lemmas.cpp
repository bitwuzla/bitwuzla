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

}  // namespace bzla::bv::abstraction
