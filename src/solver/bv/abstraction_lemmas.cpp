#include "solver/bv/abstraction_lemmas.h"

#include "node/node_manager.h"

namespace bzla::bv {

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
    case LemmaKind::MUL_VALUE: os << "MUL_VALUE"; break;
  }
  return os;
}

/* --- Abstraction Lemmas --------------------------------------------------- */

AbstractionLemma::AbstractionLemma(SolverState& state, LemmaKind kind)
    : d_solver_state(state), d_kind(kind)
{
}

LemmaMulZero::LemmaMulZero(SolverState& state)
    : AbstractionLemma(state, LemmaKind::MUL_ZERO)
{
}

bool
LemmaMulZero::check(const Node& x, const Node& s, const Node& t) const
{
  assert(x.is_value());
  assert(s.is_value());
  assert(t.is_value());
  (void) x;
  return s.value<BitVector>().is_zero() && s != t;
}

Node
LemmaMulZero::instance(const Node& x, const Node& s, const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  size_t size     = x.type().bv_size();
  Node zero       = nm.mk_value(BitVector::mk_zero(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, zero}), nm.mk_node(Kind::EQUAL, {t, zero})});
}

LemmaMulOne::LemmaMulOne(SolverState& state)
    : AbstractionLemma(state, LemmaKind::MUL_ONE)
{
}

bool
LemmaMulOne::check(const Node& x, const Node& s, const Node& t) const
{
  assert(x.is_value());
  assert(s.is_value());
  assert(t.is_value());
  return s.value<BitVector>().is_one() && t != x;
}

Node
LemmaMulOne::instance(const Node& x, const Node& s, const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  size_t size     = x.type().bv_size();
  Node one        = nm.mk_value(BitVector::mk_one(size));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, one}), nm.mk_node(Kind::EQUAL, {t, x})});
}

LemmaMulIc::LemmaMulIc(SolverState& state)
    : AbstractionLemma(state, LemmaKind::MUL_IC)
{
}

bool
LemmaMulIc::check(const Node& x, const Node& s, const Node& t) const
{
  assert(x.is_value());
  assert(s.is_value());
  assert(t.is_value());
  (void) x;
  const BitVector& bv_s = s.value<BitVector>();
  const BitVector& bv_t = t.value<BitVector>();
  BitVector lhs         = bv_s.bvneg().ibvor(bv_s).ibvand(bv_t);
  return lhs != bv_t;
}

Node
LemmaMulIc::instance(const Node& x, const Node& s, const Node& t) const
{
  (void) x;
  NodeManager& nm = NodeManager::get();
  Node lhs        = nm.mk_node(
      Kind::BV_AND,
      {nm.mk_node(Kind::BV_OR, {nm.mk_node(Kind::BV_NEG, {s}), s}), t});
  return nm.mk_node(Kind::EQUAL, {lhs, t});
}

LemmaMulNeg::LemmaMulNeg(SolverState& state)
    : AbstractionLemma(state, LemmaKind::MUL_NEG)
{
}

bool
LemmaMulNeg::check(const Node& x, const Node& s, const Node& t) const
{
  assert(x.is_value());
  assert(s.is_value());
  assert(t.is_value());
  const BitVector& bv_x = x.value<BitVector>();
  const BitVector& bv_s = s.value<BitVector>();
  const BitVector& bv_t = t.value<BitVector>();
  return bv_s.is_ones() && bv_t.bvneg() != bv_x;
}

Node
LemmaMulNeg::instance(const Node& x, const Node& s, const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node ones       = nm.mk_value(BitVector::mk_ones(x.type().bv_size()));
  return nm.mk_node(
      Kind::IMPLIES,
      {nm.mk_node(Kind::EQUAL, {s, ones}),
       nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_NEG, {x})})});
}

LemmaMulValue::LemmaMulValue(SolverState& state)
    : AbstractionLemma(state, LemmaKind::MUL_VALUE)
{
}

bool
LemmaMulValue::check(const Node& x, const Node& s, const Node& t) const
{
  assert(x.is_value());
  assert(s.is_value());
  assert(t.is_value());
  const BitVector& val_x = x.value<BitVector>();
  const BitVector& val_s = s.value<BitVector>();
  const BitVector& val_t = t.value<BitVector>();
  return val_x.bvmul(val_s) != val_t;
}

Node
LemmaMulValue::instance(const Node& x, const Node& s, const Node& t) const
{
  NodeManager& nm = NodeManager::get();
  Node val_x      = d_solver_state.value(x);
  Node val_s      = d_solver_state.value(s);
  Node val_t =
      nm.mk_value(val_x.value<BitVector>().bvmul(val_s.value<BitVector>()));
  return nm.mk_node(Kind::IMPLIES,
                    {nm.mk_node(Kind::AND,
                                {
                                    nm.mk_node(Kind::EQUAL, {x, val_x}),
                                    nm.mk_node(Kind::EQUAL, {s, val_s}),
                                }),
                     nm.mk_node(Kind::EQUAL, {t, val_t})});
}

}  // namespace bzla::bv
