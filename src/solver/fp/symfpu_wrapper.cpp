/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/symfpu_wrapper.h"

#include <sstream>

#include "node/node_manager.h"
#include "node/node_utils.h"

namespace bzla {
namespace fp {

using namespace node;

/* --- SymFpuBV public ------------------------------------------------------ */

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const uint32_t bw, const uint32_t val)
{
  assert(bw);
  d_bv.reset(new BitVector(BitVector::from_ui(bw, static_cast<uint64_t>(val))));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const bool &val)
{
  d_bv.reset(new BitVector(val ? BitVector::mk_true() : BitVector::mk_false()));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const SymFpuBV<is_signed> &other)
{
  assert(other.d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const SymFpuBV<!is_signed> &other)
{
  assert(other.d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const BitVector &bv)
{
  assert(!bv.is_null());
  d_bv.reset(new BitVector(bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::~SymFpuBV()
{
}

template <bool is_signed>
uint32_t
SymFpuBV<is_signed>::getWidth(void) const
{
  assert(d_bv);
  return d_bv->size();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::one(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_one(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::zero(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_zero(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::allOnes(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_ones(bw);
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::isAllOnes() const
{
  assert(d_bv);
  return d_bv->is_ones();
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::isAllZeros() const
{
  assert(d_bv);
  return d_bv->is_zero();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::maxValue(const uint32_t &bw)
{
  assert(bw);
  return is_signed ? BitVector::mk_max_signed(bw) : BitVector::mk_ones(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::minValue(const uint32_t &bw)
{
  assert(bw);
  return is_signed ? BitVector::mk_min_signed(bw) : BitVector::mk_zero(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator=(const SymFpuBV<is_signed> &other)
{
  assert(d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
  return *this;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator<<(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvshl(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator>>(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvashr(*op.d_bv) : d_bv->bvshr(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator|(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvor(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator&(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvand(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator+(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvadd(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator-(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvsub(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator*(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvmul(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator/(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvsdiv(*op.d_bv) : d_bv->bvudiv(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator%(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvsrem(*op.d_bv) : d_bv->bvurem(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator-(void) const
{
  assert(d_bv);
  return d_bv->bvneg();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator~(void) const
{
  assert(d_bv);
  return d_bv->bvnot();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::increment() const
{
  assert(d_bv);
  return d_bv->bvinc();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::decrement() const
{
  assert(d_bv);
  return d_bv->bvdec();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::signExtendRightShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  uint32_t bw   = d_bv->size();
  uint32_t bwop = op.d_bv->size();
  assert(bwop <= bw);
  return d_bv->bvashr(op.d_bv->bvsext(bw - bwop));
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularLeftShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this << op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularRightShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this >> op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularIncrement() const
{
  assert(d_bv);
  return increment();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularDecrement() const
{
  assert(d_bv);
  return decrement();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularAdd(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this + op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularNegate() const
{
  assert(d_bv);
  return -(*this);
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator==(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bveq(*op.d_bv).is_true();
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator<=(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) <= 0
                   : d_bv->compare(*op.d_bv) <= 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator>=(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) >= 0
                   : d_bv->compare(*op.d_bv) >= 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator<(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) < 0
                   : d_bv->compare(*op.d_bv) < 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator>(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) > 0
                   : d_bv->compare(*op.d_bv) > 0;
}

template <bool is_signed>
SymFpuBV<true>
SymFpuBV<is_signed>::toSigned(void) const
{
  assert(d_bv);
  return SymFpuBV<true>(*this);
}

template <bool is_signed>
SymFpuBV<false>
SymFpuBV<is_signed>::toUnsigned(void) const
{
  assert(d_bv);
  return SymFpuBV<false>(*this);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::extend(uint32_t extension) const
{
  assert(d_bv);
  return is_signed ? d_bv->bvsext(extension) : d_bv->bvzext(extension);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::contract(uint32_t reduction) const
{
  assert(d_bv);
  uint32_t bw = getWidth();
  assert(bw - 1 - reduction < bw);
  return d_bv->bvextract(bw - 1 - reduction, 0);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::resize(uint32_t newSize) const
{
  assert(d_bv);
  uint32_t bw = getWidth();
  if (newSize > bw)
  {
    return extend(newSize - bw);
  }
  if (newSize < bw)
  {
    return contract(bw - newSize);
  }
  return *this;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::matchWidth(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  uint32_t bw = getWidth();
  assert(bw <= op.getWidth());
  return extend(op.getWidth() - bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::append(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvconcat(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(d_bv);
  assert(upper >= lower);
  return d_bv->bvextract(upper, lower);
}

template class SymFpuBV<true>;
template class SymFpuBV<false>;

/* --- SymFpuTraits public -------------------------------------------------- */

RoundingMode
SymFpuTraits::RNE(void)
{
  return RoundingMode::RNE;
}

RoundingMode
SymFpuTraits::RNA(void)
{
  return RoundingMode::RNA;
}

RoundingMode
SymFpuTraits::RTP(void)
{
  return RoundingMode::RTP;
}

RoundingMode
SymFpuTraits::RTN(void)
{
  return RoundingMode::RTN;
}

RoundingMode
SymFpuTraits::RTZ(void)
{
  return RoundingMode::RTZ;
}

void
SymFpuTraits::precondition(const bool &p)
{
  assert(p);
  (void) p;
}

void
SymFpuTraits::postcondition(const bool &p)
{
  assert(p);
  (void) p;
}

void
SymFpuTraits::invariant(const bool &p)
{
  assert(p);
  (void) p;
}

/* --- SymFpuSymProp -------------------------------------------------------- */

SymFpuSymProp::SymFpuSymProp(const Node &node)
{
  if (node.type().is_bool())
  {
    NodeManager &nm = NodeManager::get();
    d_node          = nm.mk_node(Kind::ITE,
                        {node,
                                  nm.mk_value(BitVector::mk_true()),
                                  nm.mk_value(BitVector::mk_false())});
  }
  else
  {
    d_node = node;
  }
  assert(check_node(d_node));
}

SymFpuSymProp::SymFpuSymProp(bool v)
    : d_node(NodeManager::get().mk_value(v ? BitVector::mk_true()
                                           : BitVector::mk_false()))
{
}

SymFpuSymProp::SymFpuSymProp(const SymFpuSymProp &other) : d_node(other.d_node)
{
  assert(check_node(other.d_node));
}

SymFpuSymProp::~SymFpuSymProp() {}

SymFpuSymProp &
SymFpuSymProp::operator=(const SymFpuSymProp &other)
{
  assert(!d_node.is_null());
  assert(!other.d_node.is_null());
  d_node = other.d_node;
  return *this;
}

SymFpuSymProp
SymFpuSymProp::operator!(void) const
{
  return NodeManager::get().mk_node(Kind::BV_NOT, {d_node});
}

SymFpuSymProp
SymFpuSymProp::operator&&(const SymFpuSymProp &op) const
{
  assert(check_node(op.d_node));
  return NodeManager::get().mk_node(Kind::BV_AND, {d_node, op.d_node});
}

SymFpuSymProp
SymFpuSymProp::operator||(const SymFpuSymProp &op) const
{
  assert(check_node(op.d_node));
  return NodeManager::get().mk_node(Kind::BV_OR, {d_node, op.d_node});
}

SymFpuSymProp
SymFpuSymProp::operator==(const SymFpuSymProp &op) const
{
  assert(check_node(op.d_node));
  return NodeManager::get().mk_node(Kind::BV_COMP, {d_node, op.d_node});
}

SymFpuSymProp
SymFpuSymProp::operator^(const SymFpuSymProp &op) const
{
  assert(check_node(op.d_node));
  return NodeManager::get().mk_node(Kind::BV_XOR, {d_node, op.d_node});
}

bool
SymFpuSymProp::check_node(const Node &node) const
{
  assert(!node.is_null());
  return node.type().is_bv() && node.type().bv_size() == 1;
}

/* --- SymFpuSymBV public --------------------------------------------------- */

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const Node &node) : d_node(node)
{
  assert(check_node(node));
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(bool v)
    : d_node(NodeManager::get().mk_value(v ? BitVector::mk_true()
                                           : BitVector::mk_false()))
{
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const uint32_t w, const uint32_t val)
    : d_node(NodeManager::get().mk_value(
        is_signed ? BitVector::from_si(w, val) : BitVector::from_ui(w, val)))
{
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymProp &p)
{
  assert(!p.d_node.is_null());
  d_node = p.d_node;
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<is_signed> &other)
    : d_node(other.d_node)
{
  assert(check_node(other.d_node));
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<!is_signed> &other)
    : d_node(other.d_node)
{
  assert(check_node(other.d_node));
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const BitVector &bv)
    : d_node(NodeManager::get().mk_value(bv))
{
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuBV<is_signed> &bv)
    : d_node(NodeManager::get().mk_value(*bv.d_bv))
{
  assert(bv.d_bv);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::~SymFpuSymBV()
{
}

template <bool is_signed>
SymFpuSymBV<is_signed> &
SymFpuSymBV<is_signed>::operator=(const SymFpuSymBV<is_signed> &other)
{
  assert(!d_node.is_null());
  assert(!other.d_node.is_null());
  d_node = other.d_node;
  return *this;
}

template <bool is_signed>
uint32_t
SymFpuSymBV<is_signed>::getWidth(void) const
{
  return d_node.type().bv_size();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::one(const uint32_t &w)
{
  return NodeManager::get().mk_value(BitVector::mk_one(w));
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::zero(const uint32_t &w)
{
  return NodeManager::get().mk_value(BitVector::mk_zero(w));
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::allOnes(const uint32_t &w)
{
  return NodeManager::get().mk_value(BitVector::mk_ones(w));
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::isAllOnes() const
{
  return *this == SymFpuSymBV<is_signed>::allOnes(getWidth());
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::isAllZeros() const
{
  return *this == SymFpuSymBV<is_signed>::zero(getWidth());
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::maxValue(const uint32_t &w)
{
  return NodeManager::get().mk_value(BitVector::mk_max_signed(w));
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::minValue(const uint32_t &w)
{
  return NodeManager::get().mk_value(BitVector::mk_min_signed(w));
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator<<(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_SHL, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator>>(const SymFpuSymBV<is_signed> &op) const
{
  return is_signed
             ? NodeManager::get().mk_node(Kind::BV_ASHR, {d_node, op.d_node})
             : NodeManager::get().mk_node(Kind::BV_SHR, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator|(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_OR, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator&(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_AND, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator+(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_ADD, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_SUB, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator*(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_MUL, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator/(const SymFpuSymBV<is_signed> &op) const
{
  return is_signed
             ? NodeManager::get().mk_node(Kind::BV_SDIV, {d_node, op.d_node})
             : NodeManager::get().mk_node(Kind::BV_UDIV, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator%(const SymFpuSymBV<is_signed> &op) const
{
  return is_signed
             ? NodeManager::get().mk_node(Kind::BV_SREM, {d_node, op.d_node})
             : NodeManager::get().mk_node(Kind::BV_UREM, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(void) const
{
  return NodeManager::get().mk_node(Kind::BV_NEG, {d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator~(void) const
{
  return NodeManager::get().mk_node(Kind::BV_NOT, {d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::increment() const
{
  NodeManager &nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_ADD,
      {d_node, nm.mk_value(BitVector::mk_one(d_node.type().bv_size()))});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::decrement() const
{
  NodeManager &nm = NodeManager::get();
  return nm.mk_node(
      Kind::BV_SUB,
      {d_node, nm.mk_value(BitVector::mk_one(d_node.type().bv_size()))});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::signExtendRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_ASHR, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularLeftShift(const SymFpuSymBV<is_signed> &op) const
{
  return *this << op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  return *this >> op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularIncrement() const
{
  return increment();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularDecrement() const
{
  return decrement();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularAdd(const SymFpuSymBV<is_signed> &op) const
{
  return *this + op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularNegate() const
{
  return -(*this);
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator!(void) const
{
  return NodeManager::get().mk_node(Kind::BV_NOT, {d_node});
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator||(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_OR, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator^(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_XOR, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator==(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_COMP, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<=(const SymFpuSymBV<is_signed> &op) const
{
  NodeManager &nm = NodeManager::get();
  return node::utils::bool_to_bv1(
      is_signed ? nm.mk_node(Kind::BV_SLE, {d_node, op.d_node})
                : nm.mk_node(Kind::BV_ULE, {d_node, op.d_node}));
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>=(const SymFpuSymBV<is_signed> &op) const
{
  NodeManager &nm = NodeManager::get();
  return node::utils::bool_to_bv1(
      is_signed ? nm.mk_node(Kind::BV_SGE, {d_node, op.d_node})
                : nm.mk_node(Kind::BV_UGE, {d_node, op.d_node}));
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<(const SymFpuSymBV<is_signed> &op) const
{
  NodeManager &nm = NodeManager::get();
  return node::utils::bool_to_bv1(
      is_signed ? nm.mk_node(Kind::BV_SLT, {d_node, op.d_node})
                : nm.mk_node(Kind::BV_ULT, {d_node, op.d_node}));
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>(const SymFpuSymBV<is_signed> &op) const
{
  NodeManager &nm = NodeManager::get();
  return node::utils::bool_to_bv1(
      is_signed ? nm.mk_node(Kind::BV_SGT, {d_node, op.d_node})
                : nm.mk_node(Kind::BV_UGT, {d_node, op.d_node}));
}

template <bool is_signed>
SymFpuSymBV<true>
SymFpuSymBV<is_signed>::toSigned(void) const
{
  return SymFpuSymBV<true>(*this);
}

template <bool is_signed>
SymFpuSymBV<false>
SymFpuSymBV<is_signed>::toUnsigned(void) const
{
  return SymFpuSymBV<false>(*this);
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::extend(uint32_t extension) const
{
  return is_signed ? NodeManager::get().mk_node(
             Kind::BV_SIGN_EXTEND, {d_node}, {extension})
                   : NodeManager::get().mk_node(
                       Kind::BV_ZERO_EXTEND, {d_node}, {extension});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::contract(uint32_t reduction) const
{
  return NodeManager::get().mk_node(
      Kind::BV_EXTRACT, {d_node}, {getWidth() - 1 - reduction, 0});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::resize(uint32_t newSize) const
{
  uint32_t bw = getWidth();
  if (newSize > bw) return extend(newSize - bw);
  if (newSize < bw) return contract(bw - newSize);
  return *this;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::matchWidth(const SymFpuSymBV<is_signed> &op) const
{
  assert(getWidth() <= op.getWidth());
  return extend(op.getWidth() - getWidth());
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::append(const SymFpuSymBV<is_signed> &op) const
{
  return NodeManager::get().mk_node(Kind::BV_CONCAT, {d_node, op.d_node});
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  return NodeManager::get().mk_node(Kind::BV_EXTRACT, {d_node}, {upper, lower});
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::check_node(const Node &node) const
{
  assert(!node.is_null());
  return node.type().is_bv();
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::check_bool_node(const Node &node) const
{
  return node.type().is_bool();
}

template class SymFpuSymBV<true>;
template class SymFpuSymBV<false>;

/* --- SymFpuSymRM public --------------------------------------------------- */

Node
SymFpuSymRM::mk_value(const RoundingMode rm)
{
  assert(rm != RoundingMode::NUM_RM);
  return NodeManager::get().mk_value(
      BitVector::from_ui(BZLA_RM_BV_SIZE, static_cast<uint64_t>(rm)));
}

SymFpuSymRM::SymFpuSymRM(const Node &node)
{
  assert(check_node(node));
  const Type &type = node.type();
  if (type.is_bv())
  {
    d_node = node;
  }
  else
  {
    assert(type.is_rm());
    if (node.is_value())
    {
      d_node = mk_value(node.value<RoundingMode>());
    }
    else
    {
      NodeManager &nm = NodeManager::get();
      d_node          = nm.mk_const(nm.mk_bv_type(BZLA_RM_BV_SIZE),
                           "_rm_var_" + std::to_string(node.id()) + "_");
    }
  }
}

SymFpuSymRM::SymFpuSymRM(const RoundingMode rm) : d_node(mk_value(rm))
{
  assert(check_node(d_node));
}

SymFpuSymRM::SymFpuSymRM(const SymFpuSymRM &other) : d_node(other.d_node)
{
  assert(check_node(other.d_node));
}

SymFpuSymRM::~SymFpuSymRM() {}

SymFpuSymProp
SymFpuSymRM::valid(void) const
{
  assert(!d_node.is_null());
  NodeManager &nm = NodeManager::get();
  uint64_t size   = d_node.type().bv_size();
  return node::utils::bool_to_bv1(
      nm.mk_node(Kind::BV_ULT,
                 {d_node, nm.mk_value(BitVector::from_ui(size, static_cast<uint64_t>(RoundingMode::NUM_RM)))}));
}

SymFpuSymProp
SymFpuSymRM::operator==(const SymFpuSymRM &other) const
{
  assert(!d_node.is_null());
  assert(!other.d_node.is_null());
  return NodeManager::get().mk_node(Kind::BV_COMP, {d_node, other.d_node});
}

bool
SymFpuSymRM::check_node(const Node &node) const
{
  assert(!node.is_null());
  assert((((uint32_t) 1u) << BZLA_RM_BV_SIZE)
         >= SYMFPU_NUMBER_OF_ROUNDING_MODES);
  return (node.type().is_bv() && node.type().bv_size() == BZLA_RM_BV_SIZE)
         || node.type().is_rm();
}

/* --- SymFpuSymTraits public ----------------------------------------------- */

SymFpuSymRM
SymFpuSymTraits::RNE(void)
{
  return RoundingMode::RNE;
}

SymFpuSymRM
SymFpuSymTraits::RNA(void)
{
  return RoundingMode::RNA;
}

SymFpuSymRM
SymFpuSymTraits::RTP(void)
{
  return RoundingMode::RTP;
}

SymFpuSymRM
SymFpuSymTraits::RTN(void)
{
  return RoundingMode::RTN;
}

SymFpuSymRM
SymFpuSymTraits::RTZ(void)
{
  return RoundingMode::RTZ;
}

void
SymFpuSymTraits::precondition(const bool b)
{
  assert(b);
  (void) b;
}

void
SymFpuSymTraits::postcondition(const bool b)
{
  assert(b);
  (void) b;
}

void
SymFpuSymTraits::invariant(const bool b)
{
  assert(b);
  (void) b;
}

void
SymFpuSymTraits::precondition(const prop &p)
{
  (void) p;
}

void
SymFpuSymTraits::postcondition(const prop &p)
{
  (void) p;
}

void
SymFpuSymTraits::invariant(const prop &p)
{
  (void) p;
}

}  // namespace fp
}  // namespace bzla
