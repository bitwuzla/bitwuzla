#include "solver/fp/symfpu_wrapper.h"

#include <sstream>

namespace bzla {
namespace fp {

/* --- SymFpuBV public ------------------------------------------------------ */

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const uint32_t bw, const uint32_t val)
{
  assert(bw);
  d_bv.reset(new BitVector(bw, val));
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

SymFpuSymProp::SymFpuSymProp(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
  d_node = bzla_node_copy(s_bzla, node);
}

SymFpuSymProp::SymFpuSymProp(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

SymFpuSymProp::SymFpuSymProp(const SymFpuSymProp &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

SymFpuSymProp::~SymFpuSymProp()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

SymFpuSymProp &
SymFpuSymProp::operator=(const SymFpuSymProp &other)
{
  assert(d_node);
  assert(other.d_node);
  assert(s_bzla == bzla_node_real_addr(d_node)->bzla);
  assert(s_bzla == bzla_node_real_addr(other.d_node)->bzla);
  BzlaNode *n = bzla_node_copy(s_bzla, other.d_node);
  bzla_node_release(s_bzla, d_node);
  d_node = n;
  return *this;
}

SymFpuSymProp
SymFpuSymProp::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_bv_not(s_bzla, d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

SymFpuSymProp
SymFpuSymProp::operator&&(const SymFpuSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

SymFpuSymProp
SymFpuSymProp::operator||(const SymFpuSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

SymFpuSymProp
SymFpuSymProp::operator==(const SymFpuSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

SymFpuSymProp
SymFpuSymProp::operator^(const SymFpuSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

bool
SymFpuSymProp::check_node(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node))
         && bzla_node_bv_get_width(s_bzla, node) == 1;
}

/* --- SymFpuSymBV public --------------------------------------------------- */

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
  d_node = bzla_node_copy(s_bzla, node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const uint32_t w, const uint32_t val)
{
  assert(s_bzla);
  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  d_node       = is_signed ? bzla_exp_bv_int(s_bzla, val, s)
                           : bzla_exp_bv_unsigned(s_bzla, val, s);
  bzla_sort_release(s_bzla, s);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymProp &p)
{
  assert(s_bzla);
  assert(p.d_node);
  assert(bzla_sort_bv_get_width(s_bzla, bzla_node_get_sort_id(p.d_node)));
  d_node = bzla_node_copy(s_bzla, p.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<!is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const BitVector &bv)
{
  assert(s_bzla);
  BzlaBitVector *bbv = bzla_bv_new(s_bzla->mm, bv.size());
  bbv->d_bv.reset(new bzla::BitVector(bv));
  d_node = bzla_exp_bv_const(s_bzla, bbv);
  bzla_bv_free(s_bzla->mm, bbv);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuBV<is_signed> &bv)
{
  assert(s_bzla);
  assert(bv.d_bv);
  BzlaBitVector *bbv = bzla_bv_new(s_bzla->mm, bv.d_bv->size());
  bbv->d_bv.reset(new bzla::BitVector(*bv.d_bv));
  d_node = bzla_exp_bv_const(s_bzla, bbv);
  bzla_bv_free(s_bzla->mm, bbv);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::~SymFpuSymBV()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed> &
SymFpuSymBV<is_signed>::operator=(const SymFpuSymBV<is_signed> &other)
{
  assert(d_node);
  assert(other.d_node);
  assert(s_bzla == bzla_node_real_addr(d_node)->bzla);
  assert(s_bzla == bzla_node_real_addr(other.d_node)->bzla);
  BzlaNode *n = bzla_node_copy(s_bzla, other.d_node);
  bzla_node_release(s_bzla, d_node);
  d_node = n;
  return *this;
}

template <bool is_signed>
uint32_t
SymFpuSymBV<is_signed>::getWidth(void) const
{
  assert(s_bzla);
  return bzla_node_bv_get_width(s_bzla, d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::one(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_one(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::zero(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_zero(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::allOnes(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_ones(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
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
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_max_signed(s_bzla, s)
                           : bzla_exp_bv_ones(s_bzla, s);

  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::minValue(const uint32_t &w)
{
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_min_signed(s_bzla, s)
                           : bzla_exp_bv_zero(s_bzla, s);

  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator<<(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sll(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator>>(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sra(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_srl(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator|(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator&(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator+(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_add(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sub(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator*(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_mul(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator/(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sdiv(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_udiv(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator%(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_srem(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_urem(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_neg(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator~(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_not(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::increment() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_inc(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::decrement() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_dec(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::signExtendRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sra(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularLeftShift(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this << op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this >> op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularIncrement() const
{
  assert(s_bzla);
  return increment();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  return decrement();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularAdd(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this + op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularNegate() const
{
  assert(s_bzla);
  return -(*this);
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_bv_not(s_bzla, d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator||(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(checkBooleanNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator^(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator==(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<=(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_slte(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ulte(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>=(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgte(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ugte(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_slt(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ult(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgt(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ugt(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
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
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sext(s_bzla, d_node, extension)
                          : bzla_exp_bv_uext(s_bzla, d_node, extension);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::contract(uint32_t reduction) const
{
  assert(s_bzla);
  assert(getWidth() > reduction);
  BzlaNode *n =
      bzla_exp_bv_slice(s_bzla, d_node, getWidth() - 1 - reduction, 0);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
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
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_concat(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(s_bzla);
  assert(upper >= lower);
  BzlaNode *n                = bzla_exp_bv_slice(s_bzla, d_node, upper, lower);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::check_node(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node));
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::checkBooleanNode(const BzlaNode *node) const
{
  assert(check_node(node));
  return bzla_node_bv_get_width(s_bzla, node) == 1;
}

template class SymFpuSymBV<true>;
template class SymFpuSymBV<false>;

/* --- SymFpuSymRM public --------------------------------------------------- */

BzlaNode *
SymFpuSymRM::init_const(const RoundingMode rm)
{
  assert(s_bzla);
  assert(rm != RoundingMode::NUM_RM);
  BzlaMemMgr *mm    = s_bzla->mm;
  BitVector rmbv       = BitVector(BZLA_RM_BW, static_cast<uint64_t>(rm));
  BzlaBitVector *brmbv = bzla_bv_new(s_bzla->mm, rmbv.size());
  brmbv->d_bv.reset(new bzla::BitVector(rmbv));
  BzlaNode *res = bzla_exp_bv_const(s_bzla, brmbv);
  bzla_bv_free(mm, brmbv);
  return res;
}

SymFpuSymRM::SymFpuSymRM(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
  if (bzla_node_is_bv(s_bzla, node))
  {
    d_node = bzla_node_copy(s_bzla, node);
  }
  else if (bzla_node_is_rm_const(node))
  {
    BzlaRoundingMode brm = bzla_node_rm_const_get_rm(node);
    RoundingMode rm;
    if (brm == BZLA_RM_RNA)
    {
      rm = bzla::fp::RoundingMode::RNA;
    }
    else if (brm == BZLA_RM_RNE)
    {
      rm = bzla::fp::RoundingMode::RNE;
    }
    else if (brm == BZLA_RM_RTN)
    {
      rm = bzla::fp::RoundingMode::RTN;
    }
    else if (brm == BZLA_RM_RTP)
    {
      rm = bzla::fp::RoundingMode::RTP;
    }
    else
    {
      assert(brm == BZLA_RM_RTZ);
      rm = bzla::fp::RoundingMode::RTZ;
    }
    d_node = init_const(rm);
  }
  else
  {
    assert(bzla_node_is_rm(s_bzla, node));
    BzlaSortId sort = bzla_sort_bv(s_bzla, BZLA_RM_BW);
    std::stringstream ss;
    ss << "_rm_var_" << bzla_node_get_id(node) << "_";
    d_node = bzla_exp_var(s_bzla, sort, ss.str().c_str());
    bzla_sort_release(s_bzla, sort);
  }
}

SymFpuSymRM::SymFpuSymRM(const RoundingMode rm)
{
  assert(s_bzla);
  d_node = init_const(rm);
  assert(check_node(d_node));
}

SymFpuSymRM::SymFpuSymRM(const SymFpuSymRM &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

SymFpuSymRM::~SymFpuSymRM()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

SymFpuSymProp
SymFpuSymRM::valid(void) const
{
  assert(d_node);
  BzlaNode *max =
      bzla_exp_bv_unsigned(s_bzla, BZLA_RM_MAX, bzla_node_get_sort_id(d_node));
  BzlaNode *valid = bzla_exp_bv_ult(s_bzla, d_node, max);
  SymFpuSymProp res(valid);
  bzla_node_release(s_bzla, max);
  bzla_node_release(s_bzla, valid);
  return res;
}

SymFpuSymProp
SymFpuSymRM::operator==(const SymFpuSymRM &other) const
{
  assert(d_node);
  assert(other.d_node);
  BzlaNode *eq = bzla_exp_eq(s_bzla, d_node, other.d_node);
  SymFpuSymProp res(eq);
  bzla_node_release(s_bzla, eq);
  return res;
}

bool
SymFpuSymRM::check_node(const BzlaNode *node) const
{
  assert(s_bzla);
  assert(node);
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  assert((((uint32_t) 1u) << BZLA_RM_BW) >= SYMFPU_NUMBER_OF_ROUNDING_MODES);
  return (bzla_node_is_bv(s_bzla, node)
          && bzla_node_bv_get_width(s_bzla, node) == BZLA_RM_BW)
         || bzla_node_is_rm(s_bzla, node);
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
