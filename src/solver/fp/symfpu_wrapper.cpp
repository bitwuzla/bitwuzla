#include "solver/fp/symfpu_wrapper.h"

#include <sstream>

namespace bzla {
namespace fp {

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

/* --- BzlaSymRM public ----------------------------------------------------- */

BzlaNode *
SymFpuSymRM::init_const(const uint32_t val)
{
  assert(s_bzla);
  assert(bzla_rm_is_valid(val));
  BzlaMemMgr *mm    = s_bzla->mm;
  BzlaBitVector *rm = bzla_bv_uint64_to_bv(mm, val, BZLA_RM_BW);
  BzlaNode *res     = bzla_exp_bv_const(s_bzla, rm);
  bzla_bv_free(mm, rm);
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
    d_node = init_const(bzla_node_rm_const_get_rm(node));
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

SymFpuSymRM::SymFpuSymRM(const uint32_t val)
{
  assert(s_bzla);
  d_node = init_const(val);
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
  return BZLA_RM_RNE;
}

SymFpuSymRM
SymFpuSymTraits::RNA(void)
{
  return BZLA_RM_RNA;
}

SymFpuSymRM
SymFpuSymTraits::RTP(void)
{
  return BZLA_RM_RTP;
}

SymFpuSymRM
SymFpuSymTraits::RTN(void)
{
  return BZLA_RM_RTN;
}

SymFpuSymRM
SymFpuSymTraits::RTZ(void)
{
  return BZLA_RM_RTZ;
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
