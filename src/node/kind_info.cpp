/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/kind_info.h"

namespace bzla::node {

/* --- KindInfo public ------------------------------------------------------ */

uint32_t
KindInfo::num_children(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_num_children;
}

uint32_t
KindInfo::num_indices(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_num_indices;
}

const char*
KindInfo::enum_name(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_enum_name;
}

const char*
KindInfo::smt2_name(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_smt2_name;
}

bool
KindInfo::is_nary(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_num_children
         == KindInfo::s_nary;
}

bool
KindInfo::is_left_associative(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::LEFT_ASSOC;
}

bool
KindInfo::is_right_associative(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::RIGHT_ASSOC;
}

bool
KindInfo::is_commutative(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].is_commutative;
}

bool
KindInfo::is_chainable(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::CHAINABLE;
}

bool
KindInfo::is_pairwise(Kind kind)
{
  return get().d_info[static_cast<size_t>(kind)].d_attribute
         == KindAttribute::PAIRWISE;
}

bool
KindInfo::is_bool(Kind kind)
{
  return Kind::AND <= kind && kind <= Kind::XOR;
}

bool
KindInfo::is_bv(Kind kind)
{
  return Kind::BV_ADD <= kind && kind <= Kind::BV_ZERO_EXTEND;
}

bool
KindInfo::is_fp(Kind kind)
{
  return Kind::FP_ABS <= kind && kind <= Kind::FP_TO_UBV;
}

bool
KindInfo::is_array(Kind kind)
{
  return Kind::CONST_ARRAY <= kind && kind <= Kind::STORE;
}

bool
KindInfo::is_fun(Kind kind)
{
  return kind == Kind::APPLY || kind == Kind::LAMBDA;
}

bool
KindInfo::is_quant(Kind kind)
{
  return kind == Kind::EXISTS || kind == Kind::FORALL;
}

constexpr void
KindInfo::init(Kind kind,
               uint8_t num_children,
               uint8_t num_indices,
               const char* enum_name,
               const char* smt2_name,
               KindAttribute attribute,
               bool is_commutative)
{
  ++d_num_inited;
  d_info[static_cast<size_t>(kind)] = {num_children,
                                       num_indices,
                                       enum_name,
                                       smt2_name,
                                       attribute,
                                       is_commutative};
}

constexpr KindInfo::KindInfo()
{
  init(Kind::NULL_NODE, 0, 0, "NULL_NODE");

  init(Kind::CONSTANT, 0, 0, "CONSTANT");
  init(Kind::VALUE, 0, 0, "VALUE", "");
  init(Kind::VARIABLE, 0, 0, "VARIABLE");
  init(Kind::DISTINCT,
       KindInfo::s_nary,
       0,
       "DISTINCT",
       "distinct",
       KindInfo::PAIRWISE);
  init(Kind::EQUAL, 2, 0, "EQUAL", "=", KindInfo::CHAINABLE, true);
  init(Kind::ITE, 3, 0, "ITE", "ite");

  /* Boolean */
  init(Kind::AND, 2, 0, "AND", "and", KindInfo::LEFT_ASSOC, true);
  init(Kind::IMPLIES, 2, 0, "IMPLIES", "=>", KindInfo::RIGHT_ASSOC);
  init(Kind::NOT, 1, 0, "NOT", "not");
  init(Kind::OR, 2, 0, "OR", "or", KindInfo::LEFT_ASSOC, true);
  init(Kind::XOR, 2, 0, "XOR", "xor", KindInfo::LEFT_ASSOC, true);

  /* Bit-vectors */
  init(Kind::BV_ADD, 2, 0, "BV_ADD", "bvadd", KindInfo::LEFT_ASSOC, true);
  init(Kind::BV_AND, 2, 0, "BV_AND", "bvand", KindInfo::LEFT_ASSOC, true);
  init(Kind::BV_ASHR, 2, 0, "BV_ASHR", "bvashr");
  init(Kind::BV_COMP, 2, 0, "BV_COMP", "bvcomp", KindInfo::CHAINABLE, true);
  init(Kind::BV_CONCAT, 2, 0, "BV_CONCAT", "concat", KindInfo::LEFT_ASSOC);
  init(Kind::BV_DEC, 1, 0, "BV_DEC", "bvdec");
  init(Kind::BV_EXTRACT, 1, 2, "BV_EXTRACT", "extract");
  init(Kind::BV_INC, 1, 0, "BV_INC", "bvinc");
  init(Kind::BV_MUL, 2, 0, "BV_MUL", "bvmul", KindInfo::LEFT_ASSOC, true);
  init(Kind::BV_NAND, 2, 0, "BV_NAND", "bvnand", KindInfo::NONE, true);
  init(Kind::BV_NEG, 1, 0, "BV_NEG", "bvneg");
  init(Kind::BV_NEGO, 1, 0, "BV_NEGO", "bvnego");
  init(Kind::BV_NOR, 2, 0, "BV_NOR", "bvnor", KindInfo::NONE, true);
  init(Kind::BV_NOT, 1, 0, "BV_NOT", "bvnot");
  init(Kind::BV_OR, 2, 0, "BV_OR", "bvor", KindInfo::LEFT_ASSOC, true);
  init(Kind::BV_REDAND, 1, 0, "BV_REDAND", "bvredand");
  init(Kind::BV_REDOR, 1, 0, "BV_REDOR", "bvredor");
  init(Kind::BV_REDXOR, 1, 0, "BV_REDXOR", "bvredxor");
  init(Kind::BV_REPEAT, 1, 1, "BV_REPEAT", "repeat");
  init(Kind::BV_ROL, 2, 0, "BV_ROL", "bvrol");
  init(Kind::BV_ROLI, 1, 1, "BV_ROLI", "rotate_left");
  init(Kind::BV_ROR, 2, 0, "BV_ROR", "bvror");
  init(Kind::BV_RORI, 1, 1, "BV_RORI", "rotate_right");
  init(Kind::BV_SADDO, 2, 0, "BV_SADDO", "bvsaddo", KindInfo::NONE, true);
  init(Kind::BV_SDIV, 2, 0, "BV_SDIV", "bvsdiv");
  init(Kind::BV_SDIVO, 2, 0, "BV_SDIVO", "bvsdivo");
  init(Kind::BV_SGE, 2, 0, "BV_SGE", "bvsge");
  init(Kind::BV_SGT, 2, 0, "BV_SGT", "bvsgt");
  init(Kind::BV_SHL, 2, 0, "BV_SHL", "bvshl");
  init(Kind::BV_SHR, 2, 0, "BV_SHR", "bvlshr");
  init(Kind::BV_SIGN_EXTEND, 1, 1, "BV_SIGN_EXTEND", "sign_extend");
  init(Kind::BV_SLE, 2, 0, "BV_SLE", "bvsle");
  init(Kind::BV_SLT, 2, 0, "BV_SLT", "bvslt");
  init(Kind::BV_SMOD, 2, 0, "BV_SMOD", "bvsmod");
  init(Kind::BV_SMULO, 2, 0, "BV_SMULO", "bvsmulo");
  init(Kind::BV_SREM, 2, 0, "BV_SREM", "bvsrem");
  init(Kind::BV_SSUBO, 2, 0, "BV_SSUBO", "bvssubo");
  init(Kind::BV_SUB, 2, 0, "BV_SUB", "bvsub");
  init(Kind::BV_UADDO, 2, 0, "BV_UADDO", "bvuaddo", KindInfo::NONE, true);
  init(Kind::BV_UDIV, 2, 0, "BV_UDIV", "bvudiv");
  init(Kind::BV_UGE, 2, 0, "BV_UGE", "bvuge");
  init(Kind::BV_UGT, 2, 0, "BV_UGT", "bvugt");
  init(Kind::BV_ULE, 2, 0, "BV_ULE", "bvule");
  init(Kind::BV_ULT, 2, 0, "BV_ULT", "bvult");
  init(Kind::BV_UMULO, 2, 0, "BV_UMULO", "bvumulo", KindInfo::NONE, true);
  init(Kind::BV_UREM, 2, 0, "BV_UREM", "bvurem");
  init(Kind::BV_USUBO, 2, 0, "BV_USUBO", "bvusubo");
  init(Kind::BV_XNOR, 2, 0, "BV_XNOR", "bvxnor", KindInfo::NONE, true);
  init(Kind::BV_XOR, 2, 0, "BV_XOR", "bvxor", KindInfo::LEFT_ASSOC, true);
  init(Kind::BV_ZERO_EXTEND, 1, 1, "BV_ZERO_EXTEND", "zero_extend");

  /* Floating-points */
  init(Kind::FP_ABS, 1, 0, "FP_ABS", "fp.abs");
  init(Kind::FP_ADD, 3, 0, "FP_ADD", "fp.add");
  init(Kind::FP_DIV, 3, 0, "FP_DIV", "fp.div");
  init(Kind::FP_EQUAL, 2, 0, "FP_EQUAL", "fp.eq", KindInfo::CHAINABLE);
  init(Kind::FP_FMA, 4, 0, "FP_FMA", "fp.fma");
  init(Kind::FP_FP, 3, 0, "FP_FP", "fp");
  init(Kind::FP_GEQ, 2, 0, "FP_GEQ", "fp.geq", KindInfo::CHAINABLE);
  init(Kind::FP_GT, 2, 0, "FP_GT", "fp.gt", KindInfo::CHAINABLE);
  init(Kind::FP_IS_INF, 1, 0, "FP_IS_INF", "fp.isInfinite");
  init(Kind::FP_IS_NAN, 1, 0, "FP_IS_NAN", "fp.isNaN");
  init(Kind::FP_IS_NEG, 1, 0, "FP_IS_NEG", "fp.isNegative");
  init(Kind::FP_IS_NORMAL, 1, 0, "FP_IS_NORMAL", "fp.isNormal");
  init(Kind::FP_IS_POS, 1, 0, "FP_IS_POS", "fp.isPositive");
  init(Kind::FP_IS_SUBNORMAL, 1, 0, "FP_IS_SUBNORMAL", "fp.isSubnormal");
  init(Kind::FP_IS_ZERO, 1, 0, "FP_IS_ZERO", "fp.isZero");
  init(Kind::FP_LEQ, 2, 0, "FP_LEQ", "fp.leq", KindInfo::CHAINABLE);
  init(Kind::FP_LT, 2, 0, "FP_LT", "fp.lt", KindInfo::CHAINABLE);
  init(Kind::FP_MAX, 2, 0, "FP_MAX", "fp.max");
  init(Kind::FP_MIN, 2, 0, "FP_MIN", "fp.min");
  init(Kind::FP_MUL, 3, 0, "FP_MUL", "fp.mul");
  init(Kind::FP_NEG, 1, 0, "FP_NEG", "fp.neg");
  init(Kind::FP_REM, 2, 0, "FP_REM", "fp.rem");
  init(Kind::FP_RTI, 2, 0, "FP_RTI", "fp.roundToIntegral");
  init(Kind::FP_SQRT, 2, 0, "FP_SQRT", "fp.sqrt");
  init(Kind::FP_SUB, 3, 0, "FP_SUB", "fp.sub");
  init(Kind::FP_TO_FP_FROM_BV, 1, 2, "FP_TO_FP_FROM_BV", "to_fp");
  init(Kind::FP_TO_FP_FROM_FP, 2, 2, "FP_TO_FP_FROM_FP", "to_fp");
  init(Kind::FP_TO_FP_FROM_SBV, 2, 2, "FP_TO_FP_FROM_SBV", "to_fp");
  init(Kind::FP_TO_FP_FROM_UBV, 2, 2, "FP_TO_FP_FROM_UBV", "to_fp_unsigned");
  init(Kind::FP_TO_SBV, 2, 1, "FP_TO_SBV", "to_sbv");
  init(Kind::FP_TO_UBV, 2, 1, "FP_TO_UBV", "to_ubv");

  /* Arrays */
  init(Kind::CONST_ARRAY, 1, 0, "CONST_ARRAY");
  init(Kind::SELECT, 2, 0, "SELECT", "select");
  init(Kind::STORE, 3, 0, "STORE", "store");

  /* Quantifiers */
  init(Kind::EXISTS, 2, 0, "EXISTS", "exists", KindInfo::RIGHT_ASSOC);
  init(Kind::FORALL, 2, 0, "FORALL", "forall", KindInfo::RIGHT_ASSOC);

  /* Functions */
  init(Kind::APPLY, KindInfo::s_nary, 0, "APPLY");
  init(Kind::LAMBDA, 2, 0, "LAMBDA", "lambda", KindInfo::RIGHT_ASSOC);
}

constexpr bool
KindInfo::complete() const
{
  return d_num_inited == static_cast<size_t>(Kind::NUM_KINDS);
}

const KindInfo&
KindInfo::get()
{
  static const constexpr KindInfo info;
  static_assert(info.complete(), "KindInfo not fully initialized.");
  return info;
}

}  // namespace bzla::node
