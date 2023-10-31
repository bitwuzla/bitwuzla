/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <sstream>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

class TestPrinter : public TestCommon
{
 protected:
  void test_unary(Kind kind, const Type& type)
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(kind, {d_nm.mk_const(type, "x")}));
    ASSERT_EQ(ss.str(), "(" + std::string(KindInfo::smt2_name(kind)) + " x)");
  }
  void test_unary_indexed(Kind kind,
                          const Type& type,
                          const std::vector<uint64_t>& idxs)
  {
    std::stringstream ss, es;
    Printer::print(ss, d_nm.mk_node(kind, {d_nm.mk_const(type, "x")}, idxs));
    es << "((_ " << KindInfo::smt2_name(kind);
    for (uint64_t i : idxs) es << " " << i;
    es << ") x)";
    ASSERT_EQ(ss.str(), es.str());
  }
  void test_nary(Kind kind, const std::vector<Type>& types)
  {
    std::stringstream ss, es;
    std::vector<Node> consts;
    es << "(" << KindInfo::smt2_name(kind);
    for (size_t i = 0; i < types.size(); ++i)
    {
      consts.push_back(d_nm.mk_const(types[i], "x" + std::to_string(i)));
      es << " "
         << "x" + std::to_string(i);
    }
    es << ")";
    Printer::print(ss, d_nm.mk_node(kind, consts));
    ASSERT_EQ(ss.str(), es.str());
  }
  void test_nary_indexed(Kind kind,
                         const std::vector<Type>& types,
                         const std::vector<uint64_t>& idxs)
  {
    std::stringstream ss, es;
    std::vector<Node> consts;
    es << "((_ " << KindInfo::smt2_name(kind);
    for (uint64_t i : idxs) es << " " << i;
    es << ")";
    for (size_t i = 0; i < types.size(); ++i)
    {
      consts.push_back(d_nm.mk_const(types[i], "x" + std::to_string(i)));
      es << " "
         << "x" + std::to_string(i);
    }
    es << ")";
    Printer::print(ss, d_nm.mk_node(kind, consts, idxs));
    ASSERT_EQ(ss.str(), es.str());
  }

  NodeManager& d_nm = NodeManager::get();
  Type d_type_bool  = d_nm.mk_bool_type();
  Type d_type_bv    = d_nm.mk_bv_type(8);
  Type d_type_fp    = d_nm.mk_fp_type(5, 11);
  Type d_type_rm    = d_nm.mk_rm_type();
};

TEST_F(TestPrinter, print_type)
{
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_bool_type());
    ASSERT_EQ(ss.str(), "Bool");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_rm_type());
    ASSERT_EQ(ss.str(), "RoundingMode");
  }
  {
    std::stringstream ss;
    Type t = d_nm.mk_uninterpreted_type();
    Printer::print(ss, t);
    ASSERT_EQ(ss.str(), "@bzla.sort" + std::to_string(t.id()));
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_uninterpreted_type("foo"));
    ASSERT_EQ(ss.str(), "foo");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_type_bv);
    ASSERT_EQ(ss.str(), "(_ BitVec 8)");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_type_fp);
    ASSERT_EQ(ss.str(), "(_ FloatingPoint 5 11)");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_array_type(d_type_bv, d_type_fp));
    ASSERT_EQ(ss.str(), "(Array (_ BitVec 8) (_ FloatingPoint 5 11))");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_fun_type({d_type_bv, d_type_fp}));
    ASSERT_EQ(ss.str(), "(_ BitVec 8) -> (_ FloatingPoint 5 11)");
  }
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_fun_type({d_type_bool, d_type_bv, d_type_fp}));
    ASSERT_EQ(ss.str(), "Bool (_ BitVec 8) -> (_ FloatingPoint 5 11)");
  }
}

TEST_F(TestPrinter, print_value)
{
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_value(true));
    ASSERT_EQ(ss.str(), "true");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_value(false));
    ASSERT_EQ(ss.str(), "false");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_value(BitVector::from_ui(4, 2)));
    ASSERT_EQ(ss.str(), "#b0010");
  }

  {
    std::stringstream ss;
    Printer::print(ss,
                   d_nm.mk_value(FloatingPoint(d_nm.mk_fp_type(3, 5),
                                               BitVector::from_ui(8, 2))));
    ASSERT_EQ(ss.str(), "(fp #b0 #b000 #b0010)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_value(RoundingMode::RNA));
    ASSERT_EQ(ss.str(), "RNA");
  }
}

TEST_F(TestPrinter, print_const)
{
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_const(d_type_bool, "x"));
    ASSERT_EQ(ss.str(), "x");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_const(d_type_bool, ""));
    ASSERT_EQ(ss.str(), "||");
  }

  {
    std::stringstream ss, expected;
    Node n = d_nm.mk_const(d_type_bool);
    Printer::print(ss, n);
    expected << "@bzla.const_" << n.id();
    ASSERT_EQ(ss.str(), expected.str());
  }
}

TEST_F(TestPrinter, print_var)
{
  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_var(d_type_bool, "x"));
    ASSERT_EQ(ss.str(), "x");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_var(d_type_bool, ""));
    ASSERT_EQ(ss.str(), "||");
  }

  {
    std::stringstream ss, expected;
    Node n = d_nm.mk_var(d_type_bool);
    Printer::print(ss, n);
    expected << "@bzla.var_" << n.id();
    ASSERT_EQ(ss.str(), expected.str());
  }
}

TEST_F(TestPrinter, print_binder)
{
  Node w = d_nm.mk_var(d_type_bool, "w");
  Node x = d_nm.mk_var(d_nm.mk_bv_type(32), "x");
  Node y = d_nm.mk_var(d_nm.mk_rm_type(), "y");
  Node z = d_nm.mk_var(d_nm.mk_fp_type(8, 24), "z");

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((w Bool)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((x (_ BitVec 32))) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::FORALL, {y, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((y RoundingMode)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::FORALL, {z, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((z (_ FloatingPoint 8 24))) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::EXISTS, {w, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(exists ((w Bool)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::EXISTS, {x, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(exists ((x (_ BitVec 32))) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::EXISTS, {y, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(exists ((y RoundingMode)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::EXISTS, {z, d_nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(exists ((z (_ FloatingPoint 8 24))) true)");
  }

  {
    Node v = d_nm.mk_var(d_nm.mk_bv_type(8), "v");
    std::stringstream ss;
    Printer::print(ss, d_nm.mk_node(Kind::LAMBDA, {v, v}));
    ASSERT_EQ(ss.str(), "(lambda ((v (_ BitVec 8))) v)");
  }
}

TEST_F(TestPrinter, print_apply)
{
  Type type = d_nm.mk_fun_type({d_nm.mk_bv_type(32), d_type_bool});
  Node f    = d_nm.mk_const(type, "f");
  Node x    = d_nm.mk_const(d_nm.mk_bv_type(32), "x");

  std::stringstream ss;
  Printer::print(ss, d_nm.mk_node(Kind::APPLY, {f, x}));
  ASSERT_EQ(ss.str(), "(f x)");
}

TEST_F(TestPrinter, print_let1)
{
  Node x       = d_nm.mk_const(d_type_bool, "x");
  Node y       = d_nm.mk_const(d_type_bool, "y");
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});
  Node or_and  = d_nm.mk_node(Kind::OR, {x_and_y, x_and_y});

  std::stringstream ss;
  Printer::print(ss, or_and);
  ASSERT_EQ(ss.str(), "(let ((_let0 (and x y))) (or _let0 _let0))");
}

TEST_F(TestPrinter, print_let2)
{
  Node x          = d_nm.mk_const(d_type_bool, "x");
  Node y          = d_nm.mk_const(d_type_bool, "y");
  Node x_and_y    = d_nm.mk_node(Kind::AND, {x, y});
  Node or_and     = d_nm.mk_node(Kind::OR, {x_and_y, x_and_y});
  Node and_or_and = d_nm.mk_node(Kind::AND, {or_and, or_and});

  std::stringstream ss;
  Printer::print(ss, and_or_and);
  ASSERT_EQ(ss.str(),
            "(let ((_let0 (and x y))) (let ((_let1 (or _let0 _let0))) (and "
            "_let1 _let1)))");
}

TEST_F(TestPrinter, print_let3)
{
  Node a       = d_nm.mk_const(d_type_bool, "a");
  Node b       = d_nm.mk_const(d_type_bool, "b");
  Node a_and_b = d_nm.mk_node(Kind::AND, {a, b});
  Node forall =
      d_nm.mk_node(Kind::FORALL, {d_nm.mk_var(d_type_bool, "x"), a_and_b});
  Node or_and = d_nm.mk_node(Kind::OR, {a_and_b, forall});

  std::stringstream ss;
  Printer::print(ss, or_and);
  ASSERT_EQ(ss.str(),
            "(let ((_let0 (and a b))) (or _let0 (forall ((x Bool)) _let0)))");
}

TEST_F(TestPrinter, print_let4)
{
  Node x          = d_nm.mk_var(d_type_bool, "x");
  Node y          = d_nm.mk_var(d_type_bool, "y");
  Node x_and_y    = d_nm.mk_node(Kind::AND, {x, y});
  Node or_and     = d_nm.mk_node(Kind::OR, {x_and_y, x_and_y});
  Node and_or_and = d_nm.mk_node(Kind::AND, {or_and, or_and});
  Node forall     = d_nm.mk_node(Kind::FORALL,
                             {x, d_nm.mk_node(Kind::FORALL, {y, and_or_and})});

  std::stringstream ss;
  Printer::print(ss, forall);
  ASSERT_EQ(ss.str(),
            "(forall ((x Bool)) (forall ((y Bool)) (let ((_let0 (and x y))) "
            "(let ((_let1 (or _let0 _let0))) (and _let1 _let1)))))");
}

TEST_F(TestPrinter, print_nested)
{
  Node bvand0 = d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  Node bvand1 =
      d_nm.mk_node(Kind::BV_AND, {d_nm.mk_value(BitVector(4, "1001")), bvand0});
  std::stringstream ss;
  Printer::print(ss, bvand1);
  ASSERT_EQ(ss.str(), "(bvand #b1001 (bvand #b1001 #b1110))");
}

TEST_F(TestPrinter, print_const_array)
{
  Type bv32        = d_nm.mk_bv_type(32);
  Type fp32        = d_nm.mk_fp_type(8, 24);
  Node value       = d_nm.mk_const(bv32, "val");
  Node const_array = d_nm.mk_const_array(d_nm.mk_array_type(fp32, bv32), value);
  std::stringstream ss;
  Printer::print(ss, const_array);
  ASSERT_EQ(ss.str(),
            "((as const (Array (_ FloatingPoint 8 24) (_ BitVec 32))) val)");
}

/* unary operators ---------------------------------------------------------- */

// bool

TEST_F(TestPrinter, print_not) { test_unary(Kind::NOT, d_type_bool); }

// bit-vectors

TEST_F(TestPrinter, print_bv_not) { test_unary(Kind::BV_NOT, d_type_bv); }

TEST_F(TestPrinter, print_bv_neg) { test_unary(Kind::BV_NEG, d_type_bv); }

TEST_F(TestPrinter, print_bv_redand) { test_unary(Kind::BV_REDAND, d_type_bv); }

TEST_F(TestPrinter, print_bv_redor) { test_unary(Kind::BV_REDOR, d_type_bv); }

TEST_F(TestPrinter, print_bv_redxor) { test_unary(Kind::BV_REDXOR, d_type_bv); }

TEST_F(TestPrinter, print_bv_inc) { test_unary(Kind::BV_INC, d_type_bv); }

TEST_F(TestPrinter, print_bv_dec) { test_unary(Kind::BV_INC, d_type_bv); }

TEST_F(TestPrinter, print_bv_extract)
{
  test_unary_indexed(Kind::BV_EXTRACT, d_type_bv, {3, 2});
}

TEST_F(TestPrinter, print_bv_repeat)
{
  test_unary_indexed(Kind::BV_REPEAT, d_type_bv, {3});
}

TEST_F(TestPrinter, print_bv_roli)
{
  test_unary_indexed(Kind::BV_ROLI, d_type_bv, {3});
}

TEST_F(TestPrinter, print_bv_rori)
{
  test_unary_indexed(Kind::BV_RORI, d_type_bv, {3});
}

TEST_F(TestPrinter, print_bv_sext)
{
  test_unary_indexed(Kind::BV_SIGN_EXTEND, d_type_bv, {3});
}

TEST_F(TestPrinter, print_bv_zext)
{
  test_unary_indexed(Kind::BV_ZERO_EXTEND, d_type_bv, {3});
}

// floating-point

TEST_F(TestPrinter, print_fp_abs) { test_unary(Kind::FP_ABS, d_type_fp); }

TEST_F(TestPrinter, print_fp_is_inf) { test_unary(Kind::FP_IS_INF, d_type_fp); }

TEST_F(TestPrinter, print_fp_is_nan) { test_unary(Kind::FP_IS_NAN, d_type_fp); }

TEST_F(TestPrinter, print_fp_is_neg) { test_unary(Kind::FP_IS_NEG, d_type_fp); }

TEST_F(TestPrinter, print_fp_is_normal)
{
  test_unary(Kind::FP_IS_NORMAL, d_type_fp);
}

TEST_F(TestPrinter, print_fp_is_pos) { test_unary(Kind::FP_IS_POS, d_type_fp); }

TEST_F(TestPrinter, print_fp_is_subnormal)
{
  test_unary(Kind::FP_IS_SUBNORMAL, d_type_fp);
}

TEST_F(TestPrinter, print_fp_is_zero)
{
  test_unary(Kind::FP_IS_ZERO, d_type_fp);
}

TEST_F(TestPrinter, print_fp_neg) { test_unary(Kind::FP_NEG, d_type_fp); }

TEST_F(TestPrinter, print_fp_to_fp_from_bv)
{
  test_unary_indexed(Kind::FP_TO_FP_FROM_BV, d_type_bv, {3, 5});
}

/* binary operators --------------------------------------------------------- */

// any

TEST_F(TestPrinter, print_equal)
{
  test_nary(Kind::EQUAL, {d_type_bool, d_type_bool});
}

TEST_F(TestPrinter, print_distinct)
{
  test_nary(Kind::DISTINCT, {d_type_bool, d_type_bool});
}

// arrays

TEST_F(TestPrinter, print_array_select)
{
  test_nary(Kind::SELECT,
            {d_nm.mk_array_type(d_type_bv, d_type_fp), d_type_bv});
}

// boolean

TEST_F(TestPrinter, print_bool_and)
{
  test_nary(Kind::AND, {d_type_bool, d_type_bool});
}

TEST_F(TestPrinter, print_bool_implies)
{
  test_nary(Kind::IMPLIES, {d_type_bool, d_type_bool});
}

TEST_F(TestPrinter, print_bool_or)
{
  test_nary(Kind::OR, {d_type_bool, d_type_bool});
}

TEST_F(TestPrinter, print_bool_xor)
{
  test_nary(Kind::XOR, {d_type_bool, d_type_bool});
}

// bit-vector

TEST_F(TestPrinter, print_bv_add)
{
  test_nary(Kind::BV_ADD, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_and)
{
  test_nary(Kind::BV_AND, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ashr)
{
  test_nary(Kind::BV_ASHR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_comp)
{
  test_nary(Kind::BV_COMP, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_concat)
{
  test_nary(Kind::BV_CONCAT, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_mul)
{
  test_nary(Kind::BV_MUL, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_nand)
{
  test_nary(Kind::BV_NAND, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_nor)
{
  test_nary(Kind::BV_NOR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_or)
{
  test_nary(Kind::BV_OR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_rol)
{
  test_nary(Kind::BV_ROL, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ror)
{
  test_nary(Kind::BV_ROR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_saddo)
{
  test_nary(Kind::BV_SADDO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sdiv)
{
  test_nary(Kind::BV_SDIV, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sdivo)
{
  test_nary(Kind::BV_SDIVO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sge)
{
  test_nary(Kind::BV_SGE, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sgt)
{
  test_nary(Kind::BV_SGT, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_shl)
{
  test_nary(Kind::BV_SHL, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_shr)
{
  test_nary(Kind::BV_SHR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sle)
{
  test_nary(Kind::BV_SLE, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_slt)
{
  test_nary(Kind::BV_SLT, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_smod)
{
  test_nary(Kind::BV_SMOD, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_smulo)
{
  test_nary(Kind::BV_SMULO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_srem)
{
  test_nary(Kind::BV_SREM, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ssubo)
{
  test_nary(Kind::BV_SSUBO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_sub)
{
  test_nary(Kind::BV_SUB, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_uaddo)
{
  test_nary(Kind::BV_UADDO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_udiv)
{
  test_nary(Kind::BV_UDIV, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_uge)
{
  test_nary(Kind::BV_UGE, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ugt)
{
  test_nary(Kind::BV_UGT, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ule)
{
  test_nary(Kind::BV_ULE, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_ult)
{
  test_nary(Kind::BV_ULT, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_umulo)
{
  test_nary(Kind::BV_UMULO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_urem)
{
  test_nary(Kind::BV_UREM, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_usubo)
{
  test_nary(Kind::BV_USUBO, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_xnor)
{
  test_nary(Kind::BV_XNOR, {d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_bv_xor)
{
  test_nary(Kind::BV_XOR, {d_type_bv, d_type_bv});
}

// floating-point

TEST_F(TestPrinter, print_fp_eq)
{
  test_nary(Kind::FP_EQUAL, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_geq)
{
  test_nary(Kind::FP_GEQ, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_gt)
{
  test_nary(Kind::FP_GT, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_leq)
{
  test_nary(Kind::FP_LEQ, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_lt)
{
  test_nary(Kind::FP_LT, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_max)
{
  test_nary(Kind::FP_MAX, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_min)
{
  test_nary(Kind::FP_MIN, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_rem)
{
  test_nary(Kind::FP_REM, {d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_rti)
{
  test_nary(Kind::FP_RTI, {d_type_rm, d_type_fp});
}

TEST_F(TestPrinter, print_fp_sqrt)
{
  test_nary(Kind::FP_SQRT, {d_type_rm, d_type_fp});
}

TEST_F(TestPrinter, print_fp_to_fp_from_fp)
{
  test_nary_indexed(Kind::FP_TO_FP_FROM_FP, {d_type_rm, d_type_fp}, {8, 24});
}

TEST_F(TestPrinter, print_fp_to_fp_from_sbv)
{
  test_nary_indexed(Kind::FP_TO_FP_FROM_SBV, {d_type_rm, d_type_bv}, {8, 24});
}

TEST_F(TestPrinter, print_fp_to_fp_from_ubv)
{
  test_nary_indexed(Kind::FP_TO_FP_FROM_UBV, {d_type_rm, d_type_bv}, {8, 24});
}

TEST_F(TestPrinter, print_fp_to_sbv)
{
  test_nary_indexed(Kind::FP_TO_SBV, {d_type_rm, d_type_fp}, {24});
}

TEST_F(TestPrinter, print_fp_to_ubv)
{
  test_nary_indexed(Kind::FP_TO_UBV, {d_type_rm, d_type_fp}, {24});
}

/* ternary operators -------------------------------------------------------- */

// any

TEST_F(TestPrinter, print_ite)
{
  test_nary(Kind::ITE, {d_type_bool, d_type_bv, d_type_bv});
}

// arrays

TEST_F(TestPrinter, print_array_store)
{
  test_nary(Kind::STORE,
            {d_nm.mk_array_type(d_type_bv, d_type_fp), d_type_bv, d_type_fp});
}

// floating-point

TEST_F(TestPrinter, print_fp_add)
{
  test_nary(Kind::FP_ADD, {d_type_rm, d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_div)
{
  test_nary(Kind::FP_DIV, {d_type_rm, d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_FP)
{
  test_nary(Kind::FP_FP, {d_nm.mk_bv_type(1), d_type_bv, d_type_bv});
}

TEST_F(TestPrinter, print_fp_mul)
{
  test_nary(Kind::FP_MUL, {d_type_rm, d_type_fp, d_type_fp});
}

TEST_F(TestPrinter, print_fp_sub)
{
  test_nary(Kind::FP_SUB, {d_type_rm, d_type_fp, d_type_fp});
}

/* quaternary operators ----------------------------------------------------- */

// floating-point

TEST_F(TestPrinter, print_fp_fma)
{
  test_nary(Kind::FP_FMA, {d_type_rm, d_type_fp, d_type_fp, d_type_fp});
}

}  // namespace bzla::test
