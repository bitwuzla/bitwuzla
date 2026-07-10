/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "rewrite/evaluator.h"
#include "solver/fp/symfpu_nm.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

// The evaluator only handles node kinds that survive rewriting (it is invoked
// from SolverEngine::_value()). Kinds that are unconditionally eliminated by
// the rewriter (OR, BV_DEC, BV_INC, FP_EQUAL, FP_FP, FP_GEQ, FP_GT, FP_SUB) are
// intentionally not handled here.
class TestEvaluator : public TestRewriter
{
 protected:
  TestEvaluator() : d_snm(d_nm) {}

  /**
   * Evaluate `kind` on the given value children and check the result.
   *
   * The result of Evaluator::evaluate() is cross-checked against the value
   * obtained by fully rewriting the corresponding node. The rewriter folds
   * value-only nodes through the *_EVAL rewrite rules, an independent dispatch
   * that does not go through Evaluator, so it is an independent oracle for the
   * evaluator's dispatch (operand order, index handling, operator selection).
   *
   * @return The evaluated (value) node.
   */
  Node check(Kind kind,
             const std::vector<Node>& children,
             const std::vector<uint64_t>& indices = {})
  {
    for (const Node& c : children)
    {
      assert(c.is_value());
    }
    Node node = d_nm.mk_node(kind, children, indices);
    Node rw   = d_rewriter.rewrite(node);
    EXPECT_TRUE(rw.is_value()) << "reference rewrite did not fold: " << node;

    Node ev = Evaluator::evaluate(d_nm, kind, children, indices);
    EXPECT_TRUE(ev.is_value());
    EXPECT_EQ(rw, ev) << "evaluator/rewriter mismatch for: " << node;
    return ev;
  }

  Node bv(uint64_t size, const std::string& bits)
  {
    return d_nm.mk_value(BitVector(size, bits));
  }

  Node fp35(const std::string& bits)
  {
    return d_nm.mk_value(FloatingPoint(d_fp35_type.fp_exp_size(),
                                       d_fp35_type.fp_sig_size(),
                                       BitVector(8, bits)));
  }

  fp::SymFpuNM d_snm;
};

/* -- Core / Boolean -------------------------------------------------------- */

TEST_F(TestEvaluator, core)
{
  Node ten   = bv(8, "00001010");
  Node three = bv(8, "00000011");
  Node rne   = d_nm.mk_value(RoundingMode::RNE);
  Node rtz   = d_nm.mk_value(RoundingMode::RTZ);

  // EQUAL (generic term equality)
  EXPECT_TRUE(check(Kind::EQUAL, {ten, ten}).value<bool>());
  EXPECT_FALSE(check(Kind::EQUAL, {ten, three}).value<bool>());
  EXPECT_TRUE(check(Kind::EQUAL, {d_true, d_true}).value<bool>());
  EXPECT_FALSE(check(Kind::EQUAL, {d_true, d_false}).value<bool>());
  EXPECT_TRUE(check(Kind::EQUAL, {rne, rne}).value<bool>());
  EXPECT_FALSE(check(Kind::EQUAL, {rne, rtz}).value<bool>());

  // ITE
  EXPECT_EQ(check(Kind::ITE, {d_true, ten, three}), ten);
  EXPECT_EQ(check(Kind::ITE, {d_false, ten, three}), three);

  // NOT / AND
  EXPECT_TRUE(check(Kind::NOT, {d_false}).value<bool>());
  EXPECT_FALSE(check(Kind::NOT, {d_true}).value<bool>());
  EXPECT_TRUE(check(Kind::AND, {d_true, d_true}).value<bool>());
  EXPECT_FALSE(check(Kind::AND, {d_true, d_false}).value<bool>());
}

/* -- Bit-vectors ----------------------------------------------------------- */

TEST_F(TestEvaluator, bv)
{
  Node a = bv(8, "00001010");  // 10
  Node b = bv(8, "00000011");  // 3

  EXPECT_EQ(check(Kind::BV_NOT, {a}), bv(8, "11110101"));
  EXPECT_EQ(check(Kind::BV_AND, {a, b}), bv(8, "00000010"));
  EXPECT_EQ(check(Kind::BV_XOR, {a, b}), bv(8, "00001001"));
  EXPECT_EQ(check(Kind::BV_EXTRACT, {a}, {5, 2}), bv(4, "0010"));
  EXPECT_EQ(check(Kind::BV_COMP, {a, b}), bv(1, "0"));
  EXPECT_EQ(check(Kind::BV_COMP, {a, a}), bv(1, "1"));
  EXPECT_EQ(check(Kind::BV_ADD, {a, b}), bv(8, "00001101"));
  EXPECT_EQ(check(Kind::BV_MUL, {a, b}), bv(8, "00011110"));
  EXPECT_FALSE(check(Kind::BV_ULT, {a, b}).value<bool>());
  EXPECT_TRUE(check(Kind::BV_ULT, {b, a}).value<bool>());
  EXPECT_EQ(check(Kind::BV_SHL, {a, b}), bv(8, "01010000"));
  EXPECT_FALSE(check(Kind::BV_SLT, {a, b}).value<bool>());
  EXPECT_EQ(check(Kind::BV_SHR, {a, b}), bv(8, "00000001"));
  EXPECT_EQ(check(Kind::BV_ASHR, {a, b}), bv(8, "00000001"));
  EXPECT_EQ(check(Kind::BV_UDIV, {a, b}), bv(8, "00000011"));
  EXPECT_EQ(check(Kind::BV_UREM, {a, b}), bv(8, "00000001"));
  EXPECT_EQ(check(Kind::BV_CONCAT, {bv(4, "1010"), bv(4, "0011")}),
            bv(8, "10100011"));

  // Signed vs. unsigned dispatch: a negative operand.
  Node neg = bv(8, "11111011");  // -5 signed / 251 unsigned
  Node two = bv(8, "00000010");
  EXPECT_EQ(check(Kind::BV_ASHR, {neg, two}), bv(8, "11111110"));  // -2
  EXPECT_EQ(check(Kind::BV_SHR, {neg, two}), bv(8, "00111110"));   // logical
  EXPECT_TRUE(check(Kind::BV_SLT, {neg, two}).value<bool>());      // -5 < 2
  EXPECT_FALSE(check(Kind::BV_ULT, {neg, two}).value<bool>());     // 251 < 2
}

/* -- Floating-point predicates --------------------------------------------- */

TEST_F(TestEvaluator, fp_predicates)
{
  Node pos    = fp35("00110000");  // +1.0
  Node neg    = fp35("10110000");  // -1.0
  Node pzero  = fp35("00000000");  // +0.0
  Node pinf   = fp35("01110000");  // +oo
  Node nan    = fp35("01110001");  // NaN
  Node subnrm = fp35("00000001");  // smallest positive subnormal

  EXPECT_TRUE(check(Kind::FP_IS_INF, {pinf}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_INF, {pos}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_NAN, {nan}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_NAN, {pos}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_NEG, {neg}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_NEG, {pos}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_POS, {pos}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_POS, {neg}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_NORMAL, {pos}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_NORMAL, {subnrm}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_SUBNORMAL, {subnrm}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_SUBNORMAL, {pos}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_IS_ZERO, {pzero}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_IS_ZERO, {pos}).value<bool>());
}

/* -- Floating-point comparisons -------------------------------------------- */

TEST_F(TestEvaluator, fp_compare)
{
  Node one = fp35("00110000");  // +1.0
  Node two = fp35("01000000");  // +2.0
  Node nan = fp35("01110001");  // NaN

  EXPECT_TRUE(check(Kind::FP_LEQ, {one, two}).value<bool>());
  EXPECT_TRUE(check(Kind::FP_LEQ, {one, one}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_LEQ, {two, one}).value<bool>());

  EXPECT_TRUE(check(Kind::FP_LT, {one, two}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_LT, {one, one}).value<bool>());

  // Any comparison with NaN is false.
  EXPECT_FALSE(check(Kind::FP_LEQ, {nan, one}).value<bool>());
  EXPECT_FALSE(check(Kind::FP_LT, {nan, one}).value<bool>());
}

/* -- Floating-point arithmetic --------------------------------------------- */

TEST_F(TestEvaluator, fp_arith)
{
  Node rne   = d_nm.mk_value(RoundingMode::RNE);
  Node one   = fp35("00110000");  // +1.0
  Node mone  = fp35("10110000");  // -1.0
  Node two   = fp35("01000000");  // +2.0
  Node three = fp35("01001000");  // +3.0
  Node four  = fp35("01010000");  // +4.0
  Node oneh  = fp35("00111000");  // +1.5

  EXPECT_EQ(check(Kind::FP_ABS, {mone}), one);
  EXPECT_EQ(check(Kind::FP_NEG, {one}), mone);
  EXPECT_EQ(check(Kind::FP_ADD, {rne, one, one}), two);
  EXPECT_EQ(check(Kind::FP_MUL, {rne, two, two}), four);
  EXPECT_EQ(check(Kind::FP_DIV, {rne, two, two}), one);
  EXPECT_EQ(check(Kind::FP_SQRT, {rne, four}), two);
  // fma: 1.0 * 2.0 + 1.0 = 3.0
  EXPECT_EQ(check(Kind::FP_FMA, {rne, one, two, one}), three);
  // rem: 1.0 rem 2.0 = 1.0 (quotient rounds to 0)
  EXPECT_EQ(check(Kind::FP_REM, {one, two}), one);
  // roundToIntegral: round 1.5 to nearest even -> 2.0
  EXPECT_EQ(check(Kind::FP_RTI, {rne, oneh}), two);
}

/* -- Floating-point conversions -------------------------------------------- */

TEST_F(TestEvaluator, fp_convert)
{
  Node rne = d_nm.mk_value(RoundingMode::RNE);

  // to_fp from IEEE bit-vector: reinterpret 8 bits as fp35.
  EXPECT_EQ(check(Kind::FP_TO_FP_FROM_BV, {bv(8, "01000000")}, {3, 5}),
            fp35("01000000"));  // +2.0

  // to_fp from fp: identity format conversion.
  EXPECT_EQ(check(Kind::FP_TO_FP_FROM_FP, {rne, fp35("01000000")}, {3, 5}),
            fp35("01000000"));  // +2.0
  // to_fp from fp: widen to a larger format (cross-checked against rewriter).
  check(Kind::FP_TO_FP_FROM_FP, {rne, fp35("00110000")}, {5, 11});

  // to_fp from signed bit-vector: -3 -> -3.0
  EXPECT_EQ(check(Kind::FP_TO_FP_FROM_SBV, {rne, bv(4, "1101")}, {3, 5}),
            fp35("11001000"));  // -3.0
  // to_fp_unsigned from bit-vector: 3 -> +3.0
  EXPECT_EQ(check(Kind::FP_TO_FP_FROM_UBV, {rne, bv(4, "0011")}, {3, 5}),
            fp35("01001000"));  // +3.0
  // Same bit pattern interpreted unsigned (13) differs from signed (-3).
  check(Kind::FP_TO_FP_FROM_UBV, {rne, bv(4, "1101")}, {3, 5});
}

}  // namespace bzla::test
