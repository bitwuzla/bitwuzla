/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <functional>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "option/option.h"
#include "sat/sat_solver_factory.h"
#include "solver/fp/floating_point.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using namespace option;

/* -------------------------------------------------------------------------- */

/**
 * Exhaustive tests for word-blasted encodings in small formats.
 *
 * For each instance, we check the validity of (= (<op> rm b) table) for
 * - operator `<op>`
 * - a symbolic rounding mode `rm`
 * - a symbolic bit-vector term `b`, whose bits give the operands of `<op>`,
 *   either directly or reinterpreted as floating-point values via
 *   (_ to_fp e s)
 * - a decision tree `table` constructed over all rounding modes and values of
 *   `b` with the expected results computed by FloatingPoint via MPFR.
 *   Unspecified results of partial operators are represented by the term
 *   (<op> rm b) itself and are thus not constrained.
 *
 * @note Script contrib/check-fp-word-blaster.py performs the same check for
 *       larger formats.
 */
class TestFpWordBlaster : public TestCommon
{
 protected:
  using FpFormat = std::pair<uint64_t, uint64_t>;

  TestFpWordBlaster() : d_sat_factory(d_options) {}

  void SetUp() override
  {
    TestCommon::SetUp();
    // Report incorrect encodings as sat instead of failing the model check.
    d_options.dbg_check_model.set(false);
    d_rm = d_nm.mk_const(d_nm.mk_rm_type(), "rm");
    for (int32_t i = 0, n = static_cast<int32_t>(RoundingMode::NUM_RM); i < n;
         ++i)
    {
      d_all_rms.push_back(static_cast<RoundingMode>(i));
    }
  }

  /**
   * Get all formats of at most the given size.
   * @param max_size The maximum size of the formats, given as the sum of
   *                 exponent and significand size.
   * @return The formats.
   */
  static std::vector<FpFormat> formats(uint64_t max_size)
  {
    std::vector<FpFormat> res;
    for (uint64_t exp_size = 2; exp_size < max_size; ++exp_size)
    {
      for (uint64_t sig_size = 2; exp_size + sig_size <= max_size; ++sig_size)
      {
        res.emplace_back(exp_size, sig_size);
      }
    }
    return res;
  }

  /**
   * Get the i-th floating-point operand given by the bits of a bit-vector
   * term.
   * @param b      The bit-vector term.
   * @param format The format of the operand.
   * @param i      The index of the operand.
   * @return The operand.
   */
  Node operand(const Node& b, const FpFormat& format, uint64_t i)
  {
    uint64_t size = format.first + format.second;
    return d_nm.mk_node(
        Kind::FP_TO_FP_FROM_BV,
        {d_nm.mk_node(Kind::BV_EXTRACT, {b}, {(i + 1) * size - 1, i * size})},
        {format.first, format.second});
  }

  /**
   * Get the i-th floating-point operand given by the bits of a bit-vector
   * value.
   * @param bv     The bit-vector value.
   * @param format The format of the operand.
   * @param i      The index of the operand.
   * @return The operand.
   */
  static FloatingPoint operand(const BitVector& bv,
                               const FpFormat& format,
                               uint64_t i)
  {
    uint64_t size = format.first + format.second;
    return FloatingPoint(format.first,
                         format.second,
                         bv.bvextract((i + 1) * size - 1, i * size));
  }

  /**
   * Check the word-blasted encoding of an operation for all rounding modes
   * and all values of a bit-vector input.
   * @param bv_size  The size of the bit-vector input.
   * @param mk_term  The function to create the operation for a given rounding
   *                 mode and bit-vector input.
   * @param expected The function to compute the expected result value for a
   *                 given rounding mode and bit-vector value, a null node if
   *                 the result is unspecified.
   * @return The result of the satisfiability check, unsat if the encoding is
   *         correct.
   */
  Result check(
      uint64_t bv_size,
      const std::function<Node(const Node&, const Node&)>& mk_term,
      const std::function<Node(RoundingMode, const BitVector&)>& expected)
  {
    Node b    = d_nm.mk_const(d_nm.mk_bv_type(bv_size), "b");
    Node term = mk_term(d_rm, b);
    Node table;
    for (RoundingMode rm : d_all_rms)
    {
      std::vector<Node> values;
      for (uint64_t i = 0, n = uint64_t{1} << bv_size; i < n; ++i)
      {
        Node res = expected(rm, BitVector::from_ui(bv_size, i));
        values.push_back(res.is_null() ? term : res);
      }
      Node tree = mk_tree(b, values, 0, bv_size);
      table = table.is_null()
                  ? tree
                  : d_nm.mk_node(
                        Kind::ITE,
                        {d_nm.mk_node(Kind::EQUAL, {d_rm, d_nm.mk_value(rm)}),
                         tree,
                         table});
    }
    SolvingContext ctx(d_nm, d_options, d_sat_factory);
    ctx.assert_formula(d_nm.mk_node(Kind::DISTINCT, {term, table}));
    return ctx.solve();
  }

  /** The node manager. */
  NodeManager d_nm;
  /** The solver options. */
  Options d_options;
  /** The SAT solver factory. */
  sat::SatSolverFactory d_sat_factory;
  /** The rounding mode constant. */
  Node d_rm;
  /** All rounding modes. */
  std::vector<RoundingMode> d_all_rms;

 private:
  /**
   * Create a decision tree that maps each value of the lower `size` bits of
   * `b` to its expected result.
   *
   * This encodes the expected results for one rounding mode, which are
   * computed concretely for every value of `b`, as a term over `b` that can
   * be compared against the word-blasted encoding (see check()). The tree
   * splits on the most significant bit first and selects values[offset + i]
   * if the lower `size` bits of `b` represent value `i`. If both subtrees of a
   * split are equal, the split is omitted. This keeps the tree small, since
   * inputs that only differ in their lower bits often have the same result,
   * e.g., all NaNs, or all values that round to the same integral value.
   *
   * @param b      The bit-vector input.
   * @param values The expected results, indexed by the value of `b`.
   * @param offset The index of the first leaf of the tree in `values`.
   * @param size   The number of bits to split on.
   * @return The decision tree.
   */
  Node mk_tree(const Node& b,
               const std::vector<Node>& values,
               uint64_t offset,
               uint64_t size)
  {
    if (size == 0)
    {
      return values[offset];
    }
    uint64_t half = uint64_t{1} << (size - 1);
    Node lo       = mk_tree(b, values, offset, size - 1);
    Node hi       = mk_tree(b, values, offset + half, size - 1);
    if (lo == hi)
    {
      return lo;
    }
    Node bit = d_nm.mk_node(Kind::BV_EXTRACT, {b}, {size - 1, size - 1});
    return d_nm.mk_node(
        Kind::ITE,
        {d_nm.mk_node(Kind::EQUAL, {bit, d_nm.mk_value(BitVector::mk_true())}),
         hi,
         lo});
  }
};

/* -------------------------------------------------------------------------- */

// Requires the patches applied to the bundled SymFPU, which is only guaranteed
// to be used with experimental formats.
#ifdef BZLA_USE_FPEXP

TEST_F(TestFpWordBlaster, rti)
{
  for (const auto& [exp_size, sig_size] : formats(11))
  {
    auto mk_term = [&](const Node& rm, const Node& b) {
      return d_nm.mk_node(
          Kind::FP_RTI,
          {rm,
           d_nm.mk_node(Kind::FP_TO_FP_FROM_BV, {b}, {exp_size, sig_size})});
    };
    auto expected = [&](RoundingMode rm, const BitVector& bv) {
      return d_nm.mk_value(FloatingPoint(exp_size, sig_size, bv).fprti(rm));
    };
    ASSERT_EQ(check(exp_size + sig_size, mk_term, expected), Result::UNSAT)
        << "(_ FloatingPoint " << exp_size << " " << sig_size << ")";
  }
}

TEST_F(TestFpWordBlaster, min_max)
{
  for (const auto& format : formats(7))
  {
    for (Kind kind : {Kind::FP_MIN, Kind::FP_MAX})
    {
      auto mk_term = [&](const Node& rm, const Node& b) {
        (void) rm;
        return d_nm.mk_node(kind,
                            {operand(b, format, 0), operand(b, format, 1)});
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        (void) rm;
        FloatingPoint x = operand(bv, format, 0);
        FloatingPoint y = operand(bv, format, 1);
        // The result for zeros of different sign is unspecified.
        if (x.fpiszero() && y.fpiszero() && x.fpisneg() != y.fpisneg())
        {
          return Node();
        }
        return d_nm.mk_value(kind == Kind::FP_MIN ? x.fpmin(y) : x.fpmax(y));
      };
      ASSERT_EQ(check(2 * (format.first + format.second), mk_term, expected),
                Result::UNSAT)
          << kind << " (_ FloatingPoint " << format.first << " "
          << format.second << ")";
    }
  }
}

TEST_F(TestFpWordBlaster, to_fp_from_fp)
{
  for (const auto& [exp_size1, sig_size1] : formats(8))
  {
    for (const auto& [exp_size2, sig_size2] : formats(11))
    {
      auto mk_term = [&](const Node& rm, const Node& b) {
        return d_nm.mk_node(
            Kind::FP_TO_FP_FROM_FP,
            {rm,
             d_nm.mk_node(Kind::FP_TO_FP_FROM_BV, {b}, {exp_size1, sig_size1})},
            {exp_size2, sig_size2});
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        return d_nm.mk_value(FloatingPoint(
            exp_size2, sig_size2, rm, FloatingPoint(exp_size1, sig_size1, bv)));
      };
      ASSERT_EQ(check(exp_size1 + sig_size1, mk_term, expected), Result::UNSAT)
          << "(_ FloatingPoint " << exp_size1 << " " << sig_size1
          << ") -> (_ FloatingPoint " << exp_size2 << " " << sig_size2 << ")";
    }
  }
}

TEST_F(TestFpWordBlaster, to_fp_from_bv)
{
  for (uint64_t bv_size = 1; bv_size <= 8; ++bv_size)
  {
    for (const auto& [exp_size, sig_size] : formats(11))
    {
      for (bool sign : {false, true})
      {
        auto mk_term = [&](const Node& rm, const Node& b) {
          return d_nm.mk_node(
              sign ? Kind::FP_TO_FP_FROM_SBV : Kind::FP_TO_FP_FROM_UBV,
              {rm, b},
              {exp_size, sig_size});
        };
        auto expected = [&](RoundingMode rm, const BitVector& bv) {
          return d_nm.mk_value(FloatingPoint(exp_size, sig_size, rm, bv, sign));
        };
        ASSERT_EQ(check(bv_size, mk_term, expected), Result::UNSAT)
            << "(_ BitVec " << bv_size << ") -> (_ FloatingPoint " << exp_size
            << " " << sig_size << "), signed: " << sign;
      }
    }
  }
}

TEST_F(TestFpWordBlaster, unary)
{
  for (const auto& format : formats(8))
  {
    for (Kind kind : {Kind::FP_ABS,
                      Kind::FP_NEG,
                      Kind::FP_SQRT,
                      Kind::FP_IS_INF,
                      Kind::FP_IS_NAN,
                      Kind::FP_IS_NEG,
                      Kind::FP_IS_NORMAL,
                      Kind::FP_IS_POS,
                      Kind::FP_IS_SUBNORMAL,
                      Kind::FP_IS_ZERO})
    {
      auto mk_term = [&](const Node& rm, const Node& b) {
        Node x = operand(b, format, 0);
        return kind == Kind::FP_SQRT ? d_nm.mk_node(kind, {rm, x})
                                     : d_nm.mk_node(kind, {x});
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        FloatingPoint x = operand(bv, format, 0);
        switch (kind)
        {
          case Kind::FP_ABS: return d_nm.mk_value(x.fpabs());
          case Kind::FP_NEG: return d_nm.mk_value(x.fpneg());
          case Kind::FP_SQRT: return d_nm.mk_value(x.fpsqrt(rm));
          case Kind::FP_IS_INF: return d_nm.mk_value(x.fpisinf());
          case Kind::FP_IS_NAN: return d_nm.mk_value(x.fpisnan());
          case Kind::FP_IS_NEG: return d_nm.mk_value(x.fpisneg());
          case Kind::FP_IS_NORMAL: return d_nm.mk_value(x.fpisnormal());
          case Kind::FP_IS_POS: return d_nm.mk_value(x.fpispos());
          case Kind::FP_IS_SUBNORMAL: return d_nm.mk_value(x.fpissubnormal());
          default: assert(kind == Kind::FP_IS_ZERO);
        }
        return d_nm.mk_value(x.fpiszero());
      };
      ASSERT_EQ(check(format.first + format.second, mk_term, expected),
                Result::UNSAT)
          << kind << " (_ FloatingPoint " << format.first << " "
          << format.second << ")";
    }
  }
}

TEST_F(TestFpWordBlaster, binary)
{
  for (const auto& format : formats(5))
  {
    for (Kind kind : {Kind::FP_ADD,
                      Kind::FP_SUB,
                      Kind::FP_MUL,
                      Kind::FP_DIV,
                      Kind::FP_REM,
                      Kind::FP_EQUAL,
                      Kind::FP_LT,
                      Kind::FP_LEQ})
    {
      bool has_rm  = kind == Kind::FP_ADD || kind == Kind::FP_SUB
                     || kind == Kind::FP_MUL || kind == Kind::FP_DIV;
      auto mk_term = [&](const Node& rm, const Node& b) {
        Node x = operand(b, format, 0);
        Node y = operand(b, format, 1);
        return has_rm ? d_nm.mk_node(kind, {rm, x, y})
                      : d_nm.mk_node(kind, {x, y});
      };
      auto expected = [&](RoundingMode rm, const BitVector& bv) {
        FloatingPoint x = operand(bv, format, 0);
        FloatingPoint y = operand(bv, format, 1);
        switch (kind)
        {
          case Kind::FP_ADD: return d_nm.mk_value(x.fpadd(rm, y));
          case Kind::FP_SUB: return d_nm.mk_value(x.fpadd(rm, y.fpneg()));
          case Kind::FP_MUL: return d_nm.mk_value(x.fpmul(rm, y));
          case Kind::FP_DIV: return d_nm.mk_value(x.fpdiv(rm, y));
          case Kind::FP_REM: return d_nm.mk_value(x.fprem(y));
          case Kind::FP_EQUAL: return d_nm.mk_value(x.fpeq(y));
          case Kind::FP_LT: return d_nm.mk_value(x.fplt(y));
          default: assert(kind == Kind::FP_LEQ);
        }
        return d_nm.mk_value(x.fple(y));
      };
      ASSERT_EQ(check(2 * (format.first + format.second), mk_term, expected),
                Result::UNSAT)
          << kind << " (_ FloatingPoint " << format.first << " "
          << format.second << ")";
    }
  }
}

TEST_F(TestFpWordBlaster, fma)
{
  for (const auto& format : formats(4))
  {
    auto mk_term = [&](const Node& rm, const Node& b) {
      return d_nm.mk_node(Kind::FP_FMA,
                          {rm,
                           operand(b, format, 0),
                           operand(b, format, 1),
                           operand(b, format, 2)});
    };
    auto expected = [&](RoundingMode rm, const BitVector& bv) {
      return d_nm.mk_value(
          operand(bv, format, 0)
              .fpfma(rm, operand(bv, format, 1), operand(bv, format, 2)));
    };
    ASSERT_EQ(check(3 * (format.first + format.second), mk_term, expected),
              Result::UNSAT)
        << "(_ FloatingPoint " << format.first << " " << format.second << ")";
  }
}

#endif

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
