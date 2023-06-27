/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <iostream>

#include "ls/bv/bitvector_domain.h"
#include "node/node_manager.h"
#include "option/option.h"
#include "printer/printer.h"
#include "rng/rng.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using namespace option;

/* -------------------------------------------------------------------------- */

class TestBvPropSolver : public ::testing::Test
{
 protected:
  static constexpr bool TEST_SLOW = false;
#if __APPLE__
  static constexpr uint32_t TEST_NPROPS   = TEST_SLOW ? 200 : 100;
  static constexpr uint32_t TEST_NUPDATES = TEST_SLOW ? 200 : 100;
#else
  static constexpr uint32_t TEST_NPROPS   = TEST_SLOW ? 200 : 100;
  static constexpr uint32_t TEST_NUPDATES = TEST_SLOW ? 200 : 100;
#endif


  void SetUp() override
  {
    d_size = TEST_SLOW ? 4 : 3;
    d_options.bv_solver.set_str("prop");
    d_options.prop_nprops.set(TEST_NPROPS);
    d_options.prop_nupdates.set(TEST_NUPDATES);
    d_options.prop_const_bits.set(true);
    d_options.seed.set(1234);
    d_options.rewrite_level.set(0);
    d_options.pp_contr_ands.set(false);
    d_options.pp_embedded_constr.set(false);
    d_options.pp_flatten_and.set(false);
    d_options.pp_skeleton_preproc.set(false);
    d_options.pp_variable_subst.set(false);
    d_options.dbg_check_model.set(false);
    d_options.dbg_check_unsat_core.set(false);
  }

  /**
   * Helper to generate all combinations of given `bits`.
   * @param size  The bit-vector size.
   * @param bits  The bits to combine.
   * @return The resulting value combinations.
   */
  static std::vector<std::string> generate_all_combinations(
      size_t size, const std::vector<char>& bits);

  /**
   * Helper to generate all combinations of ternary values (combinations of
   * '0', '1', 'x').
   * @param size  The bit-vector size.
   * @return The resulting value combinations.
   */
  static std::vector<std::string> generate_ternary_values(uint32_t size);

  /**
   * Helper to generate all combinations of binary values (combinations of
   * '0', '1').
   * @param size  The bit-vector size.
   * @return The resulting value combinations.
   */
  static std::vector<std::string> generate_binary_values(uint32_t size);

  /**
   * Evaluate binary operation.
   * @param kind The operator kind.
   * @param s0   The value of the first operand.
   * @param s1   The value of the second operand.
   * @return The evaluation result.
   */
  static BitVector eval_binary_op(Kind kind,
                                  const BitVector& s0,
                                  const BitVector& s1);

  /**
   * Helper to create node with bits fixed corresponding to fixed bits in the
   * given domain.
   * @param node The node to fix the bits in.
   * @param d    The domain with the fixed bits information.
   * @return A node representing `node` with bits fixed according to `d`.
   */
  Node fix_bits(const Node& node, const ls::BitVectorDomain& d);

  /**
   * Helper for test_prop().
   * @param d0 The bit-vector domain with const bit information for the first
   *           operand. May not be nullptr.
   * @param d1 The bit-vector domain with const bit information for the second
   *           operand. Ignored if nullptr.
   * @param d2 The bit-vector domain with const bit information for the third
   *           operand. Ignored if nullptr.
   * @param s0 The bit-vector value of the first operand, used to determine
   *           the target value given the values of the other operands.
   * @param s1 The bit-vector value of the second operand, used to determine
   *           the target value given the values of the other operands.
   * @param s2 The bit-vector value of the third operand, used to determine
   *           the target value given the values of the other operands.
   * @param idx0  The first index for indexed operators.
   * @param idx2  The second index for indexed operators.
   */
  void _test_prop_aux(Kind kind,
                      const ls::BitVectorDomain* d0,
                      const ls::BitVectorDomain* d1,
                      const ls::BitVectorDomain* d2,
                      const BitVector* s0,
                      const BitVector* s1,
                      const BitVector* s2,
                      uint32_t idx0 = 0,
                      uint32_t idx1 = 0);

  /**
   * Test BvPropSolver by checking the satisfiability on
   *   (= (bvnot x) (_ bvX d_size))
   *   (= ((_ extract hi lo) x) (_ bvX (hi - lo + 1)))
   *   (= (<op> x y) (_ bvX d_size))
   *   (= (<op> x y) <bool>)
   *   (= (ite x y z) (_ bvX d_size))
   * on all combinations of fixed bits for x, y, z.
   * The propagation-based local search engine must find a solution within
   * a given limit of number of propagations/updates.
   *
   * @param kind The operator kind.
   */
  void test_prop(Kind kind);

  /** The bit-vector size for tests. */
  uint64_t d_size;
  /** The node manager. */
  NodeManager& d_nm = NodeManager::get();
  /** The configured options. */
  Options d_options;
};

/* -------------------------------------------------------------------------- */

std::vector<std::string>
TestBvPropSolver::generate_all_combinations(size_t size,
                                            const std::vector<char>& bits)
{
  size_t num_bits   = bits.size();
  size_t num_values = std::pow(num_bits, size);
  std::vector<size_t> sizes;
  std::vector<std::string> res;

  for (size_t i = 0; i < size; ++i)
  {
    sizes.push_back(num_values / std::pow(num_bits, i + 1));
  }

  // Generate all combinations of given 'bits'.
  for (size_t row = 0; row < num_values; ++row)
  {
    std::string val;
    for (size_t col = 0; col < size; ++col)
    {
      val += bits[(row / sizes[col]) % num_bits];
    }
    res.push_back(val);
  }
  return res;
}

std::vector<std::string>
TestBvPropSolver::generate_ternary_values(uint32_t size)
{
  return generate_all_combinations(size, {'x', '0', '1'});
}

std::vector<std::string>
TestBvPropSolver::generate_binary_values(uint32_t size)
{
  return generate_all_combinations(size, {'0', '1'});
}

Node
TestBvPropSolver::fix_bits(const Node& node, const ls::BitVectorDomain& d)
{
  return d_nm.mk_node(
      Kind::BV_OR,
      {d_nm.mk_node(Kind::BV_AND, {node, d_nm.mk_value(d.hi())}),
       d_nm.mk_value(d.lo())});
}

BitVector
TestBvPropSolver::eval_binary_op(Kind kind,
                                 const BitVector& s0,
                                 const BitVector& s1)
{
  BitVector res;
  switch (kind)
  {
    case Kind::BV_ADD: res = s0.bvadd(s1); break;
    case Kind::BV_AND: res = s0.bvand(s1); break;
    case Kind::BV_CONCAT: res = s0.bvconcat(s1); break;
    case Kind::BV_MUL: res = s0.bvmul(s1); break;
    case Kind::BV_SHL: res = s0.bvshl(s1); break;
    case Kind::BV_SHR: res = s0.bvshr(s1); break;
    case Kind::BV_SLT: res = s0.bvslt(s1); break;
    case Kind::BV_UDIV: res = s0.bvudiv(s1); break;
    case Kind::BV_ULT: res = s0.bvult(s1); break;
    case Kind::BV_UREM: res = s0.bvurem(s1); break;
    case Kind::BV_XOR: res = s0.bvxor(s1); break;
    case Kind::EQUAL: res = s0.bveq(s1); break;
    default: assert(false);
  }
  return res;
}

void
TestBvPropSolver::_test_prop_aux(Kind kind,
                                 const bzla::ls::BitVectorDomain* d0,
                                 const bzla::ls::BitVectorDomain* d1,
                                 const bzla::ls::BitVectorDomain* d2,
                                 const BitVector* s0,
                                 const BitVector* s1,
                                 const BitVector* s2,
                                 uint32_t idx0,
                                 uint32_t idx1)
{
  assert(s0);
  assert(d0);

  BitVector t;
  Node op;

  Type type  = d_nm.mk_bv_type(d_size);
  Type type0 = s2 ? d_nm.mk_bool_type() : type;

  Node const0 = s2 ? d_nm.mk_const(type0) : fix_bits(d_nm.mk_const(type0), *d0);
  Node const1 = s1 ? fix_bits(d_nm.mk_const(type), *d1) : Node();
  Node const2 = s2 ? fix_bits(d_nm.mk_const(type), *d2) : Node();

  SolvingContext ctx = SolvingContext(d_options);

  if (s2)
  {
    // ternary
    assert(kind == Kind::ITE);
    assert(s1);
    op = d_nm.mk_node(kind, {const0, const1, const2});
    t  = BitVector::bvite(*s0, *s1, *s2);
  }
  else if (s1)
  {
    // binary
    op = d_nm.mk_node(kind, {const0, const1});
    t  = eval_binary_op(kind, *s0, *s1);
  }
  else if (kind == Kind::BV_EXTRACT)
  {
    // unary with indices
    op = d_nm.mk_node(kind, {const0}, {idx0, idx1});
    t  = s0->bvextract(idx0, idx1);
  }
  else
  {
    assert(kind == Kind::BV_NOT);
    // unary
    op = d_nm.mk_node(kind, {const0});
    t  = s0->bvnot();
  }

  Node tt;
  if (op.type().is_bool())
  {
    tt = d_nm.mk_value(t.is_true());
  }
  else
  {
    tt = d_nm.mk_value(t);
  }
  Node eq = d_nm.mk_node(Kind::EQUAL, {op, tt});
  ctx.assert_formula(eq);

  Result res = ctx.solve();
  if (res != Result::SAT)
  {
    std::cout << "kind: " << kind << std::endl;
    std::cout << "s0: " << *s0 << std::endl;
    std::cout << "d0: " << *d0 << std::endl;
    if (s1)
    {
      std::cout << "s1: " << *s1 << std::endl;
      std::cout << "d1: " << *d1 << std::endl;
    }
    if (s2)
    {
      std::cout << "s2: " << *s2 << std::endl;
      std::cout << "d2: " << *d2 << std::endl;
    }
    std::cout << "t: " << t << std::endl;
    Printer::print(std::cout, eq);
    std::cout << std::endl;
  }
  assert(res == Result::SAT);
}

void
TestBvPropSolver::test_prop(Kind kind)
{
  std::vector<std::string> tern_values0 = {"x", "0", "1"};
  std::vector<std::string> tern_values  = generate_ternary_values(d_size);
  std::vector<std::string>& s0_values =
      kind == Kind::ITE ? tern_values0 : tern_values;

  for (const std::string& s0_str : s0_values)
  {
    ls::BitVectorDomain d0(s0_str);
    ls::BitVectorDomainGenerator gen_s0(d0);
    do
    {
      BitVector s0 = gen_s0.has_next() ? gen_s0.next() : d0.lo();
      if (kind == Kind::BV_EXTRACT)
      {
        for (uint64_t lo = 0, bw_s0 = s0.size(); lo < bw_s0; ++lo)
        {
          for (uint64_t hi = lo; hi < bw_s0; ++hi)
          {
            uint64_t bw_t = hi - lo + 1;
            for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
            {
              _test_prop_aux(
                  kind, &d0, nullptr, nullptr, &s0, nullptr, nullptr, hi, lo);
            }
          }
        }
      }
      else if (kind == Kind::BV_NOT || kind == Kind::NOT)
      {
        _test_prop_aux(kind, &d0, nullptr, nullptr, &s0, nullptr, nullptr);
      }
      else
      {
        for (const std::string& s1_str : tern_values)
        {
          ls::BitVectorDomain d1(s1_str);
          ls::BitVectorDomainGenerator gen_s1(d1);
          do
          {
            BitVector s1 = gen_s1.has_next() ? gen_s1.next() : d1.lo();
            if (kind == Kind::ITE)
            {
              for (const std::string& s2_str : tern_values)
              {
                ls::BitVectorDomain d2(s2_str);
                ls::BitVectorDomainGenerator gen_s2(d2);
                do
                {
                  BitVector s2 = gen_s2.has_next() ? gen_s2.next() : d2.lo();
                  _test_prop_aux(kind, &d0, &d1, &d2, &s0, &s1, &s2);
                } while (gen_s2.has_next());
              }
            }
            else
            {
              _test_prop_aux(kind, &d0, &d1, nullptr, &s0, &s1, nullptr);
            }
          } while (gen_s1.has_next());
        }
      }
    } while (gen_s0.has_next());
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBvPropSolver, bvadd) { test_prop(Kind::BV_ADD); }

TEST_F(TestBvPropSolver, bvand) { test_prop(Kind::BV_AND); }

TEST_F(TestBvPropSolver, bvconcat) { test_prop(Kind::BV_CONCAT); }

TEST_F(TestBvPropSolver, bvextract) { test_prop(Kind::BV_EXTRACT); }

TEST_F(TestBvPropSolver, bvmul) { test_prop(Kind::BV_MUL); }

TEST_F(TestBvPropSolver, bvnot) { test_prop(Kind::BV_NOT); }

TEST_F(TestBvPropSolver, bvshl) { test_prop(Kind::BV_SHL); }

TEST_F(TestBvPropSolver, bvshr) { test_prop(Kind::BV_SHR); }

TEST_F(TestBvPropSolver, bvudiv) { test_prop(Kind::BV_UDIV); }

TEST_F(TestBvPropSolver, bvult) { test_prop(Kind::BV_ULT); }

TEST_F(TestBvPropSolver, bvslt) { test_prop(Kind::BV_SLT); }

TEST_F(TestBvPropSolver, bvurem) { test_prop(Kind::BV_UREM); }

TEST_F(TestBvPropSolver, bvxor) { test_prop(Kind::BV_XOR); }

TEST_F(TestBvPropSolver, eq) { test_prop(Kind::EQUAL); }

TEST_F(TestBvPropSolver, ite) { test_prop(Kind::ITE); }

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
