/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_manager.h"
#include "solving_context.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBvRotate : public TestRewriter
{
 protected:
  void test_rot(uint32_t size, uint32_t nbits, bool left)
  {
    Kind kind, kindi;
    if (left)
    {
      kind  = Kind::BV_ROL;
      kindi = Kind::BV_ROLI;
    }
    else
    {
      kind  = Kind::BV_ROR;
      kindi = Kind::BV_RORI;
    }

    NodeManager& nm = NodeManager::get();
    Node const0     = nm.mk_const(nm.mk_bv_type(size));
    Node roti       = nm.mk_node(kindi, {const0}, {nbits});
    Node rot0       = nm.mk_node(
        kind, {const0, nm.mk_value(BitVector::from_ui(size, nbits))});
    option::Options d_options;
    SolvingContext ctx = SolvingContext(d_options);
    ctx.assert_formula(nm.mk_node(Kind::DISTINCT, {rot0, roti}));
    ASSERT_EQ(ctx.solve(), Result::UNSAT);
  }
};

TEST_F(TestRewriterBvRotate, rol_1_0) { test_rot(1, 0, true); }

TEST_F(TestRewriterBvRotate, rol_2_0) { test_rot(2, 0, true); }

TEST_F(TestRewriterBvRotate, rol_3_0) { test_rot(3, 0, true); }

TEST_F(TestRewriterBvRotate, rol_5_0) { test_rot(5, 0, true); }

TEST_F(TestRewriterBvRotate, rol_12_0) { test_rot(12, 0, true); }

TEST_F(TestRewriterBvRotate, rol_32_0) { test_rot(32, 0, true); }

TEST_F(TestRewriterBvRotate, rol_1_1) { test_rot(1, 1, true); }

TEST_F(TestRewriterBvRotate, rol_2_1) { test_rot(2, 1, true); }

TEST_F(TestRewriterBvRotate, rol_3_1) { test_rot(3, 1, true); }

TEST_F(TestRewriterBvRotate, rol_5_1) { test_rot(5, 1, true); }

TEST_F(TestRewriterBvRotate, rol_12_1) { test_rot(12, 1, true); }

TEST_F(TestRewriterBvRotate, rol_32_1) { test_rot(32, 1, true); }

TEST_F(TestRewriterBvRotate, rol_2_2) { test_rot(2, 2, true); }

TEST_F(TestRewriterBvRotate, rol_3_3) { test_rot(3, 3, true); }

TEST_F(TestRewriterBvRotate, rol_5_5) { test_rot(5, 5, true); }

TEST_F(TestRewriterBvRotate, rol_12_12) { test_rot(12, 12, true); }

TEST_F(TestRewriterBvRotate, rol_32_32) { test_rot(32, 32, true); }

TEST_F(TestRewriterBvRotate, ror_1_0) { test_rot(1, 0, false); }

TEST_F(TestRewriterBvRotate, ror_2_0) { test_rot(2, 0, false); }

TEST_F(TestRewriterBvRotate, ror_3_0) { test_rot(3, 0, false); }

TEST_F(TestRewriterBvRotate, ror_5_0) { test_rot(5, 0, false); }

TEST_F(TestRewriterBvRotate, ror_12_0) { test_rot(12, 0, false); }

TEST_F(TestRewriterBvRotate, ror_32_0) { test_rot(32, 0, false); }

TEST_F(TestRewriterBvRotate, ror_1_1) { test_rot(1, 1, false); }

TEST_F(TestRewriterBvRotate, ror_2_1) { test_rot(2, 1, false); }

TEST_F(TestRewriterBvRotate, ror_3_1) { test_rot(3, 1, false); }

TEST_F(TestRewriterBvRotate, ror_5_1) { test_rot(5, 1, false); }

TEST_F(TestRewriterBvRotate, ror_12_1) { test_rot(12, 1, false); }

TEST_F(TestRewriterBvRotate, ror_32_1) { test_rot(32, 1, false); }

TEST_F(TestRewriterBvRotate, ror_2_2) { test_rot(2, 2, false); }

TEST_F(TestRewriterBvRotate, ror_3_3) { test_rot(3, 3, false); }

TEST_F(TestRewriterBvRotate, ror_5_5) { test_rot(5, 5, false); }

TEST_F(TestRewriterBvRotate, ror_12_12) { test_rot(12, 12, false); }

TEST_F(TestRewriterBvRotate, ror_32_32) { test_rot(32, 32, false); }

}  // namespace bzla::test
