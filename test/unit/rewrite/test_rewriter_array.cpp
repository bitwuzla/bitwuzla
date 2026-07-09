/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterArray : public TestRewriter
{
 protected:
  void SetUp() override
  {
    TestRewriter::SetUp();
    d_arr_type = d_nm.mk_array_type(d_bv4_type, d_bv4_type);
    d_arr      = d_nm.mk_const(d_arr_type, "arr");
    d_idx1     = d_nm.mk_value(BitVector(4, "0001"));
    d_idx2     = d_nm.mk_value(BitVector(4, "0010"));
    d_idx3     = d_nm.mk_value(BitVector(4, "0011"));
  }

  Node store(const Node& a, const Node& i, const Node& v)
  {
    return d_nm.mk_node(Kind::STORE, {a, i, v});
  }
  Node select(const Node& a, const Node& i)
  {
    return d_nm.mk_node(Kind::SELECT, {a, i});
  }

  Type d_arr_type;
  Node d_arr;
  Node d_idx1;
  Node d_idx2;
  Node d_idx3;
};

/* select ------------------------------------------------------------------- */

TEST_F(TestRewriterArray, array_prop_select)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ARRAY_PROP_SELECT;
  //// applies
  // select(store(arr, 2, c), 2) -> c  (matching store index)
  test_rule<kind>(select(store(d_arr, d_idx2, d_bv4_c), d_idx2));
  // select(store(store(arr, 1, c), 2, d), 3) -> select(arr, 3)  (propagate to
  // base array over value store indices that do not match)
  test_rule<kind>(
      select(store(store(d_arr, d_idx1, d_bv4_c), d_idx2, d_bv4_d), d_idx3));
  // select(store(store(arr, i, c), 2, d), 3) -> select(store(arr, i, c), 3)
  // (propagate past the value store index, stop at the symbolic store index)
  test_rule<kind>(
      select(store(store(d_arr, d_bv4_a, d_bv4_c), d_idx2, d_bv4_d), d_idx3));

  //// does not apply
  // symbolic select index
  test_rule_does_not_apply<kind>(
      select(store(d_arr, d_idx2, d_bv4_c), d_bv4_a));
  // top-most store has a symbolic index (nothing propagated yet)
  test_rule_does_not_apply<kind>(
      select(store(d_arr, d_bv4_a, d_bv4_c), d_idx3));
  // select directly on a symbolic array (no store to propagate through)
  test_rule_does_not_apply<kind>(select(d_arr, d_idx3));
}

}  // namespace bzla::test
