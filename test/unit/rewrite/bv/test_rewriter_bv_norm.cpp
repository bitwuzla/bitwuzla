#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBvNorm : public TestRewriter
{
};

/* bvadd -------------------------------------------------------------------- */

TEST_F(TestRewriterBvNorm, bv_add_norm_mul_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_NORM_MUL_CONST;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_bv4_b})),
       d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_zero}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_zero})),
       d_bv4_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_bv4_a, d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_bv4_a, d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_bv4_a,
       d_nm.mk_node(Kind::BV_NOT,
                    {d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_bv4_b})})}));
}

}  // namespace bzla::test
