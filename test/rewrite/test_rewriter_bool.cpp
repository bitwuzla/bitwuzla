#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "rewrite/rewriter.h"
#include "rewrite/rewrites_bool.h"
#include "test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBool : public TestRewriter
{
  void SetUp() override {}

 protected:
  void test_elim_rule_bool(Kind kind)
  {
    test_elim_rule(kind, d_nm.mk_bool_type());
  }

  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
};

TEST_F(TestRewriterBool, bool_and_eval)
{
  // applies
  Node and0 =
      d_nm.mk_node(Kind::AND, {d_nm.mk_value(true), d_nm.mk_value(true)});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(and0));

  Node and1 = d_nm.mk_node(Kind::AND, {and0, d_nm.mk_value(false)});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(and1));
  // empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(and1));
  // does not apply
  Node and2 = d_nm.mk_node(
      Kind::AND, {d_nm.mk_const(d_nm.mk_bool_type()), d_nm.mk_value(false)});
  ASSERT_EQ(
      and2,
      RewriteRule<RewriteRuleKind::AND_EVAL>::apply(d_rewriter, and2).first);
}

TEST_F(TestRewriterBool, bool_not_eval)
{
  // applies
  Node not0 = d_nm.mk_node(Kind::NOT, {d_nm.mk_value(false)});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(not0));

  Node not1 = d_nm.mk_node(Kind::NOT, {not0});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(not1));
  // empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(not1));
  // does not apply
  Node not2 = d_nm.mk_node(Kind::NOT, {d_nm.mk_const(d_nm.mk_bool_type())});
  ASSERT_EQ(
      not2,
      RewriteRule<RewriteRuleKind::NOT_EVAL>::apply(d_rewriter, not2).first);
}

TEST_F(TestRewriterBool, bool_or_elim) { test_elim_rule_bool(Kind::OR); }

}  // namespace bzla::test

