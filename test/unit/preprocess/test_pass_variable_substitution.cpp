#include "gtest/gtest.h"
#include "option/option.h"
#include "preprocess/pass/variable_substitution.h"
#include "preprocess/preprocessor.h"
#include "solving_context.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace preprocess;
using namespace backtrack;
using namespace node;

class TestPassVariableSubstitution : public TestPreprocessingPass
{
 public:
  TestPassVariableSubstitution() : d_btmgr(), d_pass(d_env, &d_btmgr){};

 protected:
  BacktrackManager d_btmgr;
  preprocess::pass::PassVariableSubstitution d_pass;
  option::Options d_options;
};

TEST_F(TestPassVariableSubstitution, subst1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type());
  Node t  = d_nm.mk_const(d_nm.mk_bool_type());
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, t});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as.size(), 1);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(eq), d_nm.mk_value(true));
}

TEST_F(TestPassVariableSubstitution, subst2)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type());
  Node y  = d_nm.mk_const(d_nm.mk_bool_type());
  Node t  = d_nm.mk_const(d_nm.mk_bool_type());
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, t})});

  d_as.push_back(eq);
  d_as.push_back(di);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  Node expected = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
  ASSERT_EQ(d_as.size(), 2);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], expected);
  ASSERT_EQ(d_pass.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(di), expected);
}

TEST_F(TestPassVariableSubstitution, cycle1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, x});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(assertions[0], eq);
}

TEST_F(TestPassVariableSubstitution, cycle2)
{
  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq1     = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});
  Node eq2     = d_nm.mk_node(Kind::EQUAL, {y, x_and_y});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(x_and_y);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], y);
}

TEST_F(TestPassVariableSubstitution, cycle3)
{
  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z       = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node x_and_z = d_nm.mk_node(Kind::AND, {x, z});
  Node eq1     = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2     = d_nm.mk_node(Kind::EQUAL, {y, x_and_z});

  d_as.push_back(x_and_z);
  d_as.push_back(eq2);
  d_as.push_back(eq1);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  Node y_and_z = d_nm.mk_node(Kind::AND, {y, z});
  ASSERT_EQ(d_as[0], x_and_z);
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], d_nm.mk_node(Kind::EQUAL, {x, x_and_z}));
}

TEST_F(TestPassVariableSubstitution, cycle4)
{
  Node x   = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y   = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z   = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node eq1 = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2 = d_nm.mk_node(Kind::EQUAL, {y, z});
  Node eq3 = d_nm.mk_node(Kind::EQUAL, {z, x});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
}

/* --- Incremental tests ---------------------------------------------------- */

TEST_F(TestPassVariableSubstitution, inc1)
{
  SolvingContext ctx(d_options);
  Preprocessor& pp = ctx.preprocessor();

  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y  = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node t  = d_nm.mk_const(d_nm.mk_bool_type(), "t");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, t})});

  ctx.assert_formula(eq);
  ctx.push();
  ctx.assert_formula(di);

  ctx.preprocess();
  auto as = ctx.assertions();

  Node expected = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], d_nm.mk_value(true));
  ASSERT_EQ(as[1], expected);
  ASSERT_EQ(pp.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(pp.process(di), expected);

  ctx.pop();
  ctx.preprocess();
  ASSERT_EQ(as.size(), 1);
  ASSERT_EQ(as[0], d_nm.mk_value(true));
  ASSERT_EQ(pp.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(pp.process(di), expected);
}

TEST_F(TestPassVariableSubstitution, inc2)
{
  GTEST_SKIP();

  SolvingContext ctx(d_options);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_or_y  = d_nm.mk_node(Kind::OR, {x, y});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_or_y);

  ctx.preprocess();
  auto as = ctx.assertions();

  ASSERT_EQ(as[0], di);
  ASSERT_EQ(as[1], eq);
  ASSERT_EQ(as[2], y);
  ASSERT_EQ(pp.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(pp.process(x_or_y), y);

  ctx.pop();
  ctx.preprocess();
  ASSERT_EQ(pp.process(eq), eq);
  ASSERT_EQ(pp.process(x_or_y), ctx.rewriter().rewrite(x_or_y));
}

TEST_F(TestPassVariableSubstitution, inc3)
{
  GTEST_SKIP();

  SolvingContext ctx(d_options);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_or_y  = d_nm.mk_node(Kind::OR, {x, y});
  Node x_or_z  = d_nm.mk_node(Kind::OR, {x, z});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_or_y);
  ctx.push();
  ctx.push();
  ctx.assert_formula(x_or_z);

  ctx.preprocess();
  auto as = ctx.assertions();

  Node expected = d_rw.rewrite(d_nm.mk_node(Kind::OR, {y, z}));
  ASSERT_EQ(as[0], di);
  ASSERT_EQ(as[1], eq);
  ASSERT_EQ(as[2], y);
  ASSERT_EQ(as[3], expected);
  ASSERT_EQ(pp.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(pp.process(x_or_y), y);
  ASSERT_EQ(pp.process(x_or_z), expected);

  ctx.pop();
  ASSERT_EQ(pp.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(pp.process(x_or_y), y);
  ASSERT_EQ(pp.process(x_or_z), expected);

  ctx.pop();
  ctx.pop();
  ASSERT_EQ(pp.process(eq), eq);
  ASSERT_EQ(pp.process(x_or_y), d_rw.rewrite(x_or_y));
  ASSERT_EQ(pp.process(x_or_z), d_rw.rewrite(x_or_z));
}

}  // namespace bzla::test
