#include "gtest/gtest.h"
#include "preprocess/pass/variable_substitution.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassVariableSubstitution : public TestPreprocessingPass
{
 public:
  TestPassVariableSubstitution() : d_btmgr(), d_pass(d_rw, &d_btmgr){};

 protected:
  BacktrackManager d_btmgr;
  preprocess::pass::PassVariableSubstitution d_pass;
};

TEST_F(TestPassVariableSubstitution, subst1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type());
  Node t  = d_nm.mk_const(d_nm.mk_bool_type());
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, t});

  d_pass.register_assertion(eq);
  d_as.push_back(eq);

  auto view = d_as.create_view();
  d_pass.apply(view);

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

  d_pass.register_assertion(eq);
  d_as.push_back(eq);
  d_as.push_back(di);

  auto view = d_as.create_view();
  d_pass.apply(view);

  Node expected = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
  ASSERT_EQ(d_as.size(), 2);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], expected);
  ASSERT_EQ(d_pass.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(di), expected);
}

TEST_F(TestPassVariableSubstitution, subst3)
{
  AssertionStack as(&d_btmgr);
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y  = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node t  = d_nm.mk_const(d_nm.mk_bool_type(), "t");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, t})});

  d_pass.register_assertion(eq);
  as.push_back(eq);
  d_btmgr.push();
  as.push_back(di);

  auto view = as.create_view();
  d_pass.apply(view);

  Node expected = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], d_nm.mk_value(true));
  ASSERT_EQ(as[1], expected);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 1);
  ASSERT_EQ(d_pass.process(as[0]), d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(as[1]), expected);
}

TEST_F(TestPassVariableSubstitution, subst4)
{
  AssertionStack as(&d_btmgr);

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});

  as.push_back(di);
  d_btmgr.push();
  as.push_back(eq);
  as.push_back(x_and_y);

  auto view = as.create_view();
  d_pass.register_assertion(eq);
  d_pass.apply(view);

  ASSERT_EQ(as[0], di);
  // Should not be substituted since x occurs in di at a lower level
  ASSERT_EQ(as[1], eq);
  ASSERT_EQ(as[2], y);
}

TEST_F(TestPassVariableSubstitution, subst5)
{
  AssertionStack as(&d_btmgr);

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});

  as.push_back(di);
  d_btmgr.push();
  d_btmgr.push();
  as.push_back(eq);

  auto view = as.create_view();
  d_pass.register_assertion(eq);
  d_pass.apply(view);

  ASSERT_EQ(as[0], di);
  // Should not be substituted since x occurs in di at a lower level
  ASSERT_EQ(as[1], eq);
}

TEST_F(TestPassVariableSubstitution, subst6)
{
  // TODO: push/pop combination (pop substitution constraints)
}

TEST_F(TestPassVariableSubstitution, cycle1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, x});

  d_as.push_back(eq);
  auto view = d_as.create_view();
  d_pass.register_assertion(eq);
  d_pass.apply(view);
  ASSERT_EQ(d_as[0], eq);
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
  auto view = d_as.create_view();
  d_pass.register_assertion(eq1);
  d_pass.register_assertion(eq2);
  d_pass.apply(view);
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

  d_as.push_back(eq1);
  d_as.push_back(x_and_z);
  d_as.push_back(eq2);
  auto view = d_as.create_view();
  d_pass.register_assertion(eq1);
  d_pass.register_assertion(eq2);
  d_pass.apply(view);
  Node y_and_z = d_nm.mk_node(Kind::AND, {y, z});
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], y_and_z);
  ASSERT_EQ(d_as[2], d_nm.mk_node(Kind::EQUAL, {y, y_and_z}));
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
  auto view = d_as.create_view();
  d_pass.register_assertion(eq1);
  d_pass.register_assertion(eq2);
  d_pass.register_assertion(eq3);
  d_pass.apply(view);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
}

}  // namespace bzla::test
