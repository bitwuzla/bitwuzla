/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
  TestPassVariableSubstitution() : d_pass(d_env, &d_bm)
  {
    d_options.rewrite_level.set(0);
    d_options.pp_embedded_constr.set(false);
    d_options.pp_flatten_and.set(false);
    d_options.pp_skeleton_preproc.set(false);
  };

 protected:
  Env d_env;
  preprocess::pass::PassVariableSubstitution d_pass;
};

TEST_F(TestPassVariableSubstitution, subst1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node t  = d_nm.mk_const(d_nm.mk_bool_type(), "t");
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
  ASSERT_EQ(d_as[0], y_and_z);
  ASSERT_EQ(d_as[1], d_nm.mk_node(Kind::EQUAL, {y, y_and_z}));
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
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

TEST_F(TestPassVariableSubstitution, cycle5)
{
  Node x   = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y   = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z   = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node eq1 = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2 = d_nm.mk_node(Kind::EQUAL, {y, z});
  Node eq3 = d_nm.mk_node(Kind::EQUAL, {z, x});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));

  d_as.push_back(eq3);
  preprocess::AssertionVector assertions2(d_as.view());
  d_pass.apply(assertions);
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

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_t = d_nm.invert_node(t);
    ASSERT_EQ(as.size(), 2);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(as[1], d_nm.mk_node(Kind::EQUAL, {y, not_t}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_t, not_t}));
    ASSERT_EQ(pp.process(di),
              d_nm.invert_node(d_nm.mk_node(Kind::EQUAL, {not_t, t})));

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di),
              d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})}));
  }
  else
  {
    Node expected =
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
    ASSERT_EQ(as.size(), 2);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(as[1], expected);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di), expected);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di), expected);
  }
}

TEST_F(TestPassVariableSubstitution, inc2)
{
  SolvingContext ctx(d_options);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_and_y);

  ctx.preprocess();
  auto as = ctx.assertions();

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_y       = d_nm.invert_node(y);
    Node not_y_and_y = d_nm.mk_node(Kind::AND, {not_y, y});
    ASSERT_EQ(as[0], d_nm.invert_node(d_nm.mk_node(Kind::EQUAL, {not_y, y})));
    ASSERT_EQ(as[1], d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(as[2], not_y_and_y);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
  }
  else
  {
    Node y_and_y = d_nm.mk_node(Kind::AND, {y, y});
    ASSERT_EQ(as[0], di);
    ASSERT_EQ(as[1], eq);
    ASSERT_EQ(as[2], y_and_y);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(pp.process(eq), eq);
    ASSERT_EQ(pp.process(x_and_y), x_and_y);
  }
}

TEST_F(TestPassVariableSubstitution, inc3)
{
  SolvingContext ctx(d_options);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});
  Node x_and_z = d_nm.mk_node(Kind::AND, {x, z});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_and_y);
  ctx.push();
  ctx.push();
  ctx.assert_formula(x_and_z);

  ctx.preprocess();
  auto as = ctx.assertions();

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_y       = d_nm.invert_node(y);
    Node not_y_eq_y  = d_nm.mk_node(Kind::EQUAL, {not_y, y});
    Node not_y_and_z = d_nm.mk_node(Kind::AND, {not_y, z});
    Node not_y_and_y = d_nm.mk_node(Kind::AND, {not_y, y});
    ASSERT_EQ(as[0], d_nm.invert_node(not_y_eq_y));
    ASSERT_EQ(as[1], not_y_eq_y);
    ASSERT_EQ(as[2], not_y_and_y);
    ASSERT_EQ(as[3], not_y_and_z);
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);

    ctx.pop();
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);

    ctx.pop();
    ctx.pop();
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);
  }
  else
  {
    Node y_and_z = d_nm.mk_node(Kind::AND, {y, z});
    Node y_and_y = d_nm.mk_node(Kind::AND, {y, y});
    ASSERT_EQ(as[0], di);
    ASSERT_EQ(as[1], eq);
    ASSERT_EQ(as[2], y_and_y);
    ASSERT_EQ(as[3], y_and_z);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);
    ASSERT_EQ(pp.process(x_and_z), y_and_z);

    ctx.pop();
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);
    ASSERT_EQ(pp.process(x_and_z), y_and_z);

    ctx.pop();
    ctx.pop();
    ASSERT_EQ(pp.process(eq), eq);
    ASSERT_EQ(pp.process(x_and_y), x_and_y);
    ASSERT_EQ(pp.process(x_and_z), x_and_z);
  }
}

}  // namespace bzla::test
