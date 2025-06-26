/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "node/node_utils.h"
#include "preprocess/pass/elim_lambda.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassElimLambda : public TestPreprocessingPass
{
 public:
  TestPassElimLambda() : d_env(d_nm), d_pass(d_env, &d_bm) {};

 protected:
  Env d_env;
  preprocess::pass::PassElimLambda d_pass;
};

TEST_F(TestPassElimLambda, reduce1)
{
  auto bool_type = d_nm.mk_bool_type();
  auto x1        = d_nm.mk_var(bool_type, "x1");
  auto x2        = d_nm.mk_var(bool_type, "x2");
  auto b         = d_nm.mk_node(Kind::XOR, {x1, x2});
  auto l         = utils::mk_nary(d_nm, Kind::LAMBDA, {x1, x2, b});

  auto a1 = d_nm.mk_const(bool_type, "a1");
  auto a2 = d_nm.mk_const(bool_type, "a2");

  d_as.push_back(d_nm.mk_node(Kind::APPLY, {l, a1, a2}));

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0], d_nm.mk_node(Kind::XOR, {a1, a2}));
}

TEST_F(TestPassElimLambda, reduce2)
{
  auto bool_type = d_nm.mk_bool_type();
  auto x1        = d_nm.mk_var(bool_type, "x1");
  auto x2        = d_nm.mk_var(bool_type, "x2");
  auto b         = d_nm.mk_node(Kind::XOR, {x1, x2});
  auto l         = utils::mk_nary(d_nm, Kind::LAMBDA, {x1, x2, b});

  auto a1 = d_nm.mk_const(bool_type, "a1");
  auto a2 = d_nm.mk_const(bool_type, "a2");
  auto b1 = d_nm.mk_const(bool_type, "b1");
  auto b2 = d_nm.mk_const(bool_type, "b2");

  d_as.push_back(d_nm.mk_node(Kind::APPLY, {l, a1, a2}));
  d_as.push_back(d_nm.mk_node(Kind::APPLY, {l, b1, b2}));
  d_as.push_back(d_nm.mk_node(Kind::APPLY, {l, a1, a2}));

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0], d_nm.mk_node(Kind::XOR, {a1, a2}));
  ASSERT_EQ(d_as[1], d_nm.mk_node(Kind::XOR, {b1, b2}));
  ASSERT_EQ(d_as[2], d_nm.mk_node(Kind::XOR, {a1, a2}));
}

TEST_F(TestPassElimLambda, reduce3)
{
  auto bool_type = d_nm.mk_bool_type();
  auto x1        = d_nm.mk_var(bool_type, "x1");
  auto x2        = d_nm.mk_var(bool_type, "x2");
  auto b         = d_nm.mk_node(Kind::XOR, {x1, x2});
  auto l         = utils::mk_nary(d_nm, Kind::LAMBDA, {x1, x2, b});

  auto a1 = d_nm.mk_const(bool_type, "a1");
  auto a2 = d_nm.mk_const(bool_type, "a2");
  auto b1 = d_nm.mk_const(bool_type, "b1");
  auto b2 = d_nm.mk_const(bool_type, "b2");

  d_as.push_back(d_nm.mk_node(Kind::OR,
                              {
                                  d_nm.mk_node(Kind::APPLY, {l, a1, a2}),
                                  d_nm.mk_node(Kind::APPLY, {l, b1, b2}),
                              }));

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0],
            d_nm.mk_node(Kind::OR,
                         {d_nm.mk_node(Kind::XOR, {a1, a2}),
                          d_nm.mk_node(Kind::XOR, {b1, b2})}));
}

TEST_F(TestPassElimLambda, reduce4)
{
  auto bool_type = d_nm.mk_bool_type();
  auto x1        = d_nm.mk_var(bool_type, "x1");
  auto x2        = d_nm.mk_var(bool_type, "x2");
  auto b         = d_nm.mk_node(Kind::XOR, {x1, x2});
  auto l         = utils::mk_nary(d_nm, Kind::LAMBDA, {x1, x2, b});

  auto a1 = d_nm.mk_const(bool_type, "a1");
  auto b1 = d_nm.mk_const(bool_type, "b1");
  auto b2 = d_nm.mk_const(bool_type, "b2");

  d_as.push_back(
      d_nm.mk_node(Kind::APPLY, {l, a1, d_nm.mk_node(Kind::APPLY, {l, b1, b2})})

  );

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0],
            d_nm.mk_node(Kind::XOR, {a1, d_nm.mk_node(Kind::XOR, {b1, b2})}));
}

TEST_F(TestPassElimLambda, nested1)
{
  auto bool_type = d_nm.mk_bool_type();
  auto x1        = d_nm.mk_var(bool_type, "x1");
  auto x2        = d_nm.mk_var(bool_type, "x2");
  auto x3        = d_nm.mk_var(bool_type, "x3");
  auto x4        = d_nm.mk_var(bool_type, "x4");
  auto b1        = d_nm.mk_node(Kind::OR, {x1, x2});
  auto l1        = utils::mk_nary(d_nm, Kind::LAMBDA, {x1, x2, b1});
  auto b2 =
      d_nm.mk_node(Kind::XOR, {x3, d_nm.mk_node(Kind::APPLY, {l1, x3, x4})});
  auto l2 = utils::mk_nary(d_nm, Kind::LAMBDA, {x3, x4, b2});

  auto a1 = d_nm.mk_const(bool_type, "a1");
  auto a2 = d_nm.mk_const(bool_type, "a2");
  d_as.push_back(d_nm.mk_node(Kind::APPLY, {l2, a1, a2}));

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0],
            d_nm.mk_node(Kind::XOR, {a1, d_nm.mk_node(Kind::OR, {a1, a2})}));
}

// apply with apply as argument

}  // namespace bzla::test
