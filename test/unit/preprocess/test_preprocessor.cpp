/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "node/node_manager.h"
#include "option/option.h"
#include "preprocess/preprocessor.h"
#include "rewrite/rewriter.h"
#include "sat/sat_solver_factory.h"
#include "solving_context.h"
#include "test/unit/preprocess/test_preprocess_pass.h"
namespace bzla::test {

using namespace preprocess;
using namespace node;

class TestPreprocessor : public ::testing::Test
{
 public:
  TestPreprocessor()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_rw(d_env.rewriter()) {};

 protected:
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  NodeManager d_nm;
  Env d_env;
  Rewriter& d_rw;
};

TEST_F(TestPreprocessor, ctor_dtor)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
}

TEST_F(TestPreprocessor, inc1)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);

  ctx.push();
  ctx.pop();
}

TEST_F(TestPreprocessor, inc2)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);

  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
}

}  // namespace bzla::test
