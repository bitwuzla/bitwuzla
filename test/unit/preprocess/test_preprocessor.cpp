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
#include "node/node_manager.h"
#include "option/option.h"
#include "preprocess/preprocessor.h"
#include "rewrite/rewriter.h"
#include "solving_context.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace preprocess;
using namespace node;

class TestPreprocessor : public ::testing::Test
{
 public:
  TestPreprocessor() : d_nm(NodeManager::get()), d_rw(d_env.rewriter()){};

 protected:
  NodeManager& d_nm;
  Env d_env;
  Rewriter& d_rw;
  option::Options d_options;
};

TEST_F(TestPreprocessor, ctor_dtor)
{
  SolvingContext ctx(d_options);
}

TEST_F(TestPreprocessor, inc1)
{
  SolvingContext ctx(d_options);

  ctx.push();
  ctx.pop();
}

TEST_F(TestPreprocessor, inc2)
{
  SolvingContext ctx(d_options);

  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
}

}  // namespace bzla::test
