/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/assertion_stack.h"
#include "env.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "rewrite/rewriter.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPreprocessingPass : public ::testing::Test
{
 public:
  TestPreprocessingPass() : d_nm(NodeManager::get()) {}

 protected:
  NodeManager& d_nm;
  option::Options d_options;
  backtrack::BacktrackManager d_bm;
  AssertionStack d_as;
};

}
