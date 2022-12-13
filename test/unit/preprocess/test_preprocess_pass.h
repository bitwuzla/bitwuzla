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
  TestPreprocessingPass() : d_nm(NodeManager::get()), d_rw(d_env.rewriter()){};

 protected:
  NodeManager& d_nm;
  Env d_env;
  Rewriter& d_rw;
  AssertionStack d_as;
};

}
