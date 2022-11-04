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
  TestPreprocessor() : d_nm(NodeManager::get()){};

 protected:
  NodeManager& d_nm;
  Rewriter d_rw;
  option::Options d_options;
};

TEST_F(TestPreprocessor, ctor_dtor)
{
  SolvingContext ctx(d_options);
  Preprocessor pp(ctx);
}

TEST_F(TestPreprocessor, inc1)
{
  SolvingContext ctx(d_options);
  Preprocessor pp(ctx);

  ctx.push();
  ctx.pop();
}

TEST_F(TestPreprocessor, inc2)
{
  SolvingContext ctx(d_options);
  Preprocessor pp(ctx);

  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
  ctx.push();
  ctx.pop();
}

}  // namespace bzla::test
