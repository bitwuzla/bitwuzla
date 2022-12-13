#include "preprocess/pass/rewrite.h"

#include "env.h"

namespace bzla::preprocess::pass {

void
PassRewrite::apply(AssertionVector& assertions)
{
  auto& rw = d_env.rewriter();
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    assertions.replace(i, rw.rewrite(assertions[i]));
  }
}

Node
PassRewrite::process(const Node& term)
{
  return d_env.rewriter().rewrite(term);
}

}  // namespace bzla::preprocess::pass
