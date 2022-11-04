#include "preprocess/pass/rewrite.h"

namespace bzla::preprocess::pass {

void
PassRewrite::apply(AssertionVector& assertions)
{
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    assertions.replace(i, d_rewriter.rewrite(assertions[i]));
  }
}

Node
PassRewrite::process(const Node& term)
{
  return d_rewriter.rewrite(term);
}

}  // namespace bzla::preprocess::pass
