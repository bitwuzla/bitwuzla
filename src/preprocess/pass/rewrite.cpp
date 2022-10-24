#include "preprocess/pass/rewrite.h"

namespace bzla::preprocess::pass {

void
PassRewrite::apply(backtrack::AssertionView& assertions)
{
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i].first;
    assertions.replace(assertion, d_rewriter.rewrite(assertion));
  }
}

Node
PassRewrite::process(const Node& term)
{
  return d_rewriter.rewrite(term);
}

}  // namespace bzla::preprocess::pass
