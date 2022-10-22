#include "preprocess/pass/rewrite.h"

namespace bzla::preprocess::pass {

void
PassRewrite::apply(backtrack::AssertionView& assertions)
{
  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i].first;
    Node rewritten        = d_rewriter.rewrite(assertion);
    if (rewritten != assertion)
    {
      assertions.replace(assertion, rewritten);
    }
  }
}

Node
PassRewrite::process(const Node& term)
{
  return d_rewriter.rewrite(term);
}

}  // namespace bzla::preprocess::pass
