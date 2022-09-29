#include "preprocess/pass/rewrite.h"

namespace bzla::preprocess::pass {

void
PassRewrite::apply()
{
  while (!d_assertions.empty())
  {
    auto [assertion, index] = d_assertions.next_index();
    Node rewritten          = d_rewriter.rewrite(assertion);
    if (rewritten != assertion)
    {
      d_assertions.replace(index, rewritten);
    }
  }
  // TODO: report back when assertion simplifies to false
}

}  // namespace bzla::preprocess::pass
