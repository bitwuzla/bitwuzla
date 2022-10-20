#include "preprocess/preprocessor.h"

#include "solving_context.h"

namespace bzla::preprocess {

Preprocessor::Preprocessor(SolvingContext& context)
    : d_assertions(context.assertions()),
      d_pass_rewrite(context.rewriter()),
      d_pass_elim_lambda(context.rewriter()),
      d_pass_variable_substitution(context.rewriter(), context.backtrack_mgr())
{
}

Result
Preprocessor::preprocess()
{
  std::vector<Node> orig_assertions;
  std::vector<std::pair<Node, size_t>> assertions;
  while (!d_assertions.empty())
  {
    assertions.push_back(d_assertions.next_level());
    orig_assertions.push_back(assertions.back().first);
  }

  // TODO: apply until fixed-point
  // fixed-point passes
  d_pass_rewrite.apply(assertions);

  // one-shot passes
  d_pass_elim_lambda.apply(assertions);

  for (size_t i = 0, size = orig_assertions.size(); i < size; ++i)
  {
    d_assertions.replace(orig_assertions[i], assertions[i].first);
  }

  return Result::UNKNOWN;
}

}  // namespace bzla::preprocess
