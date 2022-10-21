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
  // TODO: apply until fixed-point
  // fixed-point passes
  d_pass_rewrite.apply(d_assertions);
  d_pass_variable_substitution.apply(d_assertions);

  // one-shot passes
  d_pass_elim_lambda.apply(d_assertions);

  return Result::UNKNOWN;
}

void
Preprocessor::register_assertion(const Node& assertion)
{
  d_pass_variable_substitution.register_assertion(assertion);
}

}  // namespace bzla::preprocess
