#include "preprocess/preprocessor.h"

#include "solving_context.h"

namespace bzla::preprocess {

Preprocessor::Preprocessor(SolvingContext& context)
    : d_pass_rewrite(context.assertions(), context.rewriter()),
      d_pass_elim_lambda(context.assertions(), context.rewriter())
{
}

Result
Preprocessor::preprocess()
{
  d_pass_rewrite.apply();
  d_pass_elim_lambda.apply();

  return Result::UNKNOWN;
}

}  // namespace bzla::preprocess
