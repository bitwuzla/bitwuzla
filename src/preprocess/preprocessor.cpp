#include "preprocess/preprocessor.h"

#include "solving_context.h"

namespace bzla::preprocess {

Preprocessor::Preprocessor(SolvingContext& context)
    : d_pass_rewrite(context.assertions(), context.rewriter())
{
}

Result
Preprocessor::preprocess()
{
  d_pass_rewrite.apply();

  return Result::UNKNOWN;
}

}  // namespace bzla::preprocess
