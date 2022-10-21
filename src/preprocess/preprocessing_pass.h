#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess {

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
 public:
  PreprocessingPass(Rewriter& rewriter) : d_rewriter(rewriter) {}

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply(backtrack::AssertionView& assertions) = 0;

 protected:
  Rewriter& d_rewriter;
};

}  // namespace bzla::preprocess
#endif
