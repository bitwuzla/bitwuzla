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
  PreprocessingPass(backtrack::AssertionView& assertions, Rewriter& rewriter)
      : d_assertions(assertions), d_rewriter(rewriter)
  {
  }

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply() = 0;

 protected:
  backtrack::AssertionView& d_assertions;
  Rewriter& d_rewriter;
};

}  // namespace bzla::preprocess
#endif
