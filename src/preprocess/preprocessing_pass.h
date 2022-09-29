#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include "backtrack/assertion_stack.h"

namespace bzla::preprocess {

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
 public:
  PreprocessingPass(backtrack::AssertionView& assertions)
      : d_assertions(assertions)
  {
  }

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply() = 0;

 protected:
  backtrack::AssertionView& d_assertions;
};

}  // namespace bzla::preprocess
#endif
