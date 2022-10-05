#ifndef BZLA_PREPROCESS_PASS_REWRITE_H_INCLUDED
#define BZLA_PREPROCESS_PASS_REWRITE_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassRewrite : public PreprocessingPass
{
 public:
  PassRewrite(backtrack::AssertionView& assertions, Rewriter& rewriter)
      : PreprocessingPass(assertions, rewriter)
  {
  }

  void apply() override;
};

}  // namespace bzla::preprocess::pass
#endif
