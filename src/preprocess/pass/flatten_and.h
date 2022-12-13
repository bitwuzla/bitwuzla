#ifndef BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED
#define BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to flatten AND nodes.
 */
class PassFlattenAnd : public PreprocessingPass
{
 public:
  PassFlattenAnd(Env& env) : PreprocessingPass(env) {}

  void apply(AssertionVector& assertions) override;
};

}  // namespace bzla::preprocess::pass
#endif
