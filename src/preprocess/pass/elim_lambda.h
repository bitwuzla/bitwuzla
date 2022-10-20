#ifndef BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED
#define BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassElimLambda : public PreprocessingPass
{
 public:
  PassElimLambda(Rewriter& rewriter) : PreprocessingPass(rewriter) {}

  void apply(std::vector<std::pair<Node, size_t>>& assertions) override;
};

}  // namespace bzla::preprocess::pass
#endif
