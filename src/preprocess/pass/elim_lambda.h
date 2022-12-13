#ifndef BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED
#define BZLA_PREPROCESS_PASS_ELIM_LAMBDA_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to eliminate applications on lambda nodes.
 */
class PassElimLambda : public PreprocessingPass
{
 public:
  PassElimLambda(Env& env) : PreprocessingPass(env) {}

  void apply(AssertionVector& assertions) override;

  Node process(const Node& term) override;

 private:
  Node reduce(const Node& node) const;

  std::unordered_map<Node, Node> d_cache;
};

}  // namespace bzla::preprocess::pass
#endif
