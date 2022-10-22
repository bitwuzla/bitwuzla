#ifndef BZLA_PREPROCESS_PREPROCESSOR_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSOR_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "preprocess/pass/elim_lambda.h"
#include "preprocess/pass/rewrite.h"
#include "preprocess/pass/variable_substitution.h"
#include "solver/result.h"

namespace bzla {

class SolvingContext;

namespace preprocess {

class Preprocessor
{
 public:
  Preprocessor(SolvingContext& context);

  /** Preprocess current set of assertions. */
  Result preprocess();

  void register_assertion(const Node& assertion);

  /** Preprocess given term. */
  Node process(const Node& term);

 private:
  backtrack::AssertionView& d_assertions;
  /** Preprocessing passes */
  pass::PassRewrite d_pass_rewrite;
  pass::PassElimLambda d_pass_elim_lambda;
  pass::PassVariableSubstitution d_pass_variable_substitution;
};

}  // namespace preprocess
}  // namespace bzla

#endif
