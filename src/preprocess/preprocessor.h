#ifndef BZLA_PREPROCESS_PREPROCESSOR_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSOR_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "preprocess/pass/elim_lambda.h"
#include "preprocess/pass/rewrite.h"
#include "solver/result.h"

namespace bzla {

class SolvingContext;

namespace preprocess {

class Preprocessor
{
 public:
  Preprocessor(SolvingContext& context);

  Result preprocess();

 private:
  /** Preprocessing passes */
  pass::PassRewrite d_pass_rewrite;
  pass::PassElimLambda d_pass_elim_lambda;
};

}  // namespace preprocess
}  // namespace bzla

#endif
