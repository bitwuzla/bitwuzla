#include "preprocess/preprocessor.h"

#include "solving_context.h"

namespace bzla::preprocess {

Preprocessor::Preprocessor(SolvingContext& context)
    : d_assertions(context.assertions()),
      d_global_backtrack_mgr(*context.backtrack_mgr()),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_pass_rewrite(context.rewriter()),
      d_pass_elim_lambda(context.rewriter()),
      d_pass_variable_substitution(context.rewriter(), &d_backtrack_mgr),
      d_pass_flatten_and(context.rewriter())
{
}

Result
Preprocessor::preprocess()
{
  // No assertions to process, return.
  if (d_assertions.empty())
  {
    return Result::UNKNOWN;
  }

  // Process assertions by level
  while (!d_assertions.empty())
  {
    size_t level = d_assertions.level(d_assertions.begin());

    // Sync backtrack manager to level. This is required if there are levels
    // that do not contain any assertions.
    sync_scope(level);

    // Create vector for current level
    AssertionVector assertions(d_assertions);
    assert(assertions.d_level == level);

    // Apply preprocessing passes until fixed-point
    apply(assertions);

    // Advance assertions to next level
    d_assertions.set_index(d_assertions.begin() + assertions.size());
  }
  assert(d_assertions.empty());

  // Sync backtrack manager to level. This is required if there are levels
  // that do not contain any assertions.
  sync_scope(d_global_backtrack_mgr.num_levels());

  return Result::UNKNOWN;
}

Node
Preprocessor::process(const Node& term)
{
  // TODO: add more passes
  Node processed = d_pass_variable_substitution.process(term);
  return d_pass_rewrite.process(processed);
}

/* --- Preprocessor private ------------------------------------------------- */

void
Preprocessor::apply(AssertionVector& assertions)
{
  if (assertions.size() == 0)
  {
    return;
  }

  // one-shot passes
  d_pass_elim_lambda.apply(assertions);

  // fixed-point passes
  do
  {
    // Reset changed flag.
    assertions.reset_changed();

    d_pass_flatten_and.apply(assertions);
    d_pass_rewrite.apply(assertions);
    d_pass_variable_substitution.apply(assertions);
  } while (assertions.changed());
}

void
Preprocessor::sync_scope(size_t level)
{
  while (d_backtrack_mgr.num_levels() < level)
  {
    d_backtrack_mgr.push();
  }
}

}  // namespace bzla::preprocess
