#include "preprocess/preprocessor.h"

#include "solving_context.h"

namespace bzla::preprocess {

Preprocessor::Preprocessor(SolvingContext& context)
    : d_pop_callback(context.backtrack_mgr(), *this),
      d_assertions(context.assertions()),
      d_global_backtrack_mgr(*context.backtrack_mgr()),
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

  // Process assertions by scope level.
  //
  // Note: update() may insert new assertions at the end of the current level.
  //       As a result, d_assertions.end() grows and .
  for (size_t i = d_assertions.begin(); i < d_assertions.end();)
  {
    // Collect all assertions of current level
    size_t level = d_assertions.level(i);
    std::vector<size_t> indices;
    AssertionVector assertions;
    for (size_t end = d_assertions.end();
         i < end && d_assertions.level(i) == level;
         ++i)
    {
      indices.push_back(i);
      assertions.push_back(d_assertions[i]);
    }

    // Sync backtrack manager to level. This is required if there are levels
    // that do not contain any assertions.
    sync_scope(level);

    // Apply preprocessing passes until fixed-point
    apply(assertions);

    // Update d_assertions and add new assertions to current level
    update(level, assertions, indices);
    assert(level == d_backtrack_mgr.num_levels());

    // New assertions added for this level
    i += assertions.size() - indices.size();
  }
  // Sync backtrack manager to level. This is required if there are levels
  // that do not contain any assertions.
  sync_scope(d_global_backtrack_mgr.num_levels());

  // Mark assertions as processed.
  d_assertions.set_index(d_assertions.end());

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
Preprocessor::update(size_t level,
                     AssertionVector& assertions,
                     std::vector<size_t>& indices)
{
  // Update existing assertions
  for (size_t i = 0, size = indices.size(); i < size; ++i)
  {
    d_assertions.replace(indices[i], assertions[i]);
  }
  // Add new assertions
  for (size_t i = indices.size(), size = assertions.size(); i < size; ++i)
  {
    d_assertions.insert_at_level(level, assertions[i]);
  }
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
