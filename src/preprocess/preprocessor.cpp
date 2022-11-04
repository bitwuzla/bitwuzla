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

  // Preprocess assertions by scope level.
  size_t cur_level = d_assertions[0].second;  // current level
  sync_scope(cur_level);
  AssertionVector assertions;
  std::vector<size_t> indices;
  size_t index = 0;
  while (!d_assertions.empty())
  {
    const auto& [assertion, level] = d_assertions.next_level();
    if (level != cur_level)
    {
      // Apply preprocessing passes until fixed-point
      apply(assertions);
      // Update d_assertions and clear assertions and indices
      update(cur_level, assertions, indices);
      // Process next level
      cur_level = level;
      sync_scope(cur_level);
    }
    assertions.push_back(assertion);
    indices.push_back(index++);
  }
  // Process current scope
  apply(assertions);
  update(cur_level, assertions, indices);
  sync_scope(d_global_backtrack_mgr.num_levels());
  // After preprocessing is done, both backtrack managers have to be in sync.
  assert(d_backtrack_mgr.num_levels() == d_global_backtrack_mgr.num_levels());

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
  assertions.reset();
  indices.clear();
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
