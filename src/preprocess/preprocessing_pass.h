#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include "rewrite/rewriter.h"

namespace bzla {

class Env;

namespace backtrack {
class AssertionView;
}

namespace preprocess {

/**
 * Wrapper around AssertionView for manipulating assertions for a given level.
 */
class AssertionVector
{
  friend class Preprocessor;

 public:
  AssertionVector(backtrack::AssertionView& view);

  /**
   * Push back new assertion.
   *
   * @note Sets the d_changed flag to true.
   */
  void push_back(const Node& assertion);

  /** @return The size of the vector. */
  size_t size() const;

  /** @return Assertion at given index. */
  const Node& operator[](std::size_t index) const;

  /**
   * Replace assertion at index i.
   *
   * @note Sets the d_changed flag to true if contents of vector was modified.
   *
   * @param i The index of the assertion to replace.
   * @param assertion The new assertion.
   */
  void replace(size_t index, const Node& assertion);

 private:
  /** Reset d_changed. */
  void reset_changed();

  /** Determines if vector was modified since last reset_changed() call. */
  bool changed() const;

  /** The wrapper assertion view. */
  backtrack::AssertionView& d_view;
  /** The scope level of this set of assertions. */
  size_t d_level;
  /** Start index for assertions. */
  size_t d_begin;
  /** Indicates whether vector was modified. */
  bool d_changed;
};

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
 public:
  PreprocessingPass(Env& env) : d_env(env) {}

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply(AssertionVector& assertions) = 0;

  /** Apply preprocessing pass to given term. */
  virtual Node process(const Node& term) { return term; }

 protected:
  Env& d_env;
};

}  // namespace preprocess
}  // namespace bzla
#endif
