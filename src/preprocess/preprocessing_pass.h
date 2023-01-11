#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include "node/node.h"

namespace bzla {

class Env;

namespace util {
  class Logger;
}

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
   * @note Increments d_changed.
   */
  void push_back(const Node& assertion);

  /** @return The size of the vector. */
  size_t size() const;

  /** @return Assertion at given index. */
  const Node& operator[](std::size_t index) const;

  /**
   * Replace assertion at index i.
   *
   * @note Increments d_changed if contents of vector was modified.
   *
   * @param i The index of the assertion to replace.
   * @param assertion The new assertion.
   */
  void replace(size_t index, const Node& assertion);

 private:
  /** Reset d_changed. */
  void reset_modified();

  /** @return The number of changed/added assertions since the last reset. */
  size_t num_modified() const;

  /** Determines if vector was modified since the last reset. */
  bool modified() const;

  /** The wrapper assertion view. */
  backtrack::AssertionView& d_view;
  /** The scope level of this set of assertions. */
  size_t d_level;
  /** Start index for assertions. */
  size_t d_begin;
  /** Number of modified (changed, added) assertions since last reset. */
  size_t d_modified;
};

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
 public:
  PreprocessingPass(Env& env);

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply(AssertionVector& assertions) = 0;

  /** Apply preprocessing pass to given term. */
  virtual Node process(const Node& term) { return term; }

 protected:
  Env& d_env;
  util::Logger& d_logger;
};

}  // namespace preprocess
}  // namespace bzla
#endif
