#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess {

/**
 * Wrapper around std::vector<Node> for storing and manipulating assertions.
 */
class AssertionVector
{
  friend class Preprocessor;

 public:
  /**
   * Push back new assertion.
   *
   * @note Sets the d_changed flag to true.
   */
  void push_back(const Node& assertion)
  {
    d_changed = true;
    d_assertions.push_back(assertion);
  }

  /** @return The size of the vector. */
  size_t size() const { return d_assertions.size(); }

  /** @return Assertion at given position. */
  const Node& operator[](std::size_t pos) const { return d_assertions[pos]; }

  /**
   * Replace assertion at index i.
   *
   * @note Sets the d_changed flag to true if contents of vector changed.
   *
   * @param i The index of the assertion to replace.
   * @param assertion The new assertion.
   */
  void replace(size_t i, const Node& assertion)
  {
    if (d_assertions[i] != assertion)
    {
      d_changed       = true;
      d_assertions[i] = assertion;
    }
  }

 private:
  /** Reset d_changed. */
  void reset_changed() { d_changed = false; }

  /** Determines if vector was changed since last reset_changed() call. */
  bool changed() const { return d_changed; }

  bool d_changed = false;
  std::vector<Node> d_assertions;
};

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
 public:
  PreprocessingPass(Rewriter& rewriter) : d_rewriter(rewriter) {}

  /** Apply preprocessing pass to the current set of assertions. */
  virtual void apply(AssertionVector& assertions) = 0;

  /** Apply preprocessing pass to given term. */
  virtual Node process(const Node& term) { return term; }

 protected:
  Rewriter& d_rewriter;
};

}  // namespace bzla::preprocess
#endif
