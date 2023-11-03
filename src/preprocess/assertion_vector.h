/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_ASSERTION_VECTOR_H_INCLUDED
#define BZLA_PREPROCESS_ASSERTION_VECTOR_H_INCLUDED

#include "node/node.h"
#include "preprocess/assertion_tracker.h"

namespace bzla {

namespace backtrack {
class AssertionView;
}  // namespace backtrack

namespace preprocess {

/**
 * Wrapper around AssertionView for manipulating assertions for a given level.
 */
class AssertionVector
{
  friend class Preprocessor;

 public:
  AssertionVector(backtrack::AssertionView& view,
                  AssertionTracker* tracker = nullptr);

  /**
   * Push back new assertion.
   *
   * @note Increments d_changed.
   */
  void push_back(const Node& assertion, const Node& parent);

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

  /**
   * Determines whether the assertions in the vector are the initial assertions
   * on the assertion stack, i.e., the assertions on the stack before the first
   * check-sat call.
   */
  bool initial_assertions() const;

  /** Return assertion stack index at which the assertion vector starts. */
  size_t start_index() const;

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

  AssertionTracker* d_tracker;
};

}  // namespace preprocess
}  // namespace bzla

#endif
