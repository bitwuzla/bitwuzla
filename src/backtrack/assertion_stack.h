/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_ASSERTION_STACK_H_INCLUDED
#define BZLA_BACKTRACK_ASSERTION_STACK_H_INCLUDED

#include <memory>
#include <unordered_map>
#include <vector>

#include "backtrack/backtrackable.h"
#include "node/node.h"

namespace bzla::backtrack {

class AssertionStack;

/**
 * A view for the assertion stack that gets automatically updated when the
 * assertion stack is modified via push/pop.
 */
class AssertionView
{
  friend AssertionStack;

 public:
  AssertionView() = delete;

  /**
   * Get the next unprocessed assertion on the assertion stack.
   *
   * This will move d_index forward.
   *
   * @return The next unprocessed assertion.
   */
  const Node& next();

  /** @return True if the view still has assertions to process. */
  bool empty() const;

  /**
   * @return The number of assertions to process.
   * @note The indices returned by begin() are the real indices in the
   *       assertion stack and therefore begin() < size() does not hold.
   */
  size_t size() const;

  /**
   * @return Assertion at given index relative to d_start_index.
   */
  const Node& operator[](size_t index) const;

  /** @return The level of the assertion at given index. */
  size_t level(size_t index) const;

  /** @return Start index of unprocessed assertions. */
  size_t begin() const;

  /** @return Start index of unprocessed assertions of given level. */
  size_t begin(size_t level) const;

  /** @return Index after the last unprocessed assertions. */
  size_t end() const;

  /** @return Index after the last unprocessed assertions of given level. */
  size_t end(size_t level) const;

  /** Update view to index. */
  void set_index(size_t index);

  /**
   * Replace an assertion.
   *
   * @param index The index of the assertion to be replaced.
   * @param replacement The new assertion.
   * @return True if assertion was replaced, and false otherwise.
   */
  bool replace(size_t index, const Node& replacement);

  /**
   * Insert assertion at given level.
   *
   * @param level The level to insert the assertion to.
   * @param assertion The assertion to insert.
   * @return True if assertion was inserted, and false otherwise.
   */
  bool insert_at_level(size_t level, const Node& assertion);

 private:
  AssertionView(AssertionStack& assertions);
  /** The underlying assertion stack. */
  AssertionStack& d_assertions;
  /** The index of the next assertion to process. */
  size_t d_index;
};

class AssertionStack : public Backtrackable
{
 public:
  AssertionStack() = default;
  AssertionStack(BacktrackManager* mgr);

  /**
   * Push new assertion onto stack.
   *
   * @param assertion The new assertion.
   * @return Whether assertion was added.
   */
  bool push_back(const Node& assertion);

  /**
   * Replace an assertion.
   *
   * @param index The index of the assertion to be replaced.
   * @param replacement The new assertion.
   * @return True if assertion was replaced, and false otherwise.
   */
  bool replace(size_t index, const Node& replacement);

  /**
   * Insert assertion at given level.
   *
   * @param level The level to insert the assertion to.
   * @param assertion The assertion to insert.
   * @return True if assertion was inserted, and false otherwise.
   */
  bool insert_at_level(size_t level, const Node& assertion);

  /** @return The number of assertions on the stack. */
  size_t size() const;

  /** @return Start index of unprocessed assertions of given level. */
  size_t begin(size_t level) const;

  /** @return Index after the last unprocessed assertions of given level. */
  size_t end(size_t level) const;

  /**
   * Get the level of the assertion at given index.
   *
   * @param index The index of the assertion on the stack.
   * @return The level of given assertion index.
   */
  size_t level(size_t index) const;

  /**
   * Get the assertion at given index.
   *
   * @param index The index of the assertion on the stack.
   * @return The assertion at given index.
   */
  const Node& operator[](size_t index) const;

  /** @return Iterator to the first assertion of the stack. */
  auto begin() const { return d_assertions.begin(); }

  /** @return Iterator to the end of the assertion assertion stack. */
  auto end() const { return d_assertions.end(); }

  /** @return A new view for the assertion stack. */
  AssertionView& view();

  /* --- Backtrackable interface -------------------------------------------- */

  /** Push new scope. */
  void push() override;

  /**
   * Pop scope.
   *
   * This will automatically update all registered views for this assertion
   * stack.
   */
  void pop() override;

 private:
  /** Assertion associated with their current scope level. */
  std::vector<std::pair<Node, size_t>> d_assertions;
  /** Registered views. */
  std::vector<std::unique_ptr<AssertionView>> d_views;
};

}  // namespace bzla::backtrack
#endif
