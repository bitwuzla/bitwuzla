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
   * This will move d_cur_index forward.
   *
   * @return The next unprocessed assertion.
   */
  const Node& next();

  /**
   * Get the next unprocessed assertion and associated scope level.
   *
   * This will move d_cur_index forward.
   *
   * @return The next assertion and its associated scope level. */
  const std::pair<Node, size_t>& next_level();

  /**
   * @return Whether the view still has assertions to process.
   * @note This is decoupled from size() == 0, since size() computes the number
   *       of elements relative to d_start_index.
   */
  bool empty() const;

  /**
   * Replace an assertion.
   *
   * @param index The index of the assertion to be replaced.
   * @param replacement The new assertion.
   */
  void replace(size_t index, const Node& replacement);

  /**
   * Insert assertion at given level.
   *
   * @param level The level to insert the assertion to.
   * @param assertion The assertion to insert.
   */
  void insert_at_level(size_t level, const Node& assertion);

  /**
   * @return Assertion and its level at given index relative to d_start_index.
   */
  const std::pair<Node, size_t>& operator[](size_t index) const;

  /** @return The number of assertions relative to d_start_index. */
  size_t size() const;

 private:
  AssertionView(AssertionStack& assertions);
  /** The underlying assertion stack. */
  AssertionStack& d_assertions;
  /** The index of the next assertion to process. */
  size_t d_cur_index;
  /** Start index of assertions since last pop(). */
  size_t d_start_index;
};

class AssertionStack : public Backtrackable
{
 public:
  AssertionStack() = default;
  AssertionStack(BacktrackManager* mgr) : Backtrackable(mgr) {}

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
   */
  void replace(size_t index, const Node& replacement);

  /**
   * Insert assertion at given level.
   *
   * @param level The level to insert the assertion to.
   * @param assertion The assertion to insert.
   */
  void insert_at_level(size_t level, const Node& assertion);

  /** @return The number of assertions on the stack. */
  size_t size() const;

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

  const std::pair<Node, size_t>& get(size_t index) const;

  /** @return Iterator to the first assertion of the stack. */
  auto begin() const { return d_assertions.begin(); }

  /** @return Iterator to the end of the assertion assertion stack. */
  auto end() const { return d_assertions.end(); }

  /** @return A new view for the assertion stack. */
  AssertionView& create_view();

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
  /** Assertion cache to avoid pushing duplicates. */
  std::unordered_map<Node, size_t> d_cache;
  /** Registered views. */
  std::vector<std::unique_ptr<AssertionView>> d_views;
};

}  // namespace bzla::backtrack
#endif
