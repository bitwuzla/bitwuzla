#ifndef BZLA_BACKTRACK_ASSERTION_STACK_H_INCLUDED
#define BZLA_BACKTRACK_ASSERTION_STACK_H_INCLUDED

#include <memory>
#include <unordered_set>
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

  /** @return The next assertion on the assertion stack. */
  const Node& next();

  /** @return The next assertion and its associated scope level. */
  const std::pair<Node, size_t>& next_level();

  /** @return The next assertion and its associated index on the assertion
   * stack. */
  std::pair<Node, size_t> next_index();

  /** @return Whether the view still has assertions to process. */
  bool empty() const;

  /** @return The number of assertions seen by this view. */
  size_t size();

  void replace(size_t index, const Node& assertion);

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
  AssertionStack(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /**
   * Push new assertion onto stack.
   *
   * @param assertion The new assertion.
   */
  void push_back(const Node& assertion);

  /**
   * Replace an assertion.
   *
   * @param index The index of the assertion to be replaced
   * @param assertion The new assertion.
   */
  void replace(size_t index, const Node& assertion);

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
  std::unordered_set<Node> d_cache;
  /** Registered views. */
  std::vector<std::unique_ptr<AssertionView>> d_views;
};

}  // namespace bzla::backtrack
#endif
