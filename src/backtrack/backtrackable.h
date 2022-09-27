#ifndef BZLA_BACKTRACK_BACKTRACKABLE_H_INCLUDED
#define BZLA_BACKTRACK_BACKTRACKABLE_H_INCLUDED

#include <unordered_set>
#include <vector>

namespace bzla::backtrack {

class Backtrackable;

/**
 * Used to manage scopes of backtrackable objects via push()/pop().
 */
class BacktrackManager
{
  friend Backtrackable;

 public:
  /** Create new scope. */
  void push();
  /** Pop scope. */
  void pop();

 private:
  /** Registers a backtrackable object with this manager. */
  void register_backtrackable(Backtrackable* backtrackable);
  /** Removes a backtrackable object from this manager. */
  void remove_backtrackable(Backtrackable* backtrackable);

  /** Number of scopes currently pushed. */
  std::size_t d_scope_levels = 0;
  /** Set of backtrackable objects. */
  std::unordered_set<Backtrackable*> d_backtrackables;
};

/**
 * Interface to be implemented for backtrackable classes.
 */
class Backtrackable
{
 public:
  Backtrackable() = default;
  Backtrackable(BacktrackManager* mgr);
  ~Backtrackable();

  /** Create new scope. */
  virtual void push() = 0;
  /** Pop last scope. */
  virtual void pop() = 0;

 protected:
  /** Backtrack manager this object is associated with. */
  BacktrackManager* d_mgr = nullptr;
  /** Control stack used for marking scopes. */
  std::vector<std::size_t> d_control;
};

}  // namespace bzla::backtrack

#endif
