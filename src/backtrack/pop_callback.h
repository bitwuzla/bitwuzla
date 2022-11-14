#ifndef BZLA_BACKTRACK_POP_CALLBACK_H_INCLUDED
#define BZLA_BACKTRACK_POP_CALLBACK_H_INCLUDED

#include <cassert>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

/**
 * Callback for syncing pops between two backtrack managers.
 */
class PopCallback : public Backtrackable
{
 public:
  PopCallback(backtrack::BacktrackManager* mgr,
              backtrack::BacktrackManager* to_pop)
      : Backtrackable(mgr), d_backtrack_mgr(mgr), d_to_pop(to_pop)
  {
    assert(mgr);
    assert(to_pop);
  }

  void push() override {}

  void pop() override
  {
    // Only pop if both backtrack managers are in sync, i.e., have the same
    // number of scope levels.
    if (d_backtrack_mgr->num_levels() == d_to_pop->num_levels())
    {
      d_to_pop->pop();
    }
  }

 private:
  /** Backtrack manager that triggers pop. */
  backtrack::BacktrackManager* d_backtrack_mgr;
  /** Backtrack manager to be synced. */
  backtrack::BacktrackManager* d_to_pop;
};

}  // namespace bzla::backtrack
#endif
