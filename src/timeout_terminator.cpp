#include "timeout_terminator.h"

namespace bzla {

using namespace std::chrono_literals;

bool
TimeoutTerminator::terminate()
{
  return std::chrono::system_clock::now() >= d_deadline
         || (d_terminator != nullptr && d_terminator->terminate());
}

void
TimeoutTerminator::set_terminator(Terminator* terminator)
{
  d_terminator = terminator;
}

void
TimeoutTerminator::set(uint64_t time_limit)
{
  d_deadline = std::chrono::system_clock::now() + time_limit * 1ms;
}

}  // namespace bzla
