#include "resource_terminator.h"

#include <iostream>

#include "util/resources.h"

namespace bzla {

using namespace std::chrono_literals;

bool
ResourceTerminator::terminate()
{
  return (d_time_limit > 0 && std::chrono::system_clock::now() >= d_deadline)
         || (d_memory_limit > 0
             && d_memory_limit <= util::current_memory_usage())
         || (d_terminator != nullptr && d_terminator->terminate());
}

void
ResourceTerminator::set_terminator(Terminator* terminator)
{
  d_terminator = terminator;
}

void
ResourceTerminator::set_time_limit(uint64_t time_limit)
{
  d_time_limit = time_limit;
  d_deadline   = std::chrono::system_clock::now() + time_limit * 1ms;
}

void
ResourceTerminator::set_memory_limit(uint64_t memory_limit)
{
  d_memory_limit = memory_limit * 1024 * 1024;
}

}  // namespace bzla
