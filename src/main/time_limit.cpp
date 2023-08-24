#include "main/time_limit.h"

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <cstdlib>
#include <iostream>
#include <thread>

namespace bzla::main {

using namespace std::chrono_literals;

std::condition_variable cv;
std::mutex cv_m;
bool time_limit_set = false;

void
timeout_reached()
{
  std::cout << "unknown" << std::endl;
  std::_Exit(EXIT_SUCCESS);
}

void
timeout(uint64_t time_limit)
{
  std::unique_lock<std::mutex> lock(cv_m);
  if (cv.wait_for(lock, time_limit * 1ms) == std::cv_status::timeout)
  {
    timeout_reached();
  }
}

void
set_time_limit(uint64_t time_limit)
{
  if (time_limit > 0)
  {
    time_limit_set = true;
    std::thread t(timeout, time_limit);
    t.detach();
  }
}

void
reset_time_limit()
{
  if (time_limit_set)
  {
    cv.notify_all();
  }
}

}  // namespace bzla::main
