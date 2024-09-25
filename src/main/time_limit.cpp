#include "main/time_limit.h"

#include <pthread.h>  // Required for workaround

#include <condition_variable>
#include <cstdlib>
#include <iostream>
#include <thread>

namespace bzla::main {

// Workaround for condition variables in glibc < 2.34 to avoid segfault before
// exiting: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=58909
void
pthread_cond_var_bug_workaround()
{
  pthread_cond_t c;
  pthread_mutex_t mt;
  pthread_condattr_t ca;
  struct timespec ts;
  pthread_cond_signal(&c);
  pthread_cond_init(&c, &ca);
  pthread_cond_destroy(&c);
  pthread_cond_timedwait(&c, &mt, &ts);
  pthread_cond_wait(&c, &mt);
}

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
