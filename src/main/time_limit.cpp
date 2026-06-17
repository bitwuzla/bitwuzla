#include "main/time_limit.h"

#include <pthread.h>  // Required for workaround

#include <condition_variable>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <thread>

#include "bitwuzla/cpp/parser.h"

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
// Predicate guarded by cv_m: set to true by reset_time_limit() once solving has
// finished so that the timeout thread can distinguish a genuine timeout from a
// notification or a spurious wakeup.
bool done = false;

bitwuzla::parser::Parser* g_parser = nullptr;

void
timeout_reached()
{
  std::cout << "unknown" << std::endl;
  if (g_parser != nullptr)
  {
    auto bitwuzla = g_parser->bitwuzla();
    if (bitwuzla != nullptr)
    {
      auto stats = bitwuzla->statistics();
      stats.merge(g_parser->statistics());
      for (auto& [name, val] : stats)
      {
        std::cout << name << ": " << val << std::endl;
      }
    }
  }
  std::_Exit(EXIT_SUCCESS);
}

void
timeout(uint64_t time_limit)
{
  std::unique_lock<std::mutex> lock(cv_m);
  // Use the predicate overload so that (1) a spurious wakeup does not silently
  // cancel the time limit and (2) a notify_all() issued by reset_time_limit()
  // before we start waiting is not lost. wait_for() returns false only if the
  // timeout expired while 'done' is still false, i.e., on a genuine timeout.
  if (!cv.wait_for(lock, time_limit * 1ms, [] { return done; }))
  {
    timeout_reached();
  }
}

void
set_time_limit(uint64_t time_limit)
{
  if (time_limit > 0)
  {
    {
      std::lock_guard<std::mutex> lock(cv_m);
      done = false;
    }
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
    {
      std::lock_guard<std::mutex> lock(cv_m);
      done = true;
    }
    cv.notify_all();
  }
}

void
print_statistics_time_limit(bitwuzla::parser::Parser* parser)
{
  g_parser = parser;
}

}  // namespace bzla::main
