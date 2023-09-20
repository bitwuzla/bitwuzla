/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/resources.h"

#if defined(__WIN32)

// clang-format off
#include <windows.h>
#include <psapi.h>
// clang-format on

namespace {

uint64_t
memory_usage(bool max)
{
  PROCESS_MEMORY_COUNTERS mc;
  if (GetProcessMemoryInfo(GetCurrentProcess(), &mc, sizeof(mc)))
  {
    if (max)
    {
      return mc.PeakWorkingSetSize / 1024;
    }
    return mc.WorkingSetSize / 1024;
  }
  return 0;
}

}  // namespace

#elif defined(__APPLE__)

#include <mach/kern_return.h>
#include <mach/mach.h>
#include <mach/task_info.h>

namespace {

uint64_t
memory_usage(bool max)
{
  mach_task_basic_info_data_t info;
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
  kern_return_t ret            = task_info(
      mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t) &info, &count);

  if (ret == KERN_SUCCESS)
  {
    if (max)
    {
      return info.resident_size_max;
    }
    return info.resident_size;
  }
  return 0;
}

}  // namespace

#else

#include <unistd.h>

#include <fstream>

#ifdef HAVE_RUSAGE
#include <sys/resource.h>
#endif

namespace {

uint64_t
memory_usage(bool max)
{
  if (max)
  {
#ifdef HAVE_RUSAGE
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru))
    {
      return 0;
    }
    return ru.ru_maxrss * 1024;
#endif
  }
  else
  {
    std::ifstream statm("/proc/self/statm");
    if (statm.is_open())
    {
      uint64_t ignore, resident = 0;
      statm >> ignore >> resident;
      statm.close();

      uint64_t page_size = sysconf(_SC_PAGE_SIZE);
      return resident * page_size;
    }
  }
  return 0;
}

}  // namespace

#endif

namespace bzla::util {

uint64_t
maximum_memory_usage()
{
  return memory_usage(true);
}

uint64_t
current_memory_usage()
{
  return memory_usage(false);
}

}  // namespace bzla::util
