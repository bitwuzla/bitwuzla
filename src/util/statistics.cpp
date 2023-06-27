/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/statistics.h"

#include <iostream>

namespace bzla::util {

/* --- TimerStatistic public ------------------------------------------------ */

TimerStatistic::TimerStatistic() : d_elapsed(0), d_running(false) {}

uint64_t
TimerStatistic::elapsed() const
{
  auto elapsed = d_elapsed;
  if (d_running)
  {
    elapsed += std::chrono::steady_clock::now() - d_start;
  }
  return static_cast<uint64_t>(
      std::chrono::duration_cast<std::chrono::milliseconds>(elapsed).count());
}

void
TimerStatistic::start()
{
  assert(!d_running);
  d_start   = std::chrono::steady_clock::now();
  d_running = true;
}

void
TimerStatistic::stop()
{
  assert(d_running);
  d_elapsed += std::chrono::steady_clock::now() - d_start;
  d_running = false;
}

bool
TimerStatistic::running() const
{
  return d_running;
}

/* --- Timer public --------------------------------------------------------- */

Timer::Timer(TimerStatistic& stat) : d_stat(stat)
{
  if (!d_stat.running())
  {
    d_stat.start();
  }
}

Timer::~Timer()
{
  if (d_stat.running())
  {
    d_stat.stop();
  }
}

/* --- Statistics public ---------------------------------------------------- */

void
Statistics::print() const
{
  for (auto& [name, val] : d_stats)
  {
    if (std::holds_alternative<uint64_t>(val))
    {
      std::cout << name << ": " << std::get<uint64_t>(val) << std::endl;
    }
    else if (std::holds_alternative<TimerStatistic>(val))
    {
      std::cout << name << ": " << std::get<TimerStatistic>(val).elapsed()
                << "ms" << std::endl;
    }
    else
    {
      assert(std::holds_alternative<HistogramStatistic>(val));
      auto& histo = std::get<HistogramStatistic>(val);
      for (size_t i = 0, size = histo.values().size(); i < size; ++i)
      {
        if (histo.values()[i] > 0)
        {
          std::cout << name << "::" << histo.names()[i] << ": "
                    << histo.values()[i] << std::endl;
        }
      }
    }
  }
}

std::map<std::string, std::string>
Statistics::get() const
{
  std::map<std::string, std::string> res;
  for (auto& [name, val] : d_stats)
  {
    if (std::holds_alternative<uint64_t>(val))
    {
      res.emplace(name, std::to_string(std::get<uint64_t>(val)));
    }
    else if (std::holds_alternative<TimerStatistic>(val))
    {
      res.emplace(
          name, std::to_string(std::get<TimerStatistic>(val).elapsed()) + "ms");
    }
    else
    {
      assert(std::holds_alternative<HistogramStatistic>(val));
      auto& histo = std::get<HistogramStatistic>(val);
      for (size_t i = 0, size = histo.values().size(); i < size; ++i)
      {
        if (histo.values()[i] > 0)
        {
          res.emplace(name + "::" + histo.names()[i],
                      std::to_string(histo.values()[i]));
        }
      }
    }
  }
  return res;
}

}  // namespace bzla::util
