/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_STATISTICS_INCLUDED
#define BZLA_UTIL_STATISTICS_INCLUDED

#include <cassert>
#include <chrono>
#include <map>
#include <sstream>
#include <string>
#include <unordered_map>
#include <variant>
#include <vector>

namespace bzla::util {

/** Statistic to count enum types. */
class HistogramStatistic
{
 public:
  /** Increment counter for val. */
  template <typename T>
  void operator<<(const T& val)
  {
    size_t index = static_cast<size_t>(val);
    if (index >= d_values.size())
    {
      d_values.resize(index + 1);
      d_names.resize(index + 1);
    }
    if (d_names[index].empty())
    {
      std::stringstream ss;
      ss << val;
      d_names[index] = ss.str();
    }
    ++d_values[index];
  }

  template <typename K, typename V>
  void import_map(const std::unordered_map<K, V>& map)
  {
    for (auto& p : map)
    {
      *this << p.first;
      d_values[static_cast<size_t>(p.first)] = p.second;
    }
  }

  /** @return Stored counters for values. */
  const std::vector<uint64_t>& values() const { return d_values; }

  /** @return: Stored names for values. */
  const std::vector<std::string>& names() const { return d_names; }

 private:
  /** Stores counters for values added via operator<<. */
  std::vector<uint64_t> d_values;
  /** Stores names for values added via operator<<. */
  std::vector<std::string> d_names;
};

/** Statistic to compute elapsed time in code. */
class TimerStatistic
{
 public:
  friend class Timer;

  TimerStatistic();

  /** @return Cumulative elapsed milliseconds. */
  uint64_t elapsed() const;

  /** Start timer. */
  void start();

  /** Stop current timer. */
  void stop();

  /** @return Whether timer is currently running. */
  bool running() const;

 private:
  std::chrono::steady_clock::duration d_elapsed;
  std::chrono::steady_clock::time_point d_start;
  bool d_running;
};

/** Simple time statistic to record elapsed time in ms. */
class TimeStatistic
{
 public:
  TimeStatistic() : d_elapsed(0) {}
  /** @return The recorded elapsed ms. */
  uint64_t elapsed() const { return d_elapsed; }
  /**
   * Operator overload to add to the recorded elapsed time.
   * @param other The other TimeStatistic of which the elapsed time is to be
   *              added to this statistic's elapsed time.
   */
  TimeStatistic& operator+=(const TimerStatistic& other);

 private:
  /** The number of elapsed ms. */
  uint64_t d_elapsed;
};

/**
 * Timer for measuring elapsed time.
 * Starts wrapped timer when constructd, stops timer when destructed.
 */
class Timer
{
 public:
  Timer(TimerStatistic& stat);
  ~Timer();

 private:
  TimerStatistic& d_stat;
};

class Statistics
{
 public:
  /** @return Reference to new statistic. */
  template <typename T>
  T& new_stat(const std::string& name)
  {
    // assert(d_stats.find(name) == d_stats.end());
    // auto [it, inserted] = d_stats.emplace(name, T());
    // assert(inserted);
    // return std::get<T>(it->second);
    d_stats[name] = T();
    return std::get<T>(d_stats[name]);
  }

  /** Print statistics to std::cout. */
  void print() const;
  /** @return Map of strings of statistics entries. */
  std::map<std::string, std::string> get() const;

 private:
  using stat_value =
      std::variant<uint64_t, TimerStatistic, TimeStatistic, HistogramStatistic>;
  /** Registered statistic values. */
  std::map<std::string, stat_value> d_stats;
};

}  // namespace bzla::util

#endif
