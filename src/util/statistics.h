#ifndef BZLA_UTIL_STATISTICS_INCLUDED
#define BZLA_UTIL_STATISTICS_INCLUDED

#include <cassert>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
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

class Statistics
{
 public:
  ~Statistics() { print(); }

  /** @return Reference to new statistic. */
  template <typename T>
  T& new_stat(const std::string& name)
  {
    assert(d_stats.find(name) == d_stats.end());
    auto [it, inserted] = d_stats.emplace(name, T());
    assert(inserted);
    return std::get<T>(it->second);
  }

  /** Print statistics to std::cout. */
  void print() const
  {
    for (auto& [name, val] : d_stats)
    {
      if (std::holds_alternative<uint64_t>(val))
      {
        std::cout << name << ": " << std::get<uint64_t>(val) << std::endl;
      }
      else if (std::holds_alternative<double>(val))
      {
        std::cout << name << ": " << std::get<double>(val) << std::endl;
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

 private:
  using stat_value = std::variant<uint64_t, double, HistogramStatistic>;
  /** Registered statistic values. */
  std::unordered_map<std::string, stat_value> d_stats;
};

}  // namespace bzla::util

#endif
