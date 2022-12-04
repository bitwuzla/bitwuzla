#ifndef BZLA_UTIL_LOGGER_H_INCLUDED
#define BZLA_UTIL_LOGGER_H_INCLUDED

#include <iomanip>
#include <iostream>

#include "util/ostream_voider.h"

#define Msg(level)                \
  !d_logger.is_msg_enabled(level) \
      ? (void) 0                  \
      : bzla::util::OstreamVoider() & d_logger.msg(level).stream()

#define Log(level)                \
  !d_logger.is_log_enabled(level) \
      ? (void) 0                  \
      : bzla::util::OstreamVoider() & d_logger.log(level).stream()

namespace bzla::util {

class Logger
{
 public:
  class Line
  {
   public:
    Line(uint64_t level, const char* prefix = nullptr)
    {
      auto& os = stream();
      if (prefix)
      {
        os << prefix << " ";
      }
      os << std::setw(static_cast<int32_t>(2 * (level - 1))) << " ";
    }

    ~Line() { stream() << std::endl; }

    std::ostream& stream() { return std::cout; };
  };

  Logger(uint64_t log_level, uint64_t verbosity)
      : d_log_level(log_level), d_verbosity_level(verbosity)
  {
  }

  bool is_msg_enabled(uint64_t level) { return level <= d_verbosity_level; }

  bool is_log_enabled(uint64_t level) { return level <= d_log_level; }

  Line log(uint64_t level) { return Line(level); }

  Line msg(uint64_t level) { return Line(level, "[bzla]"); }

 private:
  uint64_t d_log_level;
  uint64_t d_verbosity_level;
};

}  // namespace bzla::util

#endif
