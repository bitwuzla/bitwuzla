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

#define Warn(cond) \
  !(cond) ? (void) 0 : bzla::util::OstreamVoider() & d_logger.warn().stream()

namespace bzla::util {

class Logger
{
 public:
  class Line
  {
   public:
    Line(uint64_t level, const char* prefix = nullptr);
    ~Line();
    std::ostream& stream();

   private:
    /** Stream flags saved on construction and restored on destruction. */
    std::ios_base::fmtflags d_flags;
  };

  Logger(uint64_t log_level,
         uint64_t verbosity,
         const std::string& prefix = "");

  bool is_msg_enabled(uint64_t level);

  bool is_log_enabled(uint64_t level);

  Line log(uint64_t level);

  Line msg(uint64_t level);

  Line warn();

 private:
  uint64_t d_log_level;
  uint64_t d_verbosity_level;
  std::string d_prefix;
};

}  // namespace bzla::util

#endif
