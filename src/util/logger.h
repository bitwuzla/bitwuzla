/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_LOGGER_H_INCLUDED
#define BZLA_UTIL_LOGGER_H_INCLUDED

#include <cstdint>
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

  /**
   * Constructor.
   * @param log_level The log level.
   * @param verbosity The verbosity level.
   * @param prefix    The prefix for log/verbose messages.
   */
  Logger(uint64_t log_level,
         uint64_t verbosity,
         const std::string& prefix = "");

  /** @return True if verbose messaging is enabled for the given level. */
  bool is_msg_enabled(uint64_t level);

  /** @return True if logging is enabled for the given level. */
  bool is_log_enabled(uint64_t level);

  /**
   * Start new log line for given level.
   * @param level The level.
   * @return The line.
   */
  Line log(uint64_t level);

  /**
   * Start new verbose message line for given level.
   * @param level The level.
   * @return The line.
   */
  Line msg(uint64_t level);

  /**
   * Start new warning message.
   * @note Warnings are automatically configured to be enabled at level 1.
   */
  Line warn();

  /**
   * Set the verbosity level.
   * @param level The verbosity level.
   */
  void set_verbosity_level(uint64_t level);

 private:
  /** The log level. */
  uint64_t d_log_level;
  /** The verbosity level. */
  uint64_t d_verbosity_level;
  /** The message prefix for verbose and logging messages. */
  std::string d_prefix;
};

}  // namespace bzla::util

#endif
