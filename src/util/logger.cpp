/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/logger.h"

#include "printer/printer.h"

namespace bzla::util {

Logger::Line::Line(uint64_t level, const char* prefix)
{
  auto& os = stream();
  // Save stream flags for restoring them later.
  d_flags = os.flags();
  // Set depth for node printing to 1
  os << printer::set_depth(1);
  if (prefix)
  {
    os << prefix << " ";
  }
  int32_t indent = 2 * (level - 1);
  if (indent)
  {
    os << std::setw(indent) << " ";
  }
}

Logger::Line::~Line()
{
  auto& os = stream();
  os << std::endl;
  // Reset node print depth
  os << printer::set_depth(0);
  // Reset stream flags.
  os.flags(d_flags);
}

std::ostream&
Logger::Line::stream()
{
  return std::cout;
}

Logger::Logger(uint64_t log_level,
               uint64_t verbosity,
               const std::string& prefix)
    : d_log_level(log_level), d_verbosity_level(verbosity), d_prefix(prefix)
{
}

bool
Logger::is_msg_enabled(uint64_t level)
{
  return level <= d_verbosity_level;
}

bool
Logger::is_log_enabled(uint64_t level)
{
  return level <= d_log_level;
}

Logger::Line
Logger::log(uint64_t level)
{
  return Line(level, d_prefix.empty() ? nullptr : d_prefix.c_str());
}

Logger::Line
Logger::msg(uint64_t level)
{
  return Line(level, "[bzla]");
}

Logger::Line
Logger::warn()
{
  return Line(1, "[bzla] warning:");
}

void
Logger::set_verbosity_level(uint64_t level)
{
  d_verbosity_level = level;
}

}  // namespace bzla::util
