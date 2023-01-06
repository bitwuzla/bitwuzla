#include "util/logger.h"

#include "printer/printer.h"

namespace bzla::util {

Logger::Line::Line(uint64_t level, const char* prefix)
{
  auto& os = stream();
  // Set depth for node printing to 1
  os.iword(Printer::s_stream_index_maximum_depth) = 1;
  if (prefix)
  {
    os << prefix << " ";
  }
  os << std::setw(static_cast<int32_t>(2 * (level - 1))) << " ";
}

Logger::Line::~Line()
{
  auto& os                                        = stream();
  os.iword(Printer::s_stream_index_maximum_depth) = 0;
  os << std::endl;
}

std::ostream&
Logger::Line::stream()
{
  return std::cout;
};

Logger::Logger(uint64_t log_level, uint64_t verbosity)
    : d_log_level(log_level), d_verbosity_level(verbosity)
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
  return Line(level);
}

Logger::Line
Logger::msg(uint64_t level)
{
  return Line(level, "[bzla]");
}
}  // namespace bzla::util
