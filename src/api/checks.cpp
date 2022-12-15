#include "api/checks.h"

#include "api/cpp/bitwuzla.h"

namespace bitwuzla {

/* --- BitwuzlaExceptionStream public --------------------------------------- */

BitwuzlaExceptionStream::BitwuzlaExceptionStream() {}

BitwuzlaExceptionStream::~BitwuzlaExceptionStream() noexcept(false)
{
  if (std::uncaught_exceptions() == 0)
  {
    throw Exception(d_stream.str());
  }
}
std::ostream&
BitwuzlaExceptionStream::ostream()
{
  return d_stream;
}

}  // namespace bitwuzla
