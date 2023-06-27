/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "api/checks.h"

#include <bitwuzla/cpp/bitwuzla.h>

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
