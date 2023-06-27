/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_OSTREAM_VOIDER_H_INCLUDED
#define BZLA_UTIL_OSTREAM_VOIDER_H_INCLUDED

#include <ostream>

namespace bzla::util {

class OstreamVoider
{
 public:
  OstreamVoider() = default;
  void operator&(std::ostream &ostream) { (void) ostream; }
};

}

#endif
