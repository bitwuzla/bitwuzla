/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_EXCEPTIONS_INCLUDED
#define BZLA_UTIL_EXCEPTIONS_INCLUDED

#include <exception>
#include <string>

namespace bzla {

class Unsupported : std::exception
{
 public:
  Unsupported(const std::string& msg) : d_msg(msg) {}
  const std::string& msg() const { return d_msg; }

 private:
  std::string d_msg;
};

class Error : std::exception
{
 public:
  Error(const std::string& msg) : d_msg(msg) {}
  const std::string& msg() const { return d_msg; }

 private:
  std::string d_msg;
};

}  // namespace bzla

#endif
