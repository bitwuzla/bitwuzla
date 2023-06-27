/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "abort.h"

#include <string>

class BitwuzlaException : public std::exception
{
 public:
  BitwuzlaException(const char* msg) : msg(msg) {}
  const char* what() const noexcept override { return msg.c_str(); }

 protected:
  std::string msg;
};

void
py_bitwuzla_abort_fun(const char* msg)
{
  throw BitwuzlaException(msg);
}

const char*
py_bitwuzla_get_err_msg()
{
  try
  {
    throw;
  }
  catch (const BitwuzlaException& e)
  {
    return e.what();
  }
}
