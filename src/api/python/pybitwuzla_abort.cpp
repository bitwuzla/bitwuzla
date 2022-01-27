/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "pybitwuzla_abort.h"

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
pybitwuzla_abort_fun(const char* msg)
{
  throw BitwuzlaException(msg);
}

const char*
pybitwuzla_get_err_msg()
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
