/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *  Copyright (C) 2020 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
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
