/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PRINTER_EXCEPTION_H_INCLUDED
#define BZLA_PRINTER_EXCEPTION_H_INCLUDED

#include <exception>
#include <string>

namespace bzla::printer {

/**
 * The exception thrown when the printer encounters an unrecoverable error,
 * e.g., when symbols do not comply with a language standard.
 */
class Exception : public std::exception
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  Exception(const std::string& msg) : d_msg(msg) {}
  /**
   * Get the exception message.
   * @return The exception message.
   */
  const std::string& msg() const { return d_msg; }

  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  /** The exception message. */
  std::string d_msg;
};

}  // namespace bzla::printer

#endif
