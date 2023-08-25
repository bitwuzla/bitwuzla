/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_MAIN_ERROR_H_INCLUDED
#define BZLA_MAIN_ERROR_H_INCLUDED

#include <iostream>

namespace bzla::main {

class Error
{
 public:
  Error() { stream() << "[error] "; }

  [[noreturn]] ~Error()
  {
    stream() << std::endl;
    std::exit(EXIT_FAILURE);
  }

  template <class T>
  std::ostream& operator<<(const T& t)
  {
    stream() << t;
    return stream();
  }

 private:
  std::ostream& stream() { return std::cerr; }
};

}  // namespace bzla::main

#endif
