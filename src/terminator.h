/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TERMINATOR_H_INCLUDED
#define BZLA_TERMINATOR_H_INCLUDED

namespace bzla {

class Terminator
{
 public:
  /** Destructor. */
  virtual ~Terminator(){};
  /**
   * Termination function.
   * If terminator has been connected, call to terminate connected
   * Bitwuzla instance.
   * @return True if the associated instance of Bitwuzla has been terminated.
   */
  virtual bool terminate() = 0;
};

}  // namespace bzla

#endif
