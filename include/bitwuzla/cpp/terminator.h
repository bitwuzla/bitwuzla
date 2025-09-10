/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_CPP_TERMINATOR_H_INCLUDED
#define BITWUZLA_API_CPP_TERMINATOR_H_INCLUDED

namespace bitwuzla {

/** The termination callback configuration. */
class Terminator
{
 public:
  /** Destructor. */
  virtual ~Terminator();
  /**
   * Termination function.
   * If terminator has been connected, Bitwuzla calls this function periodically
   * to determine if the connected instance should be terminated.
   * @return True if the associated instance of Bitwuzla should be terminated.
   */
  virtual bool terminate() = 0;
};

}  // namespace bitwuzla

#endif
