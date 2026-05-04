/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_SAT_PROPAGATOR_H_INCLUDED
#define BZLA_SAT_SAT_PROPAGATOR_H_INCLUDED

#include <cstdint>

namespace bzla::sat {

class Propagator;

class SatPropagator
{
 public:
  virtual ~SatPropagator()                               = default;
  virtual void attach_propagator(Propagator* propagator) = 0;
  virtual void assign(int32_t lit)                       = 0;
  virtual void unassign(int32_t var)                     = 0;
  virtual bool done() const                              = 0;
};

}  // namespace bzla::sat

#endif
