/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_GIMSATUL_H_INCLUDED
#define BZLA_SAT_GIMSATUL_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_GIMSATUL
/*------------------------------------------------------------------------*/

#include <vector>

#include "sat/sat_solver.h"

extern "C" {
struct gimsatul;
}

namespace bzla::sat {

class Gimsatul : public SatSolver
{
 public:
  Gimsatul(uint32_t threads);
  ~Gimsatul();

  void add(int32_t lit) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  Result solve() override;
  void configure_terminator(Terminator *terminator) override;
  const char *get_name() const override { return "Gimsatul"; }
  const char *get_version() const override;

 private:
  uint32_t d_nthreads;
  int32_t d_max_var     = 0;
  int32_t d_num_clauses = 0;
  std::vector<int32_t> d_literals;
  std::vector<int32_t> d_assumptions;
  struct gimsatul *d_gimsatul = nullptr;
};

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
