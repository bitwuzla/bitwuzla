/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED
#define BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED

#include <memory>
#include <string>

#include "option/option.h"
#include "sat/sat_solver.h"

namespace bzla::sat {

class SatSolverFactory
{
 public:
  /** Constructor. */
  SatSolverFactory(const option::Options& options)
      : d_sat_solver(options.sat_solver()),
        d_nthreads(options.nthreads()),
        d_mallob_api_dir(options.mallob_api_dir()),
        d_mallob_binary(options.mallob_binary()),
        d_mallob_launcher(options.mallob_launcher()),
        d_mallob_args(options.mallob_args()),
        d_mallob_nthreads(
            options.nthreads.is_user_set() ? options.nthreads() : 0)
  {
  }
  virtual ~SatSolverFactory() {}
  /** Create new SAT solver instance. */
  virtual std::unique_ptr<SatSolver> new_sat_solver(
      bool produce_interpolants = false);
  /** Determine if configured SAT solver has terminator support. */
  virtual bool has_terminator_support();

 private:
  option::SatSolver d_sat_solver;
  uint64_t d_nthreads;
  std::string d_mallob_api_dir;
  std::string d_mallob_binary;
  std::string d_mallob_launcher;
  std::string d_mallob_args;
  /** Threads for a managed Mallob process, 0 to use all available cores. */
  uint32_t d_mallob_nthreads;
};

}  // namespace bzla::sat
#endif
