/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_CMS_H_INCLUDED
#define BZLA_SAT_CMS_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_CMS
/*------------------------------------------------------------------------*/

#include <cryptominisat5/cryptominisat.h>

#include <memory>

#include "sat/sat_solver.h"

namespace bzla::sat {

class CryptoMiniSat : public SatSolver
{
 public:
  CryptoMiniSat();

  void add(int32_t lit) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  Result solve() override;
  void configure_terminator(Terminator *terminator) override;
  const char *get_name() const override { return "CryptoMiniSat"; }
  const char *get_version() const override;

  void set_num_threads(uint32_t n_threads) const;
  /**
   * Add new variable.
   * @return The number of variables in the solver.
   */
  int32_t new_var() const;

 private:
  /**
   * Convert literal to CryptoMiniSat literal.
   * @param lit The literal to convert.
   * @return The converted literal.
   */
  CMSat::Lit import_lit(int32_t lit) const;
  /**
   * Collect data for failed().
   * Caches for each variable if it is failed, i.e., in the unsat core, in
   * d_failed_map.
   */
  void analyze_failed();
  /**
   * Collect datat for fixed().
   * Caches for each variable if its assignment is implied by the formula in
   * d_assigned_map.
   */
  void analyze_fixed();
  /** Reset cached data. */
  void reset();

  /** The wrapped CryptoMiniSat instance. */
  std::unique_ptr<CMSat::SATSolver> d_solver = nullptr;
  /** The current list of assumptions. */
  std::vector<CMSat::Lit> d_assumptions;
  /** The current (unterminated) clause. */
  std::vector<CMSat::Lit> d_clause;
  /** Map variable (index) to true if it is failed, and false otherwise. */
  std::vector<bool> d_failed_map;
  /**
   * Map variable (index) to 1 (if fixed to true), -1 (if fixed to false)
   * and 0 if its assignment is not implied by the formula.
   */
  std::vector<int8_t> d_assigned_map;
  /** A cache for the current number of variables in the solver. */
  uint32_t d_nvars = 0;
};

}  // namespace bzla::sat
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
