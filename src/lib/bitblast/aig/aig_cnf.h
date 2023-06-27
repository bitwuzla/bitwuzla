/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BITBLAST_AIG_CNF_H
#define BZLA__BITBLAST_AIG_CNF_H
#include "bitblast/aig/aig_manager.h"

namespace bzla::bb {

class SatInterface
{
 public:
   virtual ~SatInterface() {};

  /**
   * Add literal to current clause.
   *
   * @param id Id of literal to be added. 0 terminates the clause.
   */
  virtual void add(int64_t lit) = 0;
  /**
   * Add a set of literals as clause.
   *
   * @param literals List of literals to be added (without terminating 0).
   */
  virtual void add_clause(const std::initializer_list<int64_t>& literals) = 0;

  virtual bool value(int64_t lit) = 0;
};

class AigCnfEncoder
{
 public:
  struct Statistics
  {
    uint64_t num_vars     = 0;  // Number of added variables
    uint64_t num_clauses  = 0;  // Number of added clauses
    uint64_t num_literals = 0;  // Number of added literals
  };

  AigCnfEncoder(SatInterface& sat_solver) : d_sat_solver(sat_solver){};

  /**
   * Recursively encodes AIG node to CNF.
   *
   * @param node The AIG node to encode.
   * @param top_level Indicates whether given node is at the top level, which
   *        enables certain optimization.
   * */
  void encode(const AigNode& node, bool top_level = false);

  int32_t value(const AigNode& node);

  /** @return CNF statistics. */
  const Statistics& statistics() const;

 private:
  /** Encode AIG to CNF. */
  void _encode(const AigNode& node);
  /** Ensure that `d_aig_encoded` is big enough to store `aig`. */
  void resize(const AigNode& aig);
  /** Checks whether `aig` was already encoded. */
  bool is_encoded(const AigNode& aig) const;
  /** Mark `aig` as encoded. */
  void set_encoded(const AigNode& aig);

  /** Maps AIG id to flag that indicates whether the AIG was already encoded. */
  std::vector<bool> d_aig_encoded;
  /** SAT solver. */
  SatInterface& d_sat_solver;
  /** CNF statistics. */
  Statistics d_statistics;
};
}  // namespace bzla::bb
#endif
