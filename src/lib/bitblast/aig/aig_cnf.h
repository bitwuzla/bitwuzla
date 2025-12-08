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
#include "bitblast/aig/aig_node.h"

namespace bzla::bitblast {

class SatInterface
{
 public:
   virtual ~SatInterface() {};

   /**
    * Allocate new variable.
    * @return Fresh variable.
    */
   virtual int32_t new_var() = 0;

   /**
    * Add literal to current clause.
    *
    * @param id Id of literal to be added. 0 terminates the clause.
    * @param aig_id   The AIG id associated with the currently added clause.
    *                 In the case of clauses associated with and nodes or AIGs
    *                 encoding ITEs, this id will always be positive. In the
    *                 case of units encoding (the leafs of AIGs representing)
    *                 top-level assertions, the clause is associated with the
    *                 top-most AIG representing the assertion (and thus the id
    *                 may be negative).
    *
    * @note Parameter `aig_id` is not needed for standard bit-blasting, but may
    *       be required, e.g., for clause labeling when generating interpolants
    *       from the SAT proof.
    */
   virtual void add(int64_t lit, int64_t aig_id = 0) = 0;
   /**
    * Add a set of literals as clause.
    *
    * @param literals List of literals to be added (without terminating 0).
    * @param aig_id   The AIG id associated with this clause. In the case of
    *                 clauses associated with and nodes or AIGs encoding ITEs,
    *                 this id will always be positive. In the case of units
    *                 encoding (the leafs of AIGs representing) top-level
    *                 assertions, the clause is associated with the top-most
    *                 AIG representing the assertion (and thus the id may be
    *                 negative).
    *
    * @note Parameter `aig_id` is not needed for standard bit-blasting, but may
    *       be required, e.g., for clause labeling when generating interpolants
    *       from the SAT proof.
    */
   virtual void add_clause(const std::initializer_list<int64_t>& literals,
                           int64_t aig_id = 0) = 0;
   /**
    * Query the value of the given literal.
    * @return True if the literal evaluates to true.
    */
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

  AigCnfEncoder(SatInterface& sat_solver);

  /**
   * Recursively encodes AIG node to CNF.
   *
   * @param node The AIG node to encode.
   * @param top_level Indicates whether given node is at the top level, which
   *        enables certain optimization.
   * */
  void encode(const AigNode& node, bool top_level = false);

  int32_t value(const AigNode& node);

  /** @return CNF variable of given encoded AIG node. */
  int32_t cnf_var(const AigNode& aig) const;

  /** @return CNF literal of given encoded AIG node. */
  int32_t cnf_lit(const AigNode& aig) const;

  /** @return Whether `aig` was already encoded to CNF. */
  bool is_encoded(const AigNode& aig) const;

  /** @return The AIG id to CNF id map. */
  const std::vector<int32_t>& aig2cnf() const { return d_aig_encoded; }

  /** @return CNF statistics. */
  const Statistics& statistics() const;

 private:
  /** Encode AIG to CNF. */
  void _encode(const AigNode& node);
  /** Ensure that `d_aig_encoded` is big enough to store `aig`. */
  void resize(const AigNode& aig);
  /** Mark `aig` as encoded. */
  void set_encoded(const AigNode& aig);

  /** Maps AIG id to CNF id, which indicates whether the AIG was encoded. */
  std::vector<int32_t> d_aig_encoded;
  /** SAT solver. */
  SatInterface& d_sat_solver;
  /** Variable allocated for true/false. */
  int32_t d_true_var;

  /** CNF statistics. */
  Statistics d_statistics;
};
}  // namespace bzla::bitblast
#endif
