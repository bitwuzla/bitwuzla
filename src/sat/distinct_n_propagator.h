/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_DISTINCT_N_PROPAGATOR_H_INCLUDED
#define BZLA_SAT_DISTINCT_N_PROPAGATOR_H_INCLUDED

#include <cstdint>
#include <memory>
#include <ostream>
#include <unordered_map>
#include <vector>

#include "lib/bv/bitvector.h"
#include "sat/sat_propagator.h"
#include "util/integer.h"

namespace bzla::sat {

class Propagator;

class WatchedBV
{
 public:
  WatchedBV(const std::vector<int32_t>& lits);

  int32_t watched() const;
  bool assign(const Propagator& propagator, int32_t lit);
  /**
   * Initialize with the next literal to watch. Fixed literals are skipped.
   *
   * @return True if all literals are fixed, i.e., the bit-vector value is fully
   *         assigned.
   */
  bool init(const Propagator& propagator);
  const auto& lits() const { return d_lits; }
  bool assigned(const Propagator& propagator) const;
  std::ostream& str(const Propagator& propagator, std::ostream& os) const;

 private:
  /** Represents the bits of the bit-vector starting with the MSB. */
  const std::vector<int32_t> d_lits;
  /** Index of currently watched lit in d_lits. */
  size_t d_watched = 0;
};

/**
 * All different constraint with assignment collision threshold. The collision
 * threshold allows for a number of assignment collisions in the ADC.
 *
 * Given the number of bit-vectors N, if the given cardinality is equal to N,
 * the assignment collision threshold is zero and thus, this class represents a
 * classic all different constraint as implemented in
 *
 *   A. Biere, R. Brummayer, "Consistency Checking of All Different Constraints
 *   over Bit-Vectors within a SAT Solver", FMCAD'08.
 *
 * If the given cardinality C is less than N, the ADC allows for N - C
 * assignment collisions, i.e., conflict clauses are only generated if this
 * threshold exceeded.
 *
 * If cardinality C is larger than N, the ADC immediately is forced to false,
 * since we do not have enough bit-vectors to reach the given cardinality.
 */
class DistinctNPropagator : public SatPropagator
{
 public:
  DistinctNPropagator(util::Integer& card,
                int32_t var,
                const std::vector<std::vector<int32_t>>& bvs);
  /**
   * Attach propagator, required for querying variable info and sending
   * conflict clauses.
   */
  void attach_propagator(Propagator* propagator) override;
  /** Assign literal watched by this propagator. */
  void assign(int32_t lit) override;
  /** Unassign literal watched by this propagator. */
  void unassign(int32_t var) override;
  /** @return Whether propagator CNF variable is fixed to false. */
  bool done() const override;

  /** @return CNF variable that represents this propagator. */
  int32_t var() const;

  std::ostream& str(std::ostream& os) const;

 private:
  /** All literals of watched bit-vector assigned. */
  void assigned(int32_t var, WatchedBV* wbv);
  /** Attached propagator. */
  Propagator* d_propagator = nullptr;
  /** CNF variable representing this propagator. */
  int32_t d_var;
  /** The cardinality of this propagator. */
  util::Integer d_cardinality;
  /** The number of allowed assignment collisions. */
  util::Integer d_num_conflict_thres;
  /** The number of current assignment collisions. */
  util::Integer d_num_conflicts;
  /** Map watched variable id to watched bit-vector. */
  std::unordered_map<int32_t, std::vector<WatchedBV*>> d_watched_vars;
  /** Maintains registered watched bit-vectors. */
  std::vector<std::unique_ptr<WatchedBV>> d_watched_bv;
  /**
   * Maps bit-vector assignments to watched bit-vector objects. Since we allow
   * collisions this maps to a vector of watched bit-vector objects.
   */
  std::unordered_map<BitVector, std::vector<WatchedBV*>> d_assigned_map;
  /**
   * Reverse map of d_assigned_map that maps trigger variable to fully assigned
   * watched bit-vector. Used by unassign() for backtracking fully-assigned
   * bit-vectors.
   */
  std::unordered_map<int32_t, std::vector<std::pair<BitVector, WatchedBV*>>>
      d_var_to_assigned;
};

}  // namespace bzla::sat

#endif
