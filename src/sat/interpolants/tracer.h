/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_INTERPOLANTS_TRACER_H_INCLUDED
#define BZLA_SAT_INTERPOLANTS_TRACER_H_INCLUDED

#include "bitblast/aig/aig_manager.h"
#include "env.h"
#include "sat/interpolants/tracer_kinds.h"
#include "solver/bv/aig_bitblaster.h"
#include "tracer.hpp"
#include "util/logger.h"

namespace bzla {

class Env;
class Node;
class NodeManager;

namespace sat::interpolants {

class Tracer : public CaDiCaL::Tracer
{
 public:
  /**
   * Constructor.
   * @param env        The associated environment.
   * @param bitblaster The associated bitblaster.
   * @param lift       True if interpolant is lifted as much as possible to the
   *                   theory level. Else, the interpolant corresponds exactly
   *                   to the bit-level AIG interpolant.
   */
  Tracer(Env& env, bv::AigBitblaster& bitblaster, bool lift)
      : d_stats(env.statistics(), "sat::interpolants::tracer::"),
        d_nm(env.nm()),
        d_bitblaster(bitblaster),
        d_amgr(bitblaster.amgr()),
        d_logger(env.logger()),
        d_lift(lift)
  {
  }

  /**
   * Set the associated AIG id of the currently processed clause.
   * @param id The AIG id.
   */
  void set_current_aig_id(int64_t id)
  {
    assert(id);
    d_cur_aig_id = id;
  }

  /**
   * Get interpolant.
   * @param var_labels    Map of AIG id to variable kinds.
   * @param clause_labels Map of AIG id to clause kinds.
   * @param term_labels   Map from terms to variable labels. If any input of a
   *                      term is labeled as A/B-local, the term is labeled as
   *                      A/B-local, and GLOBAL otherwise.
   * @return The interpolant.
   */
  virtual Node get_interpolant(
      const std::unordered_map<int64_t, VariableKind>& var_labels,
      const std::unordered_map<int64_t, ClauseKind>& clause_labels,
      const std::unordered_map<Node, sat::interpolants::VariableKind>&
          term_labels) = 0;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& size_interpolant;
    uint64_t& size_proof;
    uint64_t& size_proof_core;
  } d_stats;

 protected:
  /**
   * Alias for reverse bitblaster cache, maps AIG id (SAT variable, thus always
   * non-negative) to the Node the AIG occurs in and the bit index it is at.
   */
  using RevBitblasterCache =
      std::unordered_map<int64_t, std::pair<ConstNodeRef, size_t>>;

  /**
   * Compute a reverse mapping of the current bitblaster cache.
   * @return A mapping from AIG id (SAT variable, thus always non-negative) to
   *         the Node the AIG occurs in and the bit index it is at.
   */
  RevBitblasterCache compute_rev_bb_cache() const;

  /**
   * Helper to get the node from the bitblaster cache that represents the AIG
   * node with the given id.
   * @param aig   The AIG node to get the node representation of.
   * @param cache The reverse bitblaster cache, which is the reverse mapping
   *              of the bitblaster cache.
   * @param term_labels Map from terms to variable labels. If any input of a
   *                    term is labeled as A/B-local, the term is labeled as
   *                    A/B-local, and GLOBAL otherwise.
   * @return The node representation of the given AIG, null if the AIG does not
   *         occur in the bitblaster cache.
   */
  Node get_node_from_bb_cache(
      const bitblast::AigNode& aig,
      RevBitblasterCache& cache,
      const std::unordered_map<Node, sat::interpolants::VariableKind>&
          term_labels) const;

  /** The associated node manager. */
  NodeManager& d_nm;
  /** The associated bitblaster. */
  bv::AigBitblaster& d_bitblaster;
  /** The associated AIG manager. */
  bitblast::AigManager& d_amgr;
  /** The associated logger instance. */
  util::Logger& d_logger;
  /** True if lifting the interpolant to the theory level is enabled. */
  bool d_lift;

  /** The associated AIG id of the currently processed clause. */
  int64_t d_cur_aig_id = 0;
};

}  // namespace sat::interpolants
}  // namespace bzla

#endif
