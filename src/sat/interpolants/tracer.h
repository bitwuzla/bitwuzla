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
   */
  Tracer(Env& env, bv::AigBitblaster& bitblaster)
      : d_stats(env.statistics(), "sat::interpol::"),
        d_nm(env.nm()),
        d_bitblaster(bitblaster),
        d_amgr(bitblaster.amgr()),
        d_logger(env.logger())
  {
  }

  /**
   * Set the associated AIG id of the currently processed clause.
   * @param id The AIG id.
   */
  void set_current_aig_id(int64_t id) { d_cur_aig_id = id; }

  /**
   * Get interpolant.
   * @param var_labels A map of AIG id to variable kinds.
   * @param clause_labels A map of AIG id to clause kinds.
   * @return The interpolant.
   */
  virtual Node get_interpolant(
      const std::unordered_map<int64_t, VariableKind>& var_labels,
      const std::unordered_map<int64_t, ClauseKind>& clause_labels) = 0;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& size_interpolant;
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
   * @param aig_id The id of the AIG node to get the node representation of.
   * @param cache  The reverse bitblaster cache, which is the reverse mapping
   *               of the bitblaster cache.
   * @return The node representation of the given AIG, null if the AIG does not
   *         occur in the bitblaster cache.
   */
  Node get_node_from_bb_cache(int64_t aig_id, RevBitblasterCache& cache) const;

  /** The associated node manager. */
  NodeManager& d_nm;
  /** The associated bitblaster. */
  bv::AigBitblaster& d_bitblaster;
  /** The associated AIG manager. */
  bitblast::AigManager& d_amgr;
  /** The associated logger instance. */
  util::Logger& d_logger;

  /** The associated AIG id of the currently processed clause. */
  int64_t d_cur_aig_id = 0;
};

}  // namespace sat::interpolants
}  // namespace bzla

#endif
