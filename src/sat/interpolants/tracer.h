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
  enum class VariableKind
  {
    A,
    B,
    GLOBAL,
  };
  enum class ClauseKind
  {
    A,
    B,
    LEARNED,  // internal
  };

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
   * Label variable with given kind.
   * @param id   The variable id.
   * @param kind The variable kind.
   */
  virtual void label_variable(int32_t id, VariableKind kind) = 0;

  /**
   * Label clause with given kind.
   * @note Clause IDs must be consecutive.
   * @param id   The clause id.
   * @param kind The clause kind.
   */
  virtual void label_clause(int32_t id, ClauseKind kind) = 0;

  /**
   * Get interpolant.
   * @return The interpolant.
   */
  virtual Node get_interpolant() = 0;

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

  /** The associated node manager. */
  NodeManager& d_nm;
  /** The associated bitblaster. */
  bv::AigBitblaster& d_bitblaster;
  /** The associated AIG manager. */
  bitblast::AigManager& d_amgr;
  /** The associated logger instance. */
  util::Logger& d_logger;
};

std::ostream& operator<<(std::ostream& out, Tracer::VariableKind kind);
std::ostream& operator<<(std::ostream& out, Tracer::ClauseKind kind);

}  // namespace sat::interpolants
}  // namespace bzla

#endif
