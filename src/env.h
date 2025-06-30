/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_ENV_H_INCLUDED
#define BZLA_ENV_H_INCLUDED

#include "node/node_manager.h"
#include "option/option.h"
#include "rewrite/rewriter.h"
#include "util/logger.h"
#include "util/statistics.h"

namespace bzla {

namespace backtrack {
class BacktrackManager;
}

namespace preprocess {
class SimplifyCache;
}  // namespace preprocess

class Terminator;

class Env
{
 public:
  /**
   * Constructor.
   * @param options The associated configuration options.
   */
  Env(NodeManager& nm,
      const option::Options& options = option::Options(),
      const std::string& name        = "");

  /** @return The associated options instance. */
  const option::Options& options() const;

  /** @return The associated statistics instance. */
  util::Statistics& statistics();

  /** @return The associated rewriter instance. */
  Rewriter& rewriter();

  /** @return The associated logger instance. */
  util::Logger& logger();

  /** @return The associated node manager instance. */
  NodeManager& nm();

  /**
   * Configure associated termination configuration instance.
   * @note Only one terminator can be configured at a time. This will
   *       disconnect a previously configured terminator before configuring
   *       the given one.
   * @param terminator The terminator instance. Nullptr will disconnect the
   *                   terminator.
   */
  void configure_terminator(Terminator* terminator);

  /**
   * Terminate solving context instance if termination function `f_terminate`
   * has been configured.
   * @return True if instance has been terminated.
   */
  bool terminate() const;

  /** @return The currently connected terminator instance. */
  Terminator* terminator() const { return d_terminator; }

  /** @return Simplification backtrack manager. */
  auto& simplify_backtrack_mgr() { return *d_simplify_backtrack_mgr; }

  /** @return Node simplification cache. */
  auto& simplify_cache() { return *d_simplify_cache; }

 private:
  /** The associated node manager. */
  NodeManager& d_nm;
  /** The configured options. */
  option::Options d_options;
  /** The statistics. */
  util::Statistics d_statistics;
  /** The associated terminator. */
  Terminator* d_terminator = nullptr;
  /** The associated logger class. */
  util::Logger d_logger;
  /** Backtrack manager for preprocessor and rewriter. */
  std::unique_ptr<backtrack::BacktrackManager> d_simplify_backtrack_mgr;
  /** Node simplification cache for preprocessor and rewriter. */
  std::unique_ptr<preprocess::SimplifyCache> d_simplify_cache;
  /** The associated rewriter. */
  Rewriter d_rewriter;
};

}  // namespace bzla

#endif
