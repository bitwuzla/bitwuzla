/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include <unordered_map>

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "node/node.h"
#include "preprocess/assertion_vector.h"

namespace bzla {

class Env;

namespace util {
  class Logger;
}

namespace preprocess {

/**
 * Interface required to be implemented by preprocessing passes.
 */
class PreprocessingPass
{
  using SubstitutionMap = backtrack::unordered_map<Node, Node>;

 public:
  /**
   * Constructor.
   * @param env The associated environment.
   */
  PreprocessingPass(Env& env, backtrack::BacktrackManager* backtrack_mgr);
  virtual ~PreprocessingPass() {};

  /**
   * Apply preprocessing pass to the current set of assertions.
   * @param assertions The current set of assertions.
   */
  virtual void apply(AssertionVector& assertions) = 0;

  /**
   * Apply preprocessing pass to given term.
   * @param term The term to apply this preprocessing pass to.
   */
  virtual Node process(const Node& term) { return term; }

  void clear_cache();

 protected:
  /**
   * Count number of parents for all nodes reachable from `node`.
   *
   * @param parents Parents map to store result.
   * @param cache Traversal cache.
   */
  void count_parents(const Node& node,
                     std::unordered_map<Node, uint64_t>& parents,
                     std::unordered_set<Node>& cache);

  /**
   * Replace all occurrences of `substititutions` in `node.
   * @param node          The node.
   * @param substitutions A Map from node that should be substituted to node to
   *                      substitute with.
   * @param cache         The substitution cache, maps node to its substitution
   *                      if applicable, else to itself.
   * @return The rewritten form of the node with all occurrences in the
   *         substitution map replaced by their substitutions and the number
   *         of substitutions performed.
   */
  std::pair<Node, uint64_t> substitute(
      const Node& node,
      const SubstitutionMap& substitutions,
      std::unordered_map<Node, Node>& cache) const;

  /**
   * Mark assertion as processed.
   *
   * @param assertion The assertion to cache.
   * @return Whether assertion was added to the cache or not.
   */
  bool cache_assertion(const Node& assertion);

  /** @return Whether assertion was already processed. */
  bool processed(const Node& assertion);

  /** The associated environment. */
  Env& d_env;
  /** The associated logger. */
  util::Logger& d_logger;

 private:
  std::unordered_set<Node> d_processed_assertions;
};

}  // namespace preprocess
}  // namespace bzla
#endif
