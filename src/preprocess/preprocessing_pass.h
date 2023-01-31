#ifndef BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSING_PASS_H_INCLUDED

#include <unordered_map>

#include "backtrack/unordered_set.h"
#include "node/node.h"

namespace bzla {

class Env;

namespace util {
  class Logger;
}

namespace backtrack {
class AssertionView;
template <class K, class V>
class unordered_map;
}

namespace preprocess {

/**
 * Wrapper around AssertionView for manipulating assertions for a given level.
 */
class AssertionVector
{
  friend class Preprocessor;

 public:
  AssertionVector(backtrack::AssertionView& view);

  /**
   * Push back new assertion.
   *
   * @note Increments d_changed.
   */
  void push_back(const Node& assertion);

  /** @return The size of the vector. */
  size_t size() const;

  /** @return Assertion at given index. */
  const Node& operator[](std::size_t index) const;

  /**
   * Replace assertion at index i.
   *
   * @note Increments d_changed if contents of vector was modified.
   *
   * @param i The index of the assertion to replace.
   * @param assertion The new assertion.
   */
  void replace(size_t index, const Node& assertion);

  /**
   * Determines whether the assertions in the vector are the intial assertions
   * on the assertion stack, i.e., the assertions on the stack before the first
   * check-sat call.
   */
  bool initial_assertions() const;

 private:
  /** Reset d_changed. */
  void reset_modified();

  /** @return The number of changed/added assertions since the last reset. */
  size_t num_modified() const;

  /** Determines if vector was modified since the last reset. */
  bool modified() const;

  /** The wrapper assertion view. */
  backtrack::AssertionView& d_view;
  /** The scope level of this set of assertions. */
  size_t d_level;
  /** Start index for assertions. */
  size_t d_begin;
  /** Number of modified (changed, added) assertions since last reset. */
  size_t d_modified;
};

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
  /** @return The parents count for all currently reachable nodes. */
  std::unordered_map<Node, uint64_t> count_parents(AssertionVector& assertions);

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
   * @return Whether assertion was added to the cache or not.x
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
