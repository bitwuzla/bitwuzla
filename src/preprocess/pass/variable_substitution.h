#ifndef BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED
#define BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "node/unordered_node_ref_map.h"
#include "preprocess/preprocessing_pass.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassVariableSubstitution : public PreprocessingPass
{
 public:
  PassVariableSubstitution(Env& env, backtrack::BacktrackManager* backtrack_mgr)
      : PreprocessingPass(env),
        d_backtrack_mgr(backtrack_mgr),
        d_substitutions(backtrack_mgr),
        d_substitution_assertions(backtrack_mgr),
        d_cache(backtrack_mgr)
  {
  }

  void apply(AssertionVector& assertions) override;

  /** Process term and apply currently cached substitutions. */
  Node process(const Node& term) override;

 private:
  void remove_indirect_cycles(std::unordered_map<Node, Node>& substs) const;

  bool is_direct_cycle(const Node& var, const Node& term) const;

  Node substitute(const Node& term,
                  const std::unordered_map<Node, Node>& substitutions,
                  std::unordered_map<Node, Node>& cache) const;

  bool register_assertion(const Node& assertion);

  /** Only required to check the current assertion level. */
  const backtrack::BacktrackManager* d_backtrack_mgr;
  backtrack::unordered_map<Node, Node> d_substitutions;
  backtrack::unordered_set<Node> d_substitution_assertions;

  /** Backtrackable cache. */
  class Cache : public backtrack::Backtrackable
  {
   public:
    Cache(backtrack::BacktrackManager* mgr);

    void push() override;

    void pop() override
    {
      // Nothing to do
    }

    /** @return Current substitution map. */
    std::unordered_map<Node, Node>& substitutions();

    /** @return Current substitution cache. */
    std::unordered_map<Node, Node>& cache();

   private:
    /** Backtrackable substitution map. One map per scope level. */
    backtrack::vector<std::unordered_map<Node, Node>> d_map;
    /** Backtrackable substitution cache. One cache per scope level. */
    backtrack::vector<std::unordered_map<Node, Node>> d_cache;
  };

  /** Backtrackable substitution cache. */
  Cache d_cache;
};

}  // namespace bzla::preprocess::pass
#endif
