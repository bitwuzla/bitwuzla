#ifndef BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED
#define BZLA_PREPROCESS_PASS_VARIABLE_SUBSTITUTION_H_INCLUDED

#include "backtrack/vector.h"
#include "node/unordered_node_ref_map.h"
#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassVariableSubstitution : public PreprocessingPass
{
 public:
  PassVariableSubstitution(Rewriter& rewriter,
                           backtrack::BacktrackManager* backtrack_mgr)
      : PreprocessingPass(rewriter), d_substitutions(backtrack_mgr)
  {
  }

  void apply(std::vector<std::pair<Node, size_t>>& assertions) override;

  void register_assertion(const Node& assertion);

 private:
  void remove_indirect_cycles(std::unordered_map<Node, Node>& substs) const;

  bool is_direct_cycle(const Node& var, const Node& term) const;

  Node substitute(const Node& assertion,
                  const std::unordered_map<Node, Node>& substitutions,
                  node::unordered_node_ref_map<Node>& cache) const;

  backtrack::vector<std::tuple<Node, Node, size_t>> d_substitutions;
};

}  // namespace bzla::preprocess::pass
#endif
