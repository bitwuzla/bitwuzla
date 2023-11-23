#ifndef BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED

#include <memory>

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "env.h"
#include "solver/solver_state.h"
#include "util/logger.h"

namespace bzla::bv::abstraction {

class AbstractionLemma;
enum class LemmaKind;

class AbstractionModule
{
 public:
  AbstractionModule(Env& env, SolverState& state);
  ~AbstractionModule();

  /** Register abstraction as active. */
  void register_abstraction(const Node& node);

  /** @return True if given node is an abstraction. */
  bool is_abstraction(const Node& node);

  /** Check currently active abstractions. */
  void check();

  /** Process assertion to abstract relevant terms. */
  const Node& process(const Node& assertion, bool is_lemma);

  /** @return True if processed assertion contains an abstracted term. */
  bool is_processed(const Node& assertion);

  const Node& abstracted_term(const Node& abstraction);

 private:
  /** @return Whether this term should be abstracted. */
  bool abstract(const Node& node) const;

  const Node& get_abstraction(const Node& node);

  /** Add original term and its abstraction. */
  void add_abstraction(const Node& node, const Node& abstr);

  /** @return Abstraction UF for given node based on its type and kind. */
  const Node& abstr_uf(const Node& node);

  /** Check assignment of abstraction and add lemma if needed. */
  void check_abstraction(const Node& node);

  bool check_assertion_abstractions();

  /** Send lemma but make sure not to abstract terms in it. */
  void lemma_no_abstract(const Node& lemma, LemmaKind lk);

  /** Utility to compute score for lemma schema. */
  void score_lemmas(node::Kind k) const;

  util::Logger& d_logger;
  SolverState& d_solver_state;
  Rewriter& d_rewriter;

  /** Currently registered (active) abstractions. */
  backtrack::vector<Node> d_active_abstractions;
  /** Maps abstracted terms (original) to abstractions. */
  std::unordered_map<Node, Node> d_abstractions;
  /** Maps abstractions to abstracted terms (original). */
  std::unordered_map<Node, Node> d_abstractions_rev;
  /** Cache for process(). */
  std::unordered_map<Node, Node> d_abstraction_cache;
  /** Stores abstraction UFs based on kind and type. */
  std::unordered_map<node::Kind, std::unordered_map<Type, Node>> d_abstr_ufs;
  /** Stores abstraction consts for assertions. */
  std::unordered_map<Node, Node> d_abstr_consts;
  /** Stores enabled refinement lemmas based on kind. */
  std::unordered_map<node::Kind, std::vector<std::unique_ptr<AbstractionLemma>>>
      d_abstr_lemmas;
  /** Maps the number of value instantiations per abstracted term. */
  std::unordered_map<Node, uint64_t> d_value_insts;
  /** Abstracted assertions. */
  backtrack::vector<Node> d_assertion_abstractions;
  /** Stores refined assertions. */
  backtrack::unordered_set<Node> d_assertion_abstractions_cache;

  /** Indicates whether lemma was added during check(). */
  bool d_added_lemma;

  /** Minimum size of bit-vector operators to abstract. */
  uint64_t d_opt_minimum_size;
  /** Eager lemma mode. */
  bool d_opt_eager_refine;
  /** Value instantiation limit per abstraction. */
  uint64_t d_opt_value_inst_limit;
  /** Perform value instantiation only. */
  bool d_opt_value_inst_only;
  /** Abstract assertions. */
  bool d_opt_abstract_assertions;
  /** Number of assertion refinements per check. */
  uint64_t d_opt_assertion_refinements;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_terms;
    uint64_t& num_lemmas;
    uint64_t& num_checks;
    util::HistogramStatistic& terms;
    util::HistogramStatistic& lemmas;
    util::TimerStatistic& time_check;
  } d_stats;
};

}  // namespace bzla::bv::abstraction

#endif
