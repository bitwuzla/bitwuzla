#ifndef BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED

#include <memory>

#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "env.h"
#include "solver/solver_state.h"
#include "util/logger.h"

namespace bzla::abstract {

class AbstractionLemma;
enum class LemmaKind : uint32_t;

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

  /**
   * @return True if processed assertion contains an abstracted term. Required
   * for unsat cores.
   */
  bool is_processed_assertion(const Node& assertion);

  /**
   * @return Original assertion without abstracted terms. Required for unsat
   * cores.
   */
  const Node& get_original_assertion(const Node& processed_assertion);

 private:
  /** @return Whether this term should be abstracted. */
  bool abstract(const Node& node) const;

  const Node& get_abstraction(const Node& node);

  /** Add original term and its abstraction. */
  void add_abstraction(const Node& node, const Node& abstr);

  /** @return Abstraction UF for given node based on its type and kind. */
  const Node& abstr_uf(const Node& node);

  /** Check assignment of abstraction and add lemma if needed. */
  void check_term_abstraction(const Node& abstr);
  /** Check assignment of ITE abstraction and lazily expand if needed. */
  void check_term_abstraction_ite(const Node& abstr, const Node& node);
  /** Check assertion abstractions, and add refinement if needed. */
  bool check_assertion_abstractions();

  bool check_lemma(const AbstractionLemma* lem,
                   const Node& val_x,
                   const Node& val_s,
                   const Node& val_t,
                   const Node& x,
                   const Node& s,
                   const Node& t);

  /** Send lemma but make sure not to abstract terms in it. */
  bool lemma_no_abstract(const Node& lemma, LemmaKind lk);
  /** Send lemma, abstract terms in it. */
  bool lemma_abstract(const Node& lemma, LemmaKind lk);

  /** Utility to compute score for lemma schema. */
  void score_lemmas(node::Kind k,
                    uint64_t bv_size,
                    std::unordered_map<LemmaKind, uint64_t>& rank_map) const;
  void rank_lemmas_by_circuit_size();
  void rank_lemmas_by_score();

  void print_initial_lemmas() const;

#ifndef NDEBUG
  void verify_lemmas() const;
#endif

  Env& d_env;
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
  /** Assertion cache, used for tracking unsat cores. */
  std::unordered_map<Node, Node> d_abstraction_cache_assertions;
  /** Stores abstraction UFs based on kind and type. */
  std::unordered_map<node::Kind, std::unordered_map<Type, Node>> d_abstr_ufs;
  /** Stores abstraction consts for assertions. */
  std::unordered_map<Node, Node> d_abstr_consts;
  /** Stores abstraction consts for equalities. */
  std::unordered_map<Node, std::vector<Node>> d_abstr_equal;
  /** Stores enabled refinement lemmas based on kind. */
  std::unordered_map<node::Kind, std::vector<std::unique_ptr<AbstractionLemma>>>
      d_abstr_lemmas;
  /** Maps the number of value instantiations per abstracted term. */
  std::unordered_map<Node, uint64_t> d_value_insts;
  /** Number of times a value instantiation was a square multiplication. */
  std::unordered_map<Node, uint64_t> d_value_insts_square;
  /** Abstracted assertions. */
  backtrack::vector<Node> d_assertion_abstractions;
  /** Stores refined assertions. */
  backtrack::unordered_set<Node> d_assertion_abstractions_cache;
  /** Buffer used for delaying sending lemmas. */
  std::vector<std::tuple<Node, Node, LemmaKind>> d_lemma_buffer;
  /** Caches lemmas sent to solver engine. */
  backtrack::unordered_set<Node> d_lemma_cache;

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
  /** Incrementally bit-blast bvmul and bvadd starting from LSB. */
  bool d_opt_inc_bitblast;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_terms;
    uint64_t& num_checks;
    util::HistogramStatistic& terms;
    util::HistogramStatistic& lemmas;
    util::TimerStatistic& time_check;
  } d_stats;
};

}  // namespace bzla::abstract

#endif
