#ifndef BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_MODULE_H_INCLUDED

#include <memory>

#include "backtrack/unordered_map.h"
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

  bool abstract(const Node& node) const;

  void register_abstraction(const Node& node);

  void check();

 private:
  const Node& get_abstraction(const Node& node);

  const Node& mul_uf(const Node& node);

  void check_abstraction(const Node& node);

  util::Logger& d_logger;
  SolverState& d_solver_state;
  Rewriter& d_rewriter;

  backtrack::unordered_map<Node, Node> d_abstractions;
  backtrack::vector<Node> d_active_abstractions;

  std::unordered_map<Type, Node> d_mul_ufs;
  std::unordered_map<node::Kind, std::vector<std::unique_ptr<AbstractionLemma>>>
      d_abstr_lemmas;

  uint64_t d_minimum_size;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_abstractions;
    uint64_t& num_checks;
    util::HistogramStatistic& lemmas;
    util::TimerStatistic& time_check;
  } d_stats;
};

}  // namespace bzla::bv::abstraction

#endif
