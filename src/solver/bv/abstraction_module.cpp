#include "solver/bv/abstraction_module.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "solver/bv/abstraction_lemmas.h"

namespace bzla::bv::abstraction {

using namespace node;

/* --- AbstractionModule public --------------------------------------------- */

AbstractionModule::AbstractionModule(Env& env, SolverState& state)
    : d_logger(env.logger()),
      d_solver_state(state),
      d_rewriter(env.rewriter()),
      d_abstractions(state.backtrack_mgr()),
      d_active_abstractions(state.backtrack_mgr()),
      d_minimum_size(env.options().bv_abstraction()),
      d_stats(env.statistics())
{
  auto& mul_abstr_lemmas = d_abstr_lemmas[Kind::BV_MUL];
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ZERO>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ONE>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_IC>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_NEG>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ODD>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF1>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF2>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF3>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF4>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF5>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF6>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF7>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF8>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF9>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF10>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF11>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF12>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF13>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF14>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF15>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF16>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF17>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF18>());
}

AbstractionModule::~AbstractionModule() {}

bool
AbstractionModule::abstract(const Node& node) const
{
  return node.kind() == Kind::BV_MUL && node.type().bv_size() >= d_minimum_size;
}

void
AbstractionModule::register_abstraction(const Node& node)
{
  auto [it, inserted] = d_abstractions.emplace(node, Node());
  if (inserted)
  {
    Node func       = mul_uf(node);
    NodeManager& nm = NodeManager::get();
    it->second      = nm.mk_node(Kind::APPLY, {func, node[0], node[1]});
    d_solver_state.lemma(nm.mk_node(Kind::EQUAL, {node, it->second}));
    d_active_abstractions.push_back(node);
    ++d_stats.num_abstractions;
    Log(1) << "Register abstraction: " << node;
  }
}

void
AbstractionModule::check()
{
  util::Timer timer(d_stats.time_check);
  ++d_stats.num_checks;
  for (const Node& abstr : d_active_abstractions)
  {
    check_abstraction(abstr);
  }
}

/* --- AbstractionModule private -------------------------------------------- */

const Node&
AbstractionModule::get_abstraction(const Node& node)
{
  auto it = d_abstractions.find(node);
  assert(it != d_abstractions.end());
  return it->second;
}

const Node&
AbstractionModule::mul_uf(const Node& node)
{
  assert(node.kind() == Kind::BV_MUL);
  NodeManager& nm     = NodeManager::get();
  Type bvt            = node.type();
  Type t              = nm.mk_fun_type({bvt, bvt, bvt});
  auto [it, inserted] = d_mul_ufs.emplace(t, Node());
  if (inserted)
  {
    std::stringstream ss;
    ss << "bvmul_" << bvt.bv_size();
    it->second = nm.mk_const(t, ss.str());
  }
  return it->second;
}

void
AbstractionModule::check_abstraction(const Node& node)
{
  Log(2) << "Check abstraction: " << node;
  auto it = d_abstr_lemmas.find(node.kind());
  assert(it != d_abstr_lemmas.end());
  const auto& to_check = it->second;
  NodeManager& nm      = NodeManager::get();
  if (node.kind() == Kind::BV_MUL)
  {
    Node val_x = d_solver_state.value(node[0]);
    Node val_s = d_solver_state.value(node[1]);
    Node val_t = d_solver_state.value(node);
    Node val_expected =
        nm.mk_value(val_x.value<BitVector>().bvmul(val_s.value<BitVector>()));
    if (val_t == val_expected)
    {
      return;
    }
    Log(2) << "x: " << node[0];
    Log(2) << "s: " << node[1];
    Log(2) << "t: " << node;
    Log(2) << "val_x: " << val_x;
    Log(2) << "val_s: " << val_s;
    Log(2) << "val_t: " << val_t;
    bool added_lemma = false;
    for (const auto& lem : to_check)
    {
      Node inst = d_rewriter.rewrite(lem->instance(val_x, val_s, val_t));
      assert(inst.is_value());
      if (!inst.value<bool>())
      {
        Log(2) << lem->kind() << " inconsistent";
        Node lemma = lem->instance(node[0], node[1], get_abstraction(node));
        d_solver_state.lemma(lemma);
        added_lemma = true;
        d_stats.lemmas << lem->kind();
        break;
      }
      inst = d_rewriter.rewrite(lem->instance(val_s, val_x, val_t));
      assert(inst.is_value());
      if (!inst.value<bool>())
      {
        Log(2) << lem->kind() << " (comm.) inconsistent";
        Node lemma = lem->instance(node[1], node[0], get_abstraction(node));
        d_solver_state.lemma(lemma);
        added_lemma = true;
        d_stats.lemmas << lem->kind();
        break;
      }
    }

    // Inconsistent value, but no abstraction violated, add value-based lemma.
    if (!added_lemma)
    {
      Log(2) << LemmaKind::MUL_VALUE << " inconsistent";
      Node lemma = nm.mk_node(
          Kind::IMPLIES,
          {nm.mk_node(Kind::AND,
                      {
                          nm.mk_node(Kind::EQUAL, {node[0], val_x}),
                          nm.mk_node(Kind::EQUAL, {node[1], val_s}),
                      }),
           nm.mk_node(Kind::EQUAL, {get_abstraction(node), val_expected})});
      d_solver_state.lemma(lemma);
      d_stats.lemmas << LemmaKind::MUL_VALUE;
    }
  }
}

AbstractionModule::Statistics::Statistics(util::Statistics& stats)
    : num_abstractions(
        stats.new_stat<uint64_t>("bv::abstraction::num_abstractions")),
      num_checks(stats.new_stat<uint64_t>("bv::abstraction::num_checks")),
      lemmas(
          stats.new_stat<util::HistogramStatistic>("bv::abstraction::lemmas")),
      time_check(
          stats.new_stat<util::TimerStatistic>("bv::abstraction::time_check"))
{
}

}  // namespace bzla::bv::abstraction
