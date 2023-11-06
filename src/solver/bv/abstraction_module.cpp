#include "solver/bv/abstraction_module.h"

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "solver/bv/abstraction_lemmas.h"

namespace std {

template <>
struct hash<std::pair<uint64_t, uint64_t>>
{
  size_t operator()(const std::pair<uint64_t, uint64_t>& p) const
  {
    return 547789289u * p.first + 786695309u * p.second;
  }
};

template <>
struct hash<std::tuple<uint64_t, uint64_t, uint64_t>>
{
  size_t operator()(const std::tuple<uint64_t, uint64_t, uint64_t>& p) const
  {
    return 547789289u * std::get<0>(p) + 786695309u * std::get<1>(p)
           + 7 * std::get<2>(p);
  }
};

}  // namespace std

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
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_IC>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ZERO>());
  mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ONE>());
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

  auto& udiv_abstr_lemmas = d_abstr_lemmas[Kind::BV_UDIV];
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF1>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF2>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF3>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF4>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF5>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF6>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF7>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF8>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF9>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF10>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF11>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF12>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF13>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF14>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF15>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF16>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF17>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF18>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF19>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF20>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF21>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF22>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF23>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF24>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF25>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF26>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF27>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF28>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF29>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF30>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF31>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF32>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF33>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF34>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF35>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF36>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF37>());
  udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF38>());
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
  score_lemmas(Kind::BV_UDIV);
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
  Node val_x           = d_solver_state.value(node[0]);
  Node val_s           = d_solver_state.value(node[1]);
  Node val_t           = d_solver_state.value(node);
  if (node.kind() == Kind::BV_MUL)
  {
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
  else if (node.kind() == Kind::BV_UREM)
  {
    // TODO
  }
}

void
AbstractionModule::score_lemmas(Kind kind) const
{
  static bool done = false;
  if (done) return;
  NodeManager& nm = NodeManager::get();
  uint64_t size   = 7;
  uint64_t max    = 1;
  for (size_t i = 0; i < size; ++i)
  {
    max *= 2;
  }
  std::vector<Node> values;
  std::unordered_map<std::pair<uint64_t, uint64_t>, Node> results;
  std::unordered_map<std::tuple<uint64_t, uint64_t, uint64_t>, bool>
      results_lemmas;

  for (uint64_t i = 0; i < max; ++i)
  {
    values.push_back(nm.mk_value(BitVector::from_ui(size, i)));
  }
  for (uint64_t i = 0; i < values.size(); ++i)
  {
    for (uint64_t j = 0; j < values.size(); ++j)
    {
      auto p = std::make_pair(i, j);
      results.emplace(
          p, d_rewriter.rewrite(nm.mk_node(kind, {values[i], values[j]})));
    }
  }

  uint64_t max_score   = max * max * max;
  uint64_t final_score = max_score;
  std::cout << "lemma score (worst: " << final_score << ", best: " << max * max
            << ")" << std::endl;
  for (const auto& lem : d_abstr_lemmas.at(kind))
  {
    uint64_t score            = 0;
    uint64_t score_expected   = 0;
    uint64_t prev_final_score = final_score;
    for (uint64_t i = 0; i < values.size(); ++i)
    {
      for (uint64_t j = 0; j < values.size(); ++j)
      {
        auto itr = results.find(std::make_pair(i, j));
        assert(itr != results.end());
        const Node& expected = itr->second;
        for (uint64_t k = 0; k < values.size(); ++k)
        {
          auto t    = std::make_tuple(i, j, k);
          Node inst = d_rewriter.rewrite(
              lem->instance(values[i], values[j], values[k]));
          assert(inst.is_value());
          auto res = inst.value<bool>();
          if (kind == Kind::BV_MUL)
          {
            Node instc = d_rewriter.rewrite(
                lem->instance(values[j], values[i], values[k]));
            auto resc = instc.value<bool>();
            res       = res & resc;
          }
          auto [it, _] = results_lemmas.emplace(t, true);
          if (res)
          {
            ++score;
            if (values[k] == expected)
            {
              ++score_expected;
            }
          }
          else if (it->second)
          {
            --final_score;
          }
          it->second = it->second & res;
        }
      }
    }
    assert(score_expected == max * max);
    int64_t diff = final_score - prev_final_score;
    std::cout << lem->kind() << ": " << score << "/" << max_score
              << " (final: " << final_score << ", diff: " << diff << ", "
              << static_cast<double>(diff) / max_score * 100 << "%)"
              << std::endl;
  }
  std::cout << "final score:   " << final_score << " "
            << static_cast<double>(final_score) / max_score * 100
            << "% (wrong results: " << final_score - (max * max) << ")"
            << std::endl;
  std::cout << "optimal score: " << max * max << " "
            << static_cast<double>(max * max) / max_score * 100 << "%"
            << std::endl;
  done = true;
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
