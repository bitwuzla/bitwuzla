#include "solver/bv/abstraction_module.h"

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "solver/bv/abstraction_lemmas.h"
#include "solver/bv/bv_solver.h"

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
      d_active_abstractions(state.backtrack_mgr()),
      d_minimum_size(env.options().bv_abstraction()),
      d_stats(env.statistics(), "solver::bv::abstraction::")
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

  auto& urem_abstr_lemmas = d_abstr_lemmas[Kind::BV_UREM];
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF1>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF2>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF3>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF4>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF5>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF6>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF7>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF8>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF9>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF10>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF11>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF12>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF13>());
  urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF14>());
}

AbstractionModule::~AbstractionModule() {}

void
AbstractionModule::register_abstraction(const Node& node)
{
  assert(is_abstraction(node));
  d_active_abstractions.push_back(node);
}

bool
AbstractionModule::is_abstraction(const Node& node)
{
  return d_abstractions_rev.find(node) != d_abstractions_rev.end();
}

void
AbstractionModule::check()
{
  Log(1);
  Log(1) << "*** check abstractions";
  // score_lemmas(Kind::BV_MUL);
  util::Timer timer(d_stats.time_check);
  ++d_stats.num_checks;
  // New abstraction may be added while checking
  for (size_t i = 0; i < d_active_abstractions.size(); ++i)
  {
    check_abstraction(d_active_abstractions[i]);
  }
}

const Node&
AbstractionModule::process(const Node& assertion)
{
  node_ref_vector visit{assertion};

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_abstraction_cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      if (abstract(cur))
      {
        std::vector<Node> children;
        for (const Node& c : cur)
        {
          auto itt = d_abstraction_cache.find(c);
          assert(itt != d_abstraction_cache.end());
          children.push_back(itt->second);
        }
        Node func       = abstr_uf(cur);
        NodeManager& nm = NodeManager::get();
        it->second = nm.mk_node(Kind::APPLY, {func, children[0], children[1]});
        add_abstraction(cur, it->second);
      }
      else
      {
        it->second = utils::rebuild_node(cur, d_abstraction_cache);
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  return d_abstraction_cache.at(assertion);
}

bool
AbstractionModule::is_processed(const Node& assertion)
{
  auto it = d_abstraction_cache.find(assertion);
  return it != d_abstraction_cache.end() && it->second != assertion;
}

const Node&
AbstractionModule::abstracted_term(const Node& abstraction)
{
  assert(is_abstraction(abstraction));
  auto it = d_abstractions_rev.find(abstraction);
  assert(it != d_abstractions_rev.end());
  return it->second;
}

/* --- AbstractionModule private -------------------------------------------- */

bool
AbstractionModule::abstract(const Node& node) const
{
  Kind k = node.kind();
  return d_abstr_lemmas.find(k) != d_abstr_lemmas.end()
         && node.type().bv_size() >= d_minimum_size;
}

const Node&
AbstractionModule::get_abstraction(const Node& node)
{
  auto it = d_abstractions.find(node);
  assert(it != d_abstractions.end());
  return it->second;
}

void
AbstractionModule::add_abstraction(const Node& node, const Node& abstr)
{
  assert(abstr.kind() == Kind::APPLY);
  assert(d_abstr_lemmas.find(node.kind()) != d_abstr_lemmas.end());
  assert(d_abstractions.find(node) == d_abstractions.end());
  d_abstractions.emplace(node, abstr);
  d_abstractions_rev.emplace(abstr, node);
}

const Node&
AbstractionModule::abstr_uf(const Node& node)
{
  Type bvt            = node.type();
  auto& map           = d_abstr_ufs[node.kind()];
  auto [it, inserted] = map.emplace(bvt, Node());
  if (inserted)
  {
    std::stringstream ss;
    ss << node.kind() << "_" << bvt.bv_size();
    NodeManager& nm = NodeManager::get();
    Type t          = nm.mk_fun_type({bvt, bvt, bvt});
    it->second      = nm.mk_const(t, ss.str());
  }
  return it->second;
}

void
AbstractionModule::check_abstraction(const Node& abstr)
{
  Log(2) << "Check abstraction: " << abstr;

  auto ita = d_abstractions_rev.find(abstr);
  assert(ita != d_abstractions_rev.end());
  const Node& node = ita->second;

  Kind kind = node.kind();
  assert(kind == Kind::BV_MUL || kind == Kind::BV_UDIV
         || kind == Kind::BV_UREM);

  NodeManager& nm   = NodeManager::get();
  const Node& x     = abstr[1];
  const Node& s     = abstr[2];
  const Node& t     = abstr;
  Node val_x        = d_solver_state.value(x);
  Node val_s        = d_solver_state.value(s);
  Node val_t        = d_solver_state.value(t);
  Node val_expected = d_rewriter.rewrite(nm.mk_node(kind, {val_x, val_s}));

  if (val_t == val_expected)
  {
    return;
  }

  Log(2) << "x: " << x;
  Log(2) << "s: " << s;
  Log(2) << "t: " << t;
  Log(2) << "val_x: " << val_x;
  Log(2) << "val_s: " << val_s;
  Log(2) << "val_t: " << val_t;
  bool added_lemma = false;
  auto it          = d_abstr_lemmas.find(kind);
  assert(it != d_abstr_lemmas.end());
  const auto& to_check = it->second;
  for (const auto& lem : to_check)
  {
    Node inst = d_rewriter.rewrite(lem->instance(val_x, val_s, val_t));
    assert(inst.is_value());
    if (!inst.value<bool>())
    {
      Log(2) << lem->kind() << " inconsistent";
      Node lemma = lem->instance(x, s, t);
      d_solver_state.lemma(lemma);
      added_lemma = true;
      d_stats.lemmas << lem->kind();
      break;
    }
    if (KindInfo::is_commutative(kind))
    {
      inst = d_rewriter.rewrite(lem->instance(val_s, val_x, val_t));
      assert(inst.is_value());
      if (!inst.value<bool>())
      {
        Log(2) << lem->kind() << " (comm.) inconsistent";
        Node lemma = lem->instance(s, x, t);
        d_solver_state.lemma(lemma);
        added_lemma = true;
        d_stats.lemmas << lem->kind();
        break;
      }
    }
  }

  // Inconsistent value, but no abstraction violated, add value-based lemma.
  if (!added_lemma)
  {
    LemmaKind lk;
    if (kind == Kind::BV_MUL)
    {
      lk = LemmaKind::MUL_VALUE;
    }
    else if (kind == Kind::BV_UDIV)
    {
      lk = LemmaKind::UDIV_VALUE;
    }
    else
    {
      lk = LemmaKind::UREM_VALUE;
    }
    Log(2) << lk << " inconsistent";
    Node lemma = nm.mk_node(Kind::IMPLIES,
                            {nm.mk_node(Kind::AND,
                                        {
                                            nm.mk_node(Kind::EQUAL, {x, val_x}),
                                            nm.mk_node(Kind::EQUAL, {s, val_s}),
                                        }),
                             nm.mk_node(Kind::EQUAL, {t, val_expected})});
    d_solver_state.lemma(lemma);
    d_stats.lemmas << lk;
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

  // Create all possible values [0, max[
  for (uint64_t i = 0; i < max; ++i)
  {
    values.push_back(nm.mk_value(BitVector::from_ui(size, i)));
  }

  // Compute all results for kind
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
    // Compute result for each triplet (x, s, t)
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
          // Count cases when lemma is true (including false positives)
          if (res)
          {
            ++score;
            if (values[k] == expected)
            {
              ++score_expected;
            }
          }
          // Count number of ruled out triplets
          else if (it->second)
          {
            --final_score;
          }
          it->second &= res;
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
            << "% (wrong results: " << final_score - (max * max) << std::endl;
  std::cout << "optimal score: " << max * max << " "
            << static_cast<double>(max * max) / max_score * 100 << std::endl;
  done = true;
}

AbstractionModule::Statistics::Statistics(util::Statistics& stats,
                                          const std::string& prefix)
    : num_abstractions(stats.new_stat<uint64_t>(prefix + "num_abstractions")),
      num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}

}  // namespace bzla::bv::abstraction
