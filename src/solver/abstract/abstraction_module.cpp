#include "solver/abstract/abstraction_module.h"

#include <algorithm>

#include "bv/bitvector.h"
#include "node/kind_info.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "solver/abstract/abstraction_lemmas.h"
#include "solver/bv/bv_solver.h"
#include "util/hash_pair.h"

#ifndef NDEBUG
#include "solving_context.h"
#endif

namespace std {

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

namespace bzla::abstract {

using namespace node;

/* --- AbstractionModule public --------------------------------------------- */

AbstractionModule::AbstractionModule(Env& env, SolverState& state)
    : d_logger(env.logger()),
      d_solver_state(state),
      d_rewriter(env.rewriter()),
      d_active_abstractions(state.backtrack_mgr()),
      d_assertion_abstractions(state.backtrack_mgr()),
      d_assertion_abstractions_cache(state.backtrack_mgr()),
      d_opt_minimum_size(env.options().abstraction_bv_size()),
      d_opt_eager_refine(env.options().abstraction_eager_refine()),
      d_opt_value_inst_limit(env.options().abstraction_value_limit()),
      d_opt_value_inst_only(env.options().abstraction_value_only()),
      d_opt_abstract_assertions(env.options().abstraction_assert()),
      d_opt_assertion_refinements(env.options().abstraction_assert_refs()),
      d_stats(env.statistics(), "solver::abstract::")
{
  bool opt_initial_lemmas = env.options().abstraction_initial_lemmas();

  if (env.options().abstraction_bv_mul())
  {
    auto& mul_abstr_lemmas = d_abstr_lemmas[Kind::BV_MUL];
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_IC>());
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ZERO>());
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ONE>());
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_NEG>());
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ODD>());
    if (!opt_initial_lemmas)
    {
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
  }

  if (env.options().abstraction_bv_udiv())
  {
    auto& udiv_abstr_lemmas = d_abstr_lemmas[Kind::BV_UDIV];
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF1>());
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF2>());
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF3>());
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF4>());
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF5>());
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF6>());
    if (!opt_initial_lemmas)
    {
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
      // not correct for size 10
      // udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF22>());
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
      // not correct from size 10
      // udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF35>());
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF36>());
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF37>());
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF38>());
    }
  }

  if (env.options().abstraction_bv_urem())
  {
    auto& urem_abstr_lemmas = d_abstr_lemmas[Kind::BV_UREM];
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF1>());
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF2>());
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF3>());
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF4>());
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF5>());
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF6>());
    if (!opt_initial_lemmas)
    {
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF7>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF8>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF9>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF10>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF11>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF12>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF13>());
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF14>());
    }
  }

  // Enables incremental bit-blasting of equalities
  if (env.options().abstraction_eq())
  {
    d_abstr_lemmas.try_emplace(Kind::EQUAL);
  }

  if (env.options().abstraction_ite())
  {
    d_abstr_lemmas.try_emplace(Kind::ITE);
  }

  if (env.options().abstraction_bv_add())
  {
    auto& add_abstr_lemmas = d_abstr_lemmas[Kind::BV_ADD];
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_ZERO>());
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_SAME>());
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_INV>());
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_OVFL>());
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_NOOFVL>());
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_OR>());
    if (!opt_initial_lemmas)
    {
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF1>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF2>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF3>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF4>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF5>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF6>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF7>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF8>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF9>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF10>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF11>());
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF12>());
    }
  }
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
  // score_lemmas(Kind::BV_ADD);
  util::Timer timer(d_stats.time_check);
  ++d_stats.num_checks;

#ifndef NDEBUG
  // verify_lemmas();
#endif

  d_added_lemma = false;

  // New abstraction may be added while checking
  for (size_t i = 0; i < d_active_abstractions.size(); ++i)
  {
    // Do not use reference here, since d_active_abstractions may change when
    // calling check_abstraction().
    const Node abstr_term = d_active_abstractions[i];
    if (d_solver_state.is_relevant(abstr_term))
    {
      check_abstraction(abstr_term);
    }
  }

  // Check abstracted assertions
  if (!d_added_lemma && d_opt_abstract_assertions)
  {
    check_assertion_abstractions();
  }

  // Abstraction refinements that are added as "last resort" are only added if
  // we expaned all violated assertions.
  // This includes:
  //   - value instantiation lemmas
  //   - bit-blasting lemmas
  if (!d_added_lemma)
  {
    for (const auto& [node, lemma, lk] : d_lemma_buffer)
    {
      lemma_no_abstract(lemma, lk);
      // Increment counter for value instantiations
      if (is_lemma_kind_value(lk))
      {
        ++d_value_insts[node];
      }
    }
  }
  d_lemma_buffer.clear();
}

const Node&
AbstractionModule::process(const Node& assertion, bool is_lemma)
{
  NodeManager& nm = NodeManager::get();

  node_ref_vector visit{assertion};
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = d_abstraction_cache.try_emplace(cur);
    if (inserted)
    {
      // No need to go below quantifiers since abstraction will happen when
      // quantifier instantiation is added.
      if (cur.kind() == Kind::FORALL)
      {
        it->second = cur;
      }
      else
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      if (abstract(cur))
      {
        Node func = abstr_uf(cur);
        std::vector<Node> children{func};
        for (const Node& c : cur)
        {
          auto itt = d_abstraction_cache.find(c);
          assert(itt != d_abstraction_cache.end());
          children.push_back(itt->second);
        }
        it->second = d_rewriter.rewrite(nm.mk_node(Kind::APPLY, children));
        add_abstraction(cur, it->second);
      }
      else
      {
        it->second =
            d_rewriter.rewrite(utils::rebuild_node(cur, d_abstraction_cache));
      }
    }
    visit.pop_back();
  } while (!visit.empty());

  // Do not abstract assertions that are lemmas
  if (d_opt_abstract_assertions && !is_lemma)
  {
    auto itr = d_abstraction_cache.find(assertion);
    assert(itr != d_abstraction_cache.end());

    auto [it, inserted] = d_abstr_consts.try_emplace(itr->second);
    if (inserted)
    {
      it->second = nm.mk_const(nm.mk_bool_type());
      Log(2) << "abstract assertion: " << itr->second
             << " (abstr: " << it->second << ", orig: " << assertion << ")";
      add_abstraction(itr->second, it->second);
      d_assertion_abstractions.push_back(it->second);
      d_abstraction_cache.emplace(it->second, it->second);
    }
    return it->second;
  }

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
  assert(d_abstr_lemmas.find(k) == d_abstr_lemmas.end()
         || KindInfo::num_children(k) > 1);
  return d_abstr_lemmas.find(k) != d_abstr_lemmas.end()
         && d_opt_minimum_size > 0 && node[1].type().is_bv()
         && node[1].type().bv_size() >= d_opt_minimum_size;
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
  // assert(abstr.kind() == Kind::APPLY);
  // assert(d_abstr_lemmas.find(node.kind()) != d_abstr_lemmas.end());
  assert(d_abstractions.find(node) == d_abstractions.end());
  d_abstractions.emplace(node, abstr);
  d_abstractions_rev.emplace(abstr, node);
  ++d_stats.num_terms;
  d_stats.terms << node.kind();
}

const Node&
AbstractionModule::abstr_uf(const Node& node)
{
  assert(node.num_children() > 1);
  Type bvt            = node[1].type();
  auto& map           = d_abstr_ufs[node.kind()];
  auto [it, inserted] = map.try_emplace(bvt);
  if (inserted)
  {
    std::stringstream ss;
    ss << node.kind() << "_" << bvt.bv_size();
    NodeManager& nm = NodeManager::get();
    Type t;
    if (node.kind() == Kind::ITE)
    {
      t = nm.mk_fun_type({nm.mk_bool_type(), bvt, bvt, node.type()});
    }
    else
    {
      t = nm.mk_fun_type({bvt, bvt, node.type()});
    }
    it->second = nm.mk_const(t, ss.str());
  }
  return it->second;
}

void
AbstractionModule::check_abstraction(const Node& abstr)
{
  Log(2) << "check abstraction: " << abstr;

  auto ita = d_abstractions_rev.find(abstr);
  assert(ita != d_abstractions_rev.end());
  const Node& node = ita->second;

  Kind kind = node.kind();
  assert(d_abstr_lemmas.find(kind) != d_abstr_lemmas.end());

  if (kind == Kind::ITE)
  {
    check_abstraction_ite(abstr, node);
    return;
  }

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
    Log(2) << "skip: assignment correct";
    return;
  }

  Log(2) << "x: " << x;
  Log(2) << "s: " << s;
  Log(2) << "t: " << t;
  Log(2) << "val_x: " << val_x;
  Log(2) << "val_s: " << val_s;
  Log(2) << "val_t: " << val_t;

  bool added_lemma = false;
  if (!d_opt_value_inst_only)
  {
    auto it = d_abstr_lemmas.find(kind);
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
        lemma_no_abstract(lemma, lem->kind());
        added_lemma = true;
        if (!d_opt_eager_refine)
        {
          break;
        }
      }
      if (KindInfo::is_commutative(kind))
      {
        inst = d_rewriter.rewrite(lem->instance(val_s, val_x, val_t));
        assert(inst.is_value());
        if (!inst.value<bool>())
        {
          Log(2) << lem->kind() << " (comm.) inconsistent";
          Node lemma = lem->instance(s, x, t);
          lemma_no_abstract(lemma, lem->kind());
          added_lemma = true;
          if (!d_opt_eager_refine)
          {
            break;
          }
        }
      }
    }
  }

  // Inconsistent value, but no abstraction violated, add value-based lemma.
  if (!added_lemma)
  {
    const auto value_insts = d_value_insts[node];
    if (kind != Kind::EQUAL
        && (d_opt_value_inst_limit == 0
            || value_insts <= d_opt_value_inst_limit))
    {
      LemmaKind lk = lemma_kind_value(kind);
      Log(2) << lk << " inconsistent";
      Node lemma =
          nm.mk_node(Kind::IMPLIES,
                     {nm.mk_node(Kind::AND,
                                 {
                                     nm.mk_node(Kind::EQUAL, {x, val_x}),
                                     nm.mk_node(Kind::EQUAL, {s, val_s}),
                                 }),
                      nm.mk_node(Kind::EQUAL, {t, val_expected})});
      d_lemma_buffer.emplace_back(node, lemma, lk);
    }
    else if (kind == Kind::EQUAL)
    {
      auto [it, inserted] = d_abstr_equal.try_emplace(node);
      // Partition equality in partitions of size 16
      if (inserted)
      {
        uint64_t part_size = 16;
        uint64_t bv_size   = x.type().bv_size();
        auto& partitions   = it->second;
        for (uint64_t lo = 0, hi = part_size - 1; lo < bv_size;
             lo += part_size, hi = std::min(bv_size - 1, hi + part_size))
        {
          partitions.push_back(nm.mk_const(nm.mk_bool_type()));
          Node extr_c0 = nm.mk_node(Kind::BV_EXTRACT, {x}, {hi, lo});
          Node extr_c1 = nm.mk_node(Kind::BV_EXTRACT, {s}, {hi, lo});
          Node eq      = nm.mk_node(Kind::EQUAL, {extr_c0, extr_c1});
          add_abstraction(eq, partitions.back());
        }
        Node lemma =
            nm.mk_node(Kind::EQUAL, {t, utils::mk_nary(Kind::AND, partitions)});
        lemma_no_abstract(lemma, LemmaKind::BITBLAST_FULL);
      }

      // At this point we add the next violated partition.
      auto& partitions = it->second;
      if (!partitions.empty())
      {
        bool val_eq = val_t.value<bool>();
        for (auto itp = partitions.begin(); itp != partitions.end(); ++itp)
        {
          const Node& c = *itp;
          auto ita      = d_abstractions_rev.find(c);
          assert(ita != d_abstractions_rev.end());
          const Node& ref = ita->second;
          if (val_eq != d_solver_state.value(ref).value<bool>())
          {
            Node lemma = nm.mk_node(Kind::EQUAL, {c, ref});
            lemma_no_abstract(lemma, LemmaKind::BITBLAST_FULL);
            it->second.erase(itp);
            break;
          }
        }
      }
    }
    // Incrementally bit-blast abstracted term starting from LSB
    else if (kind == Kind::BV_MUL || kind == Kind::BV_ADD)
    {
      const auto& bv_t = val_t.value<BitVector>();
      const auto& bv_e = val_expected.value<BitVector>();
      auto bv_xor      = bv_t.bvxor(bv_e);
      uint64_t upper   = bv_xor.count_trailing_zeros() + 32;
      uint64_t size    = bv_t.size();
      assert(upper < size);
      upper = std::min(upper, size) - 1;

      Node extr_x = nm.mk_node(Kind::BV_EXTRACT, {x}, {upper, 0});
      Node extr_s = nm.mk_node(Kind::BV_EXTRACT, {s}, {upper, 0});
      Node extr_t = nm.mk_node(Kind::BV_EXTRACT, {t}, {upper, 0});
      Node term   = nm.mk_node(kind, {extr_x, extr_s});
      Node lemma  = nm.mk_node(Kind::EQUAL, {extr_t, term});
      d_lemma_buffer.emplace_back(node,
                                  lemma,
                                  upper + 1 == size ? LemmaKind::BITBLAST_FULL
                                                    : LemmaKind::BITBLAST_INC);
    }
    else
    {
      // Fully bit-blast abstracted term
      Node term  = nm.mk_node(kind, {x, s});
      Node lemma = nm.mk_node(Kind::EQUAL, {t, term});
      d_lemma_buffer.emplace_back(node, lemma, LemmaKind::BITBLAST_FULL);
    }
  }
}

void
AbstractionModule::check_abstraction_ite(const Node& abstr, const Node& node)
{
  const Node& c  = abstr[1];
  const Node& bt = abstr[2];
  const Node& bf = abstr[3];
  const Node& t  = abstr;
  Node val_c     = d_solver_state.value(c);
  Node val_t     = d_solver_state.value(t);

  bool cond = val_c.value<bool>();
  if (cond)
  {
    Node val_bt = d_solver_state.value(bt);
    if (val_t == val_bt)
    {
      Log(2) << "skip: assignment correct";
      return;
    }
  }
  else
  {
    Node val_bf = d_solver_state.value(bf);
    if (val_t == val_bf)
    {
      Log(2) << "skip: assignment correct";
      return;
    }
  }

  NodeManager& nm     = NodeManager::get();
  auto [it, inserted] = d_abstr_equal.try_emplace(node);
  // Expand branch depending on value of condition.
  if (inserted)
  {
    auto& consts = it->second;
    consts.push_back(nm.mk_const(node.type()));

    Node expand;
    const Node& _c = consts.back();
    if (cond)
    {
      expand = nm.mk_node(Kind::ITE, {c, bt, _c});
    }
    else
    {
      expand = nm.mk_node(Kind::ITE, {c, _c, bf});
    }
    lemma_no_abstract(nm.mk_node(Kind::EQUAL, {t, expand}),
                      LemmaKind::ITE_EXPAND);
  }
  else
  {
    // Expand remaining branch since value of condition changed.
    assert(!it->second.empty());
    const Node& _c = it->second.back();
    const Node& b  = cond ? bt : bf;
    Node lemma     = nm.mk_node(Kind::EQUAL, {_c, b});
    lemma_no_abstract(lemma, LemmaKind::ITE_REFINE);
    it->second.clear();
  }
}

bool
AbstractionModule::check_assertion_abstractions()
{
  uint64_t nadded = 0;
  NodeManager& nm = NodeManager::get();
  for (size_t i = 0, size = d_assertion_abstractions.size(); i < size; ++i)
  {
    const Node& abstr = d_assertion_abstractions[i];
    auto it           = d_assertion_abstractions_cache.find(abstr);
    if (it != d_assertion_abstractions_cache.end())
    {
      continue;
    }
    auto itr = d_abstractions_rev.find(abstr);
    assert(itr != d_abstractions_rev.end());
    const Node& assertion = itr->second;
    Node val              = d_solver_state.value(assertion);
    if (!val.value<bool>())
    {
      Log(2) << "violated assertion: " << abstr;
      Log(2) << "abstr assertion:    " << assertion;
      Node lemma = nm.mk_node(Kind::EQUAL, {assertion, abstr});
      lemma_no_abstract(lemma, LemmaKind::ASSERTION);
      d_assertion_abstractions_cache.insert(abstr);
      ++nadded;
      if (nadded >= d_opt_assertion_refinements)
      {
        break;
      }
    }
  }
  return nadded > 0;
}

void
AbstractionModule::lemma_no_abstract(const Node& lemma, LemmaKind lk)
{
  // Make sure that lemma is rewritten before adding to the cache.
  Node lem = d_rewriter.rewrite(lemma);
  // Cache lemma so that we won't consider it for abstraction.
  d_abstraction_cache.emplace(lem, lem);
  d_stats.lemmas << lk;
  d_solver_state.lemma(lem);
  d_added_lemma = true;
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

#ifndef NDEBUG
void
AbstractionModule::verify_lemmas() const
{
  option::Options opts;
  SolvingContext ctx(opts);
  NodeManager& nm = NodeManager::get();

  for (uint64_t size = 4; size < 32; ++size)
  {
    std::cout << std::endl;
    std::cout << "check size=" << size << std::endl;
    Node x = nm.mk_const(nm.mk_bv_type(size), "x");
    Node s = nm.mk_const(nm.mk_bv_type(size), "s");
    Node t = nm.mk_const(nm.mk_bv_type(size), "t");
    for (const auto& [k, lemmas] : d_abstr_lemmas)
    {
      Node term = nm.mk_node(k, {x, s});
      ctx.push();
      std::cout << "check: " << k << std::endl;
      Node eq = nm.mk_node(Kind::EQUAL, {term, t});
      ctx.assert_formula(eq);
      size_t i = 0;
      for (const auto& lemma : lemmas)
      {
        std::cout << "\r" << ++i << "/" << lemmas.size() << std::flush;
        ctx.push();
        Node inst = nm.mk_node(Kind::NOT, {lemma->instance(x, s, t)});
        ctx.assert_formula(inst);
        Result res = ctx.solve();
        if (res != Result::UNSAT)
        {
          std::cout << std::endl;
          std::cout << lemma->kind() << " failed" << std::endl;
          std::cout << "(assert " << eq << ")" << std::endl;
          std::cout << "(assert " << inst << ")" << std::endl;
          std::cout << "x: " << ctx.get_value(x) << std::endl;
          std::cout << "s: " << ctx.get_value(s) << std::endl;
          std::cout << "t: " << ctx.get_value(t) << std::endl;
        }
        ctx.pop();
      }
      std::cout << std::endl;
      ctx.pop();
    }
  }
}
#endif

AbstractionModule::Statistics::Statistics(util::Statistics& stats,
                                          const std::string& prefix)
    : num_terms(stats.new_stat<uint64_t>(prefix + "terms::total")),
      num_lemmas(stats.new_stat<uint64_t>(prefix + "lemmas::total")),
      num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      terms(stats.new_stat<util::HistogramStatistic>(prefix + "terms")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}

}  // namespace bzla::abstract
