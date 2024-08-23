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

namespace bzla::abstract {

using namespace node;

/* --- AbstractionModule public --------------------------------------------- */

AbstractionModule::AbstractionModule(Env& env, SolverState& state)
    : d_env(env),
      d_logger(env.logger()),
      d_solver_state(state),
      d_rewriter(env.rewriter()),
      d_active_abstractions(state.backtrack_mgr()),
      d_assertion_abstractions(state.backtrack_mgr()),
      d_assertion_abstractions_cache(state.backtrack_mgr()),
      // Some lemmas are not valid for bit-vectors of size 1 or 2. Hence, we
      // only start abstracting from size 3+ instead of guarding each lemma
      // separately.
      d_opt_minimum_size(std::max(env.options().abstraction_bv_size(),
                                  static_cast<uint64_t>(3))),
      d_opt_eager_refine(env.options().abstraction_eager_refine()),
      d_opt_value_inst_limit(env.options().abstraction_value_limit()),
      d_opt_value_inst_only(env.options().abstraction_value_only()),
      d_opt_abstract_assertions(env.options().abstraction_assert()),
      d_opt_assertion_refinements(env.options().abstraction_assert_refs()),
      d_opt_inc_bitblast(env.options().abstraction_inc_bitblast()),
      d_stats(env.statistics(), "solver::abstract::")
{
  bool opt_initial_lemmas = env.options().abstraction_initial_lemmas();

  NodeManager& nm = d_env.nm();
  if (env.options().abstraction_bv_mul())
  {
    auto& mul_abstr_lemmas = d_abstr_lemmas[Kind::BV_MUL];
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_POW2>(nm));
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_NEG_POW2>(nm));
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_IC>(nm));
    mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_ODD>(nm));
    if (!opt_initial_lemmas)
    {
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF1>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF3>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN3>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN4>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN5>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN6>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF14>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF15>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN9>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF18>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN11>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN12>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REFN13>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF13>(nm));
      mul_abstr_lemmas.emplace_back(new Lemma<LemmaKind::MUL_REF12>(nm));
    }
  }

  if (env.options().abstraction_bv_udiv())
  {
    auto& udiv_abstr_lemmas = d_abstr_lemmas[Kind::BV_UDIV];
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_POW2>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF1>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF2>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF3>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF4>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF5>(nm));
    udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF6>(nm));
    if (!opt_initial_lemmas)
    {
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF7>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF8>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF9>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF10>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF11>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF12>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF13>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF14>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF15>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF16>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF17>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF18>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF19>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF20>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF21>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF23>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF24>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF25>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF26>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF27>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF28>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF29>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF30>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF31>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF32>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF33>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF34>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF36>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF37>(nm));
      udiv_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UDIV_REF38>(nm));
    }
  }

  if (env.options().abstraction_bv_urem())
  {
    auto& urem_abstr_lemmas = d_abstr_lemmas[Kind::BV_UREM];
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_POW2>(nm));
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF1>(nm));
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF2>(nm));
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF3>(nm));
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF4>(nm));
    urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF5>(nm));
    // urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF6>(nm));
    if (!opt_initial_lemmas)
    {
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF7>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF8>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF9>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF10>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF11>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF12>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF13>(nm));
      urem_abstr_lemmas.emplace_back(new Lemma<LemmaKind::UREM_REF14>(nm));
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
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_ZERO>(nm));
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_SAME>(nm));
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_INV>(nm));
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_OVFL>(nm));
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_NOOVFL>(nm));
    add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_OR>(nm));
    if (!opt_initial_lemmas)
    {
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF1>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF2>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF3>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF4>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF5>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF6>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF7>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF8>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF9>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF10>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF11>(nm));
      add_abstr_lemmas.emplace_back(new Lemma<LemmaKind::ADD_REF12>(nm));
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
      check_term_abstraction(abstr_term);
    }
  }

  // Check abstracted assertions
  if (!d_added_lemma && d_opt_abstract_assertions)
  {
    check_assertion_abstractions();
  }

  // Abstraction refinements that are added as "last resort" are only added if
  // we expanded all violated assertions.
  // This includes:
  //   - value instantiation lemmas
  //   - bit-blasting lemmas
  if (!d_added_lemma)
  {
    for (const auto& [node, lemma, lk] : d_lemma_buffer)
    {
      if (lemma_no_abstract(lemma, lk))
      {
        // Increment counter for value instantiations
        if (is_lemma_kind_value(lk))
        {
          ++d_value_insts[node];
        }
      }
    }
  }
  d_lemma_buffer.clear();
}

const Node&
AbstractionModule::process(const Node& assertion, bool is_lemma)
{
  NodeManager& nm = d_env.nm();

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
        it->second = d_rewriter.rewrite(
            utils::rebuild_node(nm, cur, d_abstraction_cache));
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

  const auto& processed = d_abstraction_cache.at(assertion);
  // Map original assertion to processed assertion for unsat cores.
  if (processed != assertion)
  {
    d_abstraction_cache_assertions.emplace(processed, assertion);
  }
  return processed;
}

bool
AbstractionModule::is_processed_assertion(const Node& assertion)
{
  auto it = d_abstraction_cache_assertions.find(assertion);
  return it != d_abstraction_cache_assertions.end() && it->second != assertion;
}

const Node&
AbstractionModule::get_original_assertion(const Node& processed_assertion)
{
  auto it = d_abstraction_cache_assertions.find(processed_assertion);
  assert(it != d_abstraction_cache_assertions.end());
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
    NodeManager& nm = d_env.nm();
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

bool
AbstractionModule::check_lemma(const AbstractionLemma* lem,
                               const Node& val_x,
                               const Node& val_s,
                               const Node& val_t,
                               const Node& x,
                               const Node& s,
                               const Node& t)
{
  Node inst = lem->instance(val_x, val_s, val_t);
  Node lemma;
  if (!inst.is_null())
  {
    inst = d_rewriter.rewrite(inst);
    assert(inst.is_value());
    if (!inst.value<bool>())
    {
      lemma = lem->instance(x, s, t);
    }
  }
  else
  {
    inst = lem->instance(val_x, val_s, val_t, val_x, val_s, val_t);
    if (!inst.is_null())
    {
      inst = d_rewriter.rewrite(inst);
      assert(inst.is_value());
      if (!inst.value<bool>())
      {
        lemma = lem->instance(val_x, val_s, val_t, x, s, t);
      }
    }
  }

  if (!lemma.is_null())
  {
    Log(2) << lem->kind() << " inconsistent";
    return lemma_no_abstract(lemma, lem->kind());
  }

  return false;
}

void
AbstractionModule::check_term_abstraction(const Node& abstr)
{
  Log(2) << "check abstraction: " << abstr;

  auto ita = d_abstractions_rev.find(abstr);
  assert(ita != d_abstractions_rev.end());
  const Node& node = ita->second;

  Kind kind = node.kind();
  assert(d_abstr_lemmas.find(kind) != d_abstr_lemmas.end());

  if (kind == Kind::ITE)
  {
    check_term_abstraction_ite(abstr, node);
    return;
  }

  NodeManager& nm   = d_env.nm();
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
      added_lemma = check_lemma(lem.get(), val_x, val_s, val_t, x, s, t);
      if (!added_lemma && KindInfo::is_commutative(kind))
      {
        added_lemma = check_lemma(lem.get(), val_s, val_x, val_t, s, x, t);
      }
      if (added_lemma && !d_opt_eager_refine)
      {
        break;
      }
    }
  }

  // Inconsistent value, but no lemma violated, add value-based lemma.
  if (!added_lemma)
  {
    uint64_t limit = d_opt_value_inst_limit > 0
                         ? val_x.type().bv_size() / d_opt_value_inst_limit
                         : 0;
    if (kind != Kind::EQUAL && d_value_insts[node] < limit)
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
      if (kind == Kind::BV_MUL && val_x == val_s)
      {
        ++d_value_insts_square[node];
      }
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
        Node lemma = nm.mk_node(Kind::EQUAL,
                                {t, utils::mk_nary(nm, Kind::AND, partitions)});
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
    else if (d_opt_inc_bitblast
             && (kind == Kind::BV_MUL || kind == Kind::BV_ADD))
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
    // Use special square encoding for BV_MUL if value instantiations were all
    // square instantiations.
    else if (kind == Kind::BV_MUL && d_value_insts_square[node] > 0
             && d_value_insts_square[node] >= d_value_insts[node]
             && val_x == val_s)
    {
      d_lemma_buffer.emplace_back(
          node,
          nm.mk_node(
              Kind::IMPLIES,
              {nm.mk_node(Kind::EQUAL, {x, s}),
               nm.mk_node(Kind::EQUAL, {t, nm.mk_node(Kind::BV_MUL, {x, x})})}),
          LemmaKind::BITBLAST_BV_MUL_SQUARE);
      d_value_insts_square[node] = 0;  // Reset, next time we fully bit-blast
    }
    else
    {
      // Fully bit-blast abstracted term
      Node term  = nm.mk_node(kind, {x, s});
      Node lemma = nm.mk_node(Kind::EQUAL, {t, term});
      LemmaKind lk;
      switch (kind)
      {
        case Kind::BV_MUL: lk = LemmaKind::BITBLAST_BV_MUL; break;
        case Kind::BV_UDIV: lk = LemmaKind::BITBLAST_BV_UDIV; break;
        case Kind::BV_UREM: lk = LemmaKind::BITBLAST_BV_UREM; break;
        default: lk = LemmaKind::BITBLAST_FULL;
      }
      d_lemma_buffer.emplace_back(node, lemma, lk);
    }
  }
}

void
AbstractionModule::check_term_abstraction_ite(const Node& abstr,
                                              const Node& node)
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

  NodeManager& nm     = d_env.nm();
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
  NodeManager& nm = d_env.nm();
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

bool
AbstractionModule::lemma_no_abstract(const Node& lemma, LemmaKind lk)
{
  // Make sure that lemma is rewritten before adding to the cache.
  Node lem = d_rewriter.rewrite(lemma);
  // Cache lemma so that we won't consider it for abstraction.
  assert(d_abstraction_cache.find(lem) == d_abstraction_cache.end());
  d_abstraction_cache.emplace(lem, lem);
  if (d_solver_state.lemma(lem))
  {
    d_added_lemma = true;
    d_stats.lemmas << lk;
    return true;
  }
  return false;
}

bool
AbstractionModule::lemma_abstract(const Node& lemma, LemmaKind lk)
{
  if (d_solver_state.lemma(lemma))
  {
    d_added_lemma = true;
    d_stats.lemmas << lk;
    return true;
  }
  return false;
}

void
AbstractionModule::score_lemmas(
    Kind kind,
    uint64_t bv_size,
    std::unordered_map<LemmaKind, uint64_t>& rank_map) const
{
  NodeManager& nm = d_env.nm();
  uint64_t max    = 1;
  for (size_t i = 0; i < bv_size; ++i)
  {
    max *= 2;
  }
  std::vector<Node> values;
  std::vector<std::vector<std::vector<bool>>> results_lemmas(
      max, std::vector<std::vector<bool>>(max, std::vector<bool>(max, true)));
  std::vector<std::vector<std::vector<bool>>> results_optimal(
      max, std::vector<std::vector<bool>>(max, std::vector<bool>(max, false)));

  // Create all possible values [0, max[
  for (uint64_t i = 0; i < max; ++i)
  {
    values.push_back(nm.mk_value(BitVector::from_ui(bv_size, i)));
  }

  // Compute all results for kind
  uint64_t optimal_score = 0;
  for (uint64_t i = 0; i < values.size(); ++i)
  {
    for (uint64_t j = 0; j < values.size(); ++j)
    {
      for (uint64_t k = 0; k < values.size(); ++k)
      {
        Node val = d_rewriter.rewrite(
            nm.mk_node(Kind::EQUAL,
                       {values[k], nm.mk_node(kind, {values[i], values[j]})}));
        assert(val.is_value());
        results_optimal[i][j][k] = val.value<bool>();
        if (results_optimal[i][j][k])
        {
          ++optimal_score;
        }
      }
    }
  }

  std::cout << std::fixed;
  uint64_t max_score   = max * max * max;
  uint64_t final_score = max_score;
  std::cout << "lemma score (worst: " << final_score << ", best: " << max * max
            << ")" << std::endl;

  for (const auto& lem : d_abstr_lemmas.at(kind))
  {
    uint64_t score            = 0;
    uint64_t prev_final_score = final_score;
    // Compute result for each triplet (x, s, t)
    for (uint64_t i = 0; i < values.size(); ++i)
    {
      for (uint64_t j = 0; j < values.size(); ++j)
      {
        // const Node& expected = results[i][j];
        for (uint64_t k = 0; k < values.size(); ++k)
        {
          Node inst = lem->instance(values[i], values[j], values[k]);
          if (inst.is_null())
          {
            inst = lem->instance(values[i],
                                 values[j],
                                 values[k],
                                 values[i],
                                 values[j],
                                 values[k]);
          }
          bool res = true;
          if (!inst.is_null())
          {
            inst = d_rewriter.rewrite(inst);
            assert(inst.is_value());
            res = inst.value<bool>();
          }

          // check commutative case
          if (kind == Kind::BV_MUL)
          {
            Node instc = lem->instance(values[j], values[i], values[k]);
            if (instc.is_null())
            {
              instc = lem->instance(values[j],
                                    values[i],
                                    values[k],
                                    values[j],
                                    values[i],
                                    values[k]);
            }
            if (!instc.is_null())
            {
              instc = d_rewriter.rewrite(instc);
              res   = res & instc.value<bool>();
            }
          }

          auto overall_res = results_lemmas[i][j][k];
          // Count cases when lemma is true (including false positives)
          if (res)
          {
            ++score;
          }
          // Count number of ruled out triplets
          else if (overall_res)
          {
            --final_score;
          }
          results_lemmas[i][j][k] = overall_res & res;
        }
      }
    }
    rank_map[lem->kind()] = score;
    int64_t diff          = final_score - prev_final_score;
    std::cout << lem->kind() << ": " << score << "/" << max_score
              << " (final: " << final_score << ", diff: " << diff << ", "
              << static_cast<double>(diff) / max_score * 100 << "%)"
              << std::endl;
  }
  std::cout << "final score:   " << final_score << " "
            << static_cast<double>(final_score) / max_score * 100
            << "% (wrong results: " << final_score - (max * max) << ")"
            << std::endl;
  std::cout << "optimal score: " << optimal_score << " "
            << static_cast<double>(optimal_score) / max_score * 100 << "%"
            << std::endl;
}

void
AbstractionModule::rank_lemmas_by_circuit_size()
{
  Env env(d_env.nm());
  bv::AigBitblaster bb;
  NodeManager& nm = d_env.nm();
  Type bv32       = nm.mk_bv_type(32);
  std::unordered_map<Kind, std::vector<std::pair<LemmaKind, uint64_t>>>
      lemma_sizes;

  std::unordered_map<Kind, uint64_t> circuit_size;
  for (const auto& [kind, lemmas] : d_abstr_lemmas)
  {
    if (KindInfo::num_children(kind) == 2)
    {
      Node x                       = nm.mk_const(bv32);
      Node s                       = nm.mk_const(bv32);
      Node t                       = nm.mk_const(bv32);
      uint64_t size_overall_before = bb.num_aig_ands();
      for (const auto& lem : lemmas)
      {
        Node inst = lem->instance(x, s, t);
        if (inst.is_null())
        {
          // Conditional on x == s, hence manual computation needed
          if (lem->kind() == LemmaKind::BITBLAST_BV_MUL_SQUARE)
          {
            inst =
                nm.mk_node(Kind::IMPLIES,
                           {nm.mk_node(Kind::EQUAL, {x, s}),
                            nm.mk_node(Kind::EQUAL,
                                       {t, nm.mk_node(Kind::BV_MUL, {x, x})})});
          }
          else if (lem->kind() == LemmaKind::MUL_POW2)
          {
            Node val_pow2 =
                nm.mk_value(BitVector::mk_one(bv32.bv_size()).ibvshl(2));
            inst = lem->instance(val_pow2, s, t, x, s, t);
          }
          else if (lem->kind() == LemmaKind::MUL_NEG_POW2)
          {
            Node val_pow2 = nm.mk_value(
                BitVector::mk_one(bv32.bv_size()).ibvshl(2).ibvneg());
            inst = lem->instance(val_pow2, s, t, x, s, t);
          }
          else
          {
            inst = lem->instance(x, s, t, x, s, t);
          }
        }
        if (!inst.is_null())
        {
          inst                 = env.rewriter().rewrite(inst);
          uint64_t size_before = bb.num_aig_ands();
          bb.bitblast(inst);
          uint64_t circuit_size = bb.num_aig_ands() - size_before;
          lemma_sizes[kind].emplace_back(lem->kind(), circuit_size);
        }
      }
      std::cout << kind << " total lemma size: "
                << bb.num_aig_ands() - size_overall_before << std::endl;
      {
        Node x               = nm.mk_const(bv32);
        Node s               = nm.mk_const(bv32);
        Node t               = nm.mk_node(kind, {x, s});
        uint64_t size_before = bb.num_aig_ands();
        bb.bitblast(t);
        std::cout << kind
                  << " circuit size: " << bb.num_aig_ands() - size_before
                  << std::endl;
        circuit_size[kind] = bb.num_aig_ands() - size_before;
      }
    }
  }

  std::unordered_map<LemmaKind, uint64_t> rank_map;
  for (auto& [k, lemmas] : lemma_sizes)
  {
    std::sort(lemmas.begin(), lemmas.end(), [](const auto& p1, const auto& p2) {
      return p1.second < p2.second;
    });
    uint64_t sum = 0;
    bool reached = false;
    for (const auto& [lk, size] : lemmas)
    {
      rank_map.emplace(lk, size);
      sum += size;
      std::cout << size << " " << lk << " (sum: " << sum << "/"
                << circuit_size[k] << ")" << std::endl;
      if (!reached && sum >= circuit_size[k])
      {
        std::cout << "--- circuit size reached (" << circuit_size[k] << ") ---"
                  << std::endl;
        reached = true;
      }
    }
    std::sort(d_abstr_lemmas.at(k).begin(),
              d_abstr_lemmas.at(k).end(),
              [&rank_map](const auto& l1, const auto& l2) {
                return rank_map[l1->kind()] < rank_map[l2->kind()];
              });
    std::cout << "score: " << k << std::endl;
    std::unordered_map<LemmaKind, uint64_t> rm;
    score_lemmas(k, 6, rm);
  }

  std::cout << "final ranking:" << std::endl;
  std::cout << "std::unordered_map<LemmaKind, uint64_t> rank_map = {";
  for (const auto& [lk, size] : rank_map)
  {
    std::cout << "{LemmaKind::" << lk << "," << size << "}," << std::endl;
  }
  std::cout << "};" << std::endl;
  abort();
}

void
AbstractionModule::rank_lemmas_by_score()
{
  std::unordered_map<LemmaKind, uint64_t> rank_map;
  score_lemmas(Kind::BV_MUL, 6, rank_map);
  score_lemmas(Kind::BV_UDIV, 6, rank_map);
  score_lemmas(Kind::BV_UREM, 6, rank_map);

  std::cout << "std::unordered_map<LemmaKind, uint64_t> rank_map = {";
  for (const auto& [lk, score] : rank_map)
  {
    std::cout << "{LemmaKind::" << lk << "," << score << "}," << std::endl;
  }
  std::cout << "};" << std::endl;
  abort();
}

void
AbstractionModule::print_initial_lemmas() const
{
  Node x, s, t;

  NodeManager& nm                = d_env.nm();
  Type bv4                       = nm.mk_bv_type(4);
  x                              = nm.mk_const(bv4, "x");
  s                              = nm.mk_const(bv4, "s");
  t                              = nm.mk_const(bv4, "t");
  std::vector<BitVector> pow2    = {BitVector::from_ui(4, 1),
                                    BitVector::from_ui(4, 2),
                                    BitVector::from_ui(4, 4),
                                    BitVector::from_ui(4, 8)};
  std::vector<BitVector> negpow2 = {BitVector::from_ui(4, 1).bvneg(),
                                    BitVector::from_ui(4, 2).bvneg(),
                                    BitVector::from_ui(4, 4).bvneg()};
  for (const auto& lemma : d_abstr_lemmas.at(Kind::BV_MUL))
  {
    const auto lk = lemma->kind();
    if (lk == LemmaKind::MUL_REF1)
    {
      break;
    }

    if (lk == LemmaKind::MUL_POW2)
    {
      uint64_t i = 1;
      for (const auto& p2 : pow2)
      {
        Node npow2 = nm.mk_value(p2);
        std::cout
            << "(define-fun lemma_" << lemma->kind() << "_" << i
            << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
        std::cout << lemma->instance(npow2, s, t, x, s, t);
        std::cout << ")" << std::endl;
        std::cout
            << "(define-fun lemma_" << lemma->kind() << "_c" << i++
            << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
        std::cout << lemma->instance(npow2, x, t, s, x, t);
        std::cout << ")" << std::endl;
      }
    }
    else if (lk == LemmaKind::MUL_NEG_POW2)
    {
      uint64_t i = 1;
      for (const auto& p2 : negpow2)
      {
        Node npow2 = nm.mk_value(p2);
        std::cout
            << "(define-fun lemma_" << lemma->kind() << "_" << i
            << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
        std::cout << lemma->instance(npow2, s, t, x, s, t);
        std::cout << ")" << std::endl;
        std::cout
            << "(define-fun lemma_" << lemma->kind() << "_c" << i++
            << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
        std::cout << lemma->instance(npow2, x, t, s, x, t);
        std::cout << ")" << std::endl;
      }
    }
    else
    {
      std::cout
          << "(define-fun lemma_" << lemma->kind()
          << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
      std::cout << lemma->instance(x, s, t);
      std::cout << ")" << std::endl;
      std::cout
          << "(define-fun lemma_" << lemma->kind() << "_c"
          << " ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool ";
      std::cout << lemma->instance(s, x, t);
      std::cout << ")" << std::endl;
    }
  }
}

#ifndef NDEBUG
void
AbstractionModule::verify_lemmas() const
{
  option::Options opts;
  NodeManager& nm = d_env.nm();
  SolvingContext ctx(nm, opts);

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
      num_checks(stats.new_stat<uint64_t>(prefix + "num_checks")),
      terms(stats.new_stat<util::HistogramStatistic>(prefix + "terms")),
      lemmas(stats.new_stat<util::HistogramStatistic>(prefix + "lemmas")),
      time_check(stats.new_stat<util::TimerStatistic>(prefix + "time_check"))
{
}

}  // namespace bzla::abstract
