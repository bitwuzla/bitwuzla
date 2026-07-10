/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/solver_engine.h"

#include <iomanip>
#include <unordered_set>

#include "env.h"
#include "node/node.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "printer/smt2_printer.h"
#include "rewrite/evaluator.h"
#include "solver/abstract/abstraction_module.h"
#include "solving_context.h"
#include "util/resources.h"

namespace bzla {

using namespace node;

/* --- SolverEngine public -------------------------------------------------- */

SolverEngine::SolverEngine(SolvingContext& context)
    : d_context(context),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_assertions(context.assertions()),
      d_register_assertion_cache(&d_backtrack_mgr),
      d_register_term_cache(&d_backtrack_mgr),
      d_distinct_n(&d_backtrack_mgr),
      d_lemma_cache(&d_backtrack_mgr),
      d_sat_state(Result::UNKNOWN),
      d_in_solving_mode(false),
      d_stats(context.env().statistics(), "solver::engine::"),
      d_env(context.env()),
      d_logger(d_env.logger()),
      d_solver_state(*this),
      d_bv_solver(context.env(), d_solver_state),
      d_fp_solver(context.env(), d_solver_state),
      d_fun_solver(context.env(), d_solver_state),
      d_array_solver(context.env(), d_solver_state),
      d_quant_solver(context.env(), d_solver_state),
      d_am(context.env().options().abstraction()
               ? new abstract::AbstractionModule(context.env(), d_solver_state)
               : nullptr)
{
}

SolverEngine::~SolverEngine() {}

Result
SolverEngine::solve()
{
  util::Timer timer(d_stats.time_solve);

  if (d_logger.is_msg_enabled(1))
  {
    d_num_printed_stats = 0;
    print_statistics();
  }

  // Process unprocessed assertions.
  process_assertions();

  d_in_solving_mode = true;
  do
  {
    // Reset model cache
    d_value_cache.clear();

    // Process lemmas generated in previous iteration.
    process_lemmas();

    // Reset term registration flag. Reset flag after new terms were registered
    // in process_lemma().
    d_new_terms_registered = false;

    if (d_logger.is_msg_enabled(1))
    {
      print_statistics();
    }

    d_sat_state = d_bv_solver.solve();
    if (d_sat_state != Result::SAT)
    {
      break;
    }

    d_fp_solver.check();
    if (!d_lemmas.empty())
    {
      d_stats.num_lemmas_fp += d_lemmas.size();
      continue;
    }

    check_distinct_n();
    if (!d_lemmas.empty())
    {
      d_stats.num_lemmas_distinctn += d_lemmas.size();
      continue;
    }

    if (d_am != nullptr)
    {
      d_am->check();
      if (!d_lemmas.empty())
      {
        d_stats.num_lemmas_abstr += d_lemmas.size();
        continue;
      }
    }
    d_array_solver.check();
    if (!d_lemmas.empty())
    {
      d_stats.num_lemmas_array += d_lemmas.size();
      continue;
    }
    d_fun_solver.check();
    if (!d_lemmas.empty())
    {
      d_stats.num_lemmas_fun += d_lemmas.size();
      continue;
    }

    bool quant_done = d_quant_solver.check();
    if (!quant_done)
    {
      d_sat_state = Result::UNKNOWN;
    }
    d_stats.num_lemmas_quant += d_lemmas.size();

    // If new terms were registered during the check phase, we have to make sure
    // that all theory solvers are able to check newly registered terms.
  } while (!d_lemmas.empty() || d_new_terms_registered);
  d_in_solving_mode = false;

  if (d_logger.is_msg_enabled(1))
  {
    print_statistics();
  }

  Log(1);
  Log(1) << "Solver engine determined: " << d_sat_state;
  return d_sat_state;
}

Node
SolverEngine::value(const Node& term)
{
  assert(d_in_solving_mode || d_sat_state == Result::SAT);

  if (term.is_value())
  {
    return term;
  }

  Log(3) << "get value for (in_solving: " << d_in_solving_mode << "): " << term;

  if (d_in_solving_mode)
  {
    // Make sure that term is processed by abstraction module
    const Node& _term = d_am ? d_am->process(term) : term;
    process_term(_term);
    return _value(_term);
  }

  return _value(term);
}

void
SolverEngine::unsat_core(std::vector<Node>& core) const
{
  assert(d_sat_state == Result::UNSAT);
  d_bv_solver.unsat_core(core);
  // Post-process core to replace abstracted assertions with original ones.
  if (d_am != nullptr)
  {
    for (size_t i = 0, size = core.size(); i < size; ++i)
    {
      if (d_am->is_assertion_with_abstractions(core[i]))
      {
        core[i] = d_am->get_original_assertion(core[i]);
      }
    }
  }
}

Node
SolverEngine::interpolant(const std::unordered_set<Node>& ppA,
                          const std::unordered_set<Node>& ppB)
{
  if (d_am)
  {
    // The interpolation engine needs the actual set of assertions that
    // is being processed (for labeling). Thus, in case that our abstraction
    // module is enabled, assertions in ppA/ppB with abstracted terms must be
    // replaced with the corresponding abstracted assertions.
    std::vector<Node> _ppA, _ppB;
    for (const auto& a : ppA)
    {
      _ppA.push_back(d_am->get_processed(a));
    }
    for (auto& a : ppB)
    {
      _ppB.push_back(d_am->get_processed(a));
    }
    return d_am->remove_abstractions(d_bv_solver.interpolant(_ppA, _ppB));
  }
  std::vector<Node> _ppA(ppA.begin(), ppA.end()), _ppB(ppB.begin(), ppB.end());
  return d_bv_solver.interpolant(_ppA, _ppB);
}

bool
SolverEngine::lemma(const Node& lemma)
{
  assert(lemma.type().is_bool());
  Log(2) << "lemma: " << lemma;
  Node rewritten = d_env.rewriter().rewrite(lemma);
  // Lemmas should never simplify to true
  assert(!rewritten.is_value() || !rewritten.value<bool>());
  auto [it, inserted] = d_lemma_cache.insert(rewritten);
  // Solvers should not send lemma duplicates.
  assert(inserted);
  // There can be duplicates if we add more than one lemma per round.
  if (inserted)
  {
    ++d_stats.num_lemmas;
    d_lemmas.push_back(rewritten);
    return true;
  }
  return false;
}

void
SolverEngine::hint(const Node& node, const Node& value)
{
  d_bv_solver.hint(node, value);
}

void
SolverEngine::register_eq_heuristic(const std::vector<Node>& nodes)
{
  if (!nodes.empty())
  {
    const Type& t = nodes[0].type();

    if (t.is_array())
    {
      d_array_solver.register_eq_heuristic(nodes);
    }
    else if (t.is_fp() || t.is_rm())
    {
      d_fp_solver.register_eq_heuristic(nodes);
    }
    else if (t.is_bool() || t.is_bv())
    {
      d_bv_solver.register_eq_heuristic(nodes);
    }
  }
}

void
SolverEngine::register_distinct_heuristic(const std::vector<Node>& nodes)
{
  if (!nodes.empty())
  {
    const Type& t = nodes[0].type();

    if (t.is_array())
    {
      d_array_solver.register_distinct_heuristic(nodes);
    }
    else if (t.is_fp() || t.is_rm())
    {
      d_fp_solver.register_distinct_heuristic(nodes);
    }
    else if (t.is_bool() || t.is_bv())
    {
      d_bv_solver.register_distinct_heuristic(nodes);
    }
  }
}

Result
SolverEngine::ensure_model(const std::vector<Node>& terms)
{
  Log(1) << "*** ensure model";

  std::vector<Node> unregistered;
  for (const Node& t : terms)
  {
    try
    {
      Node val = _value(t);
    }
    catch (const ComputeValueException& e)
    {
      // This can only happen if unregistered quantifiers are required to
      // compute the model value.
      unregistered.push_back(t);
    }
  }

  // Process unregistered quantifiers and call solve() to check these
  // quantifiers.
  auto res = Result::SAT;
  if (!unregistered.empty())
  {
    d_in_solving_mode = true;  // Registers new terms in value()
    for (const Node& t : unregistered)
    {
      value(t);
    }
    d_in_solving_mode = false;
    // New quantifiers were registered, check them now.
    assert(d_new_terms_registered);
    res = solve();
  }
  return res;
}

backtrack::BacktrackManager*
SolverEngine::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

/* --- SolverEngine private ------------------------------------------------- */

void
SolverEngine::check_distinct_n()
{
  NodeManager& nm = d_env.nm();
  for (size_t i = 0, size = d_distinct_n.size(); i < size; ++i)
  {
    const Node& dc = d_distinct_n[i];

    Node dc_val = d_solver_state.value(dc);

    if (dc_val.value<bool>())
    {
      util::Integer card(dc[0].value<BitVector>());

      // If rewriting is disabled, DISTINCT_N may simplify to false.
      if (card > dc.num_children() - 1)
      {
        assert(d_env.options().rewrite_level() == 0);
        d_solver_state.lemma(nm.mk_node(Kind::EQUAL, {dc, nm.mk_value(false)}));
        continue;
      }

      util::Integer thresh(dc.num_children() - 1);
      thresh -= card;
      bool ok = true;
      std::unordered_map<Node, std::vector<Node>> map;
      uint64_t conflicts = 0;
      for (size_t j = 1, nchildren = dc.num_children(); j < nchildren; ++j)
      {
        const Node& cur     = dc[j];
        Node child_val      = d_solver_state.value(cur);
        auto [it, inserted] = map.try_emplace(child_val);
        it->second.push_back(cur);
        if (!inserted)
        {
          ++conflicts;
        }

        if (thresh < conflicts)
        {
          Node lem;
          std::vector<Node> eqs;
          for (const auto& [_, terms] : map)
          {
            for (size_t k = 1, s = terms.size(); k < s; ++k)
            {
              eqs.push_back(nm.mk_node(Kind::EQUAL, {terms[k - 1], terms[k]}));
              if (conflicts == eqs.size())
              {
                lem = nm.mk_node(
                    Kind::IMPLIES,
                    {dc,
                     nm.mk_node(Kind::NOT,
                                {utils::mk_nary(nm, Kind::AND, eqs)})});
                break;
              }
            }
            if (!lem.is_null())
            {
              break;
            }
          }

          assert(!lem.is_null());
          d_solver_state.lemma(lem);
          ok = false;
          break;
        }
      }
      if (ok)
      {
        assert(card <= map.size());
      }
    }
    else
    {
      // dc evaluates to false under the current model. With CaDiCaL an eq
      // decision heuristic forces the phase of dc to match the actual number
      // of distinct children; without an external propagator (e.g., with
      // Kissat) the SAT solver may assign dc to false even though the children
      // take at least card distinct values, i.e., dc actually evaluates to
      // true. Detect this and add a lemma that forces dc.
      util::Integer card(dc[0].value<BitVector>());
      std::unordered_map<Node, std::vector<Node>> map;
      for (size_t j = 1, nchildren = dc.num_children(); j < nchildren; ++j)
      {
        map[d_solver_state.value(dc[j])].push_back(dc[j]);
      }
      // map.size() is the number of distinct values under the current model.
      // If it is at least card, dc must be true.
      if (card <= map.size())
      {
        // Collect one representative per distinct value class until we have
        // card pairwise distinct elements. Their pairwise disequalities are a
        // sufficient reason for dc to hold.
        std::vector<Node> reps;
        for (const auto& [val, terms] : map)
        {
          (void) val;
          reps.push_back(terms.front());
          if (card <= reps.size())
          {
            break;
          }
        }
        // The reps are pairwise distinct under the model; their distinctness
        // is a sufficient reason for dc to hold. card <= 1 yields a single rep,
        // in which case dc is unconditionally forced.
        Node lem =
            reps.size() < 2
                ? dc
                : nm.mk_node(Kind::IMPLIES,
                             {utils::mk_nary(nm, Kind::DISTINCT, reps), dc});
        d_solver_state.lemma(lem);
      }
    }
  }
}

void
SolverEngine::sync_scope(size_t level)
{
  while (d_backtrack_mgr.num_levels() < level)
  {
    d_backtrack_mgr.push();
  }
}

void
SolverEngine::process_assertions()
{
  Log(1) << "Processing " << d_assertions.size() << " assertions";
  while (!d_assertions.empty())
  {
    size_t level   = d_assertions.level(d_assertions.begin());
    bool top_level = level == 0;

    // Sync backtrack manager to level. This is required if there are levels
    // that do not contain any assertions.
    sync_scope(level);

    // Create vector for current level
    preprocess::AssertionVector assertions(d_assertions);
    for (size_t i = 0, size = assertions.size(); i < size; ++i)
    {
      process_assertion(assertions[i], top_level, false);
    }

    // Advance assertions to next level
    d_assertions.set_index(d_assertions.begin() + assertions.size());
  }
  assert(d_assertions.empty());

  // Sync backtrack manager to level. This is required if there are levels
  // that do not contain any assertions.
  sync_scope(d_context.backtrack_mgr()->num_levels());
}

void
SolverEngine::process_assertion(const Node& assertion,
                                bool top_level,
                                bool is_lemma)
{
  Node _assertion =
      d_am ? d_am->process_assertion(assertion, is_lemma) : assertion;

  // Send assertion to bit-vector solver.
  auto [it, inserted] = d_register_assertion_cache.insert(_assertion);
  if (inserted)
  {
    Log(2) << "register assertion (top: " << top_level << "): " << _assertion;
    d_bv_solver.register_assertion(_assertion, top_level, is_lemma);
    d_quant_solver.register_assertion(_assertion);
  }
  process_term(_assertion);
}

void
SolverEngine::process_term(const Node& term)
{
  assert(d_am == nullptr || d_am->process(term) == term);
  util::Timer timer(d_stats.time_register_term);
  // Make sure that terms are processed by the abstraction module.
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_register_term_cache.insert(cur);
    if (inserted)
    {
      if (cur.kind() == Kind::DISTINCT_N
          && (!d_env.options().adc_sat_propagator()
              || (!cur[1].type().is_bool() && !cur[1].type().is_bv())))
      {
        d_distinct_n.push_back(cur);
        register_eq_heuristic({cur, d_env.nm().mk_value(true)});
        d_new_terms_registered = true;
      }
      else if (quant::QuantSolver::is_theory_leaf(cur))
      {
        Log(2) << "register quantifier term: " << cur;
        d_quant_solver.register_term(cur);
        d_new_terms_registered = true;
      }
      else
      {
        if (d_am != nullptr && d_am->is_abstraction(cur))
        {
          Log(2) << "register abstraction term: " << cur;
          d_am->register_abstraction(cur);
          d_new_terms_registered = true;
        }
        else if (fun::FunSolver::is_theory_leaf(cur))
        {
          Log(2) << "register function term: " << cur;
          d_fun_solver.register_term(cur);
          d_new_terms_registered = true;
        }
        else if (array::ArraySolver::is_theory_leaf(cur))
        {
          Log(2) << "register array term: " << cur;
          d_array_solver.register_term(cur);
          d_new_terms_registered = true;
        }
        else if (fp::FpSolver::is_theory_leaf(cur))
        {
          Log(2) << "register floating-point term: " << cur;
          d_fp_solver.register_term(cur);
          d_new_terms_registered = true;
        }
        else if (bv::BvSolver::is_theory_leaf(cur))
        {
          d_bv_solver.register_term(cur);
          d_new_terms_registered = true;
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());
}

bool
SolverEngine::registered(const Node& term) const
{
  // All terms we encounter during solving are registered.
  if (d_in_solving_mode)
  {
    assert(d_register_term_cache.find(term) != d_register_term_cache.end());
    return true;
  }
  auto it = d_register_term_cache.find(term);
  return it != d_register_term_cache.end();
}

void
SolverEngine::process_lemmas()
{
  Log(1) << "Processing " << d_lemmas.size() << " lemmas";
  for (const Node& lemma : d_lemmas)
  {
    process_assertion(lemma, true, true);
  }
  d_lemmas.clear();
}

Node
SolverEngine::_value(const Node& term)
{
  NodeManager& nm = d_env.nm();
  node_ref_vector visit{term};

  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = d_value_cache.emplace(cur, Node());
    if (inserted)
    {
      if (registered(cur))
      {
        if (bv::BvSolver::is_leaf(cur)
            || array::ArraySolver::is_theory_leaf(cur)
            || fp::FpSolver::is_theory_leaf(cur)
            || fun::FunSolver::is_theory_leaf(cur)
            || quant::QuantSolver::is_theory_leaf(cur))
        {
          continue;
        }
      }
      else
      {
        assert(!d_in_solving_mode);
        Kind k = cur.kind();
        if (k == Kind::FORALL || k == Kind::LAMBDA || k == Kind::FP_SYMFPU_RM
            || k == Kind::FP_SYMFPU_EXP || k == Kind::FP_SYMFPU_INF
            || k == Kind::FP_SYMFPU_NAN || k == Kind::FP_SYMFPU_SIG
            || k == Kind::FP_SYMFPU_SIGN || k == Kind::FP_SYMFPU_ZERO)
        {
          continue;
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      Node value;
      Kind k = cur.kind();

      // If we encounter an unregistered node after solving, for some node
      // kinds we have to compute the values differently than during solving.
      // In these cases we ask the corresponding theory solver to generate a
      // model value instead of using the value in the bit-vector abstraction.
      // The unregistered node does not occur in the bit-vector abstraction and
      // therefore would only be assigned a default value.
      switch (k)
      {
        case Kind::VALUE: value = cur; break;

        case Kind::VARIABLE: {
          Log(3) << "variable encountered: " << cur;
          d_value_cache.clear();
          throw ComputeValueException(cur);
        }
        break;

        case Kind::APPLY:
        case Kind::SELECT:
        case Kind::FORALL:
          if (!registered(cur))
          {
            if (k == Kind::SELECT)
            {
              Log(3) << "unregistered select encountered: " << cur;
              Node sel = nm.mk_node(
                  Kind::SELECT, {cached_value(cur[0]), cached_value(cur[1])});
              value = d_array_solver.value(sel);
            }
            // Compute value of function application based on current function
            // model.
            else if (k == Kind::APPLY)
            {
              Log(3) << "unregistered apply encountered: " << cur;
              std::vector<Node> args{cur[0]};
              for (size_t i = 1; i < cur.num_children(); ++i)
              {
                args.push_back(cached_value(cur[i]));
                assert(!args.back().is_null());
              }
              Node app = nm.mk_node(Kind::APPLY, args);
              value    = d_fun_solver.value(app);
            }
            // If an unregistered quantifier is encountered, we cannot compute a
            // value without another solve().
            else if (k == Kind::FORALL)
            {
              Log(3) << "unregistered forall encountered: " << cur;
              // Invalidate model cache as it may contain intermediate cache
              // values (value not fully computed).
              d_value_cache.clear();
              throw ComputeValueException(cur);
            }
            break;
          }
          [[fallthrough]];

        case Kind::AM_ABSTRACT:
        case Kind::FP_SYMFPU_RM:
        case Kind::FP_SYMFPU_EXP:
        case Kind::FP_SYMFPU_INF:
        case Kind::FP_SYMFPU_NAN:
        case Kind::FP_SYMFPU_SIG:
        case Kind::FP_SYMFPU_SIGN:
        case Kind::FP_SYMFPU_ZERO:
        case Kind::CONSTANT: {
          const Type& type = cur.type();
          if (type.is_bool() || type.is_bv())
          {
            value = d_bv_solver.value(cur);
          }
          else if (type.is_rm() || type.is_fp())
          {
            value = d_fp_solver.value(cur);
          }
          else if (type.is_fun() || type.is_uninterpreted())
          {
            value = d_fun_solver.value(cur);
          }
          else
          {
            assert(type.is_array());
            value = d_array_solver.value(cur);
          }
        }
        break;

        case Kind::EQUAL: {
          const Type& type0 = cur[0].type();
          if (type0.is_bool() || type0.is_bv() || !registered(cur))
          {
            goto EVALUATE;
          }
          // For all other registered equalities use the current value in the
          // bit-vector abstraction.
          else
          {
            assert(registered(cur));
            value = d_bv_solver.value(cur);
          }
        }
        break;

        case Kind::DISTINCT_N: value = d_bv_solver.value(cur); break;

        // Partial Floating-point kinds
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
        case Kind::FP_MAX:
        case Kind::FP_MIN:
          if (registered(cur))
          {
            // Partial floating-point operators should always have a consistent
            // value in the bit-vector abstraction.
            if (k == Kind::FP_TO_SBV || k == Kind::FP_TO_UBV)
            {
              value = d_bv_solver.value(cur);
            }
            else
            {
              value = d_fp_solver.value(cur);
            }
          }
          else
          {
            // Partial floating-point operators have no constant folding
            // available, ask floating-point solver for a value.
            std::vector<Node> values;
            for (const Node& arg : cur)
            {
              values.push_back(cached_value(arg));
            }
            value = d_fp_solver.value(
                nm.mk_node(cur.kind(), values, cur.indices()));
          }
          break;

        // These FP kinds are part of the bit-vector abstraction. Values
        // are computed differently depending on solving mode.
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORMAL:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORMAL:
        case Kind::FP_IS_ZERO:
        case Kind::FP_LEQ:
        case Kind::FP_LT:
          // During solving we use the current value in the bit-vector
          // abstraction.
          if (registered(cur))
          {
            value = d_bv_solver.value(cur);
            break;
          }
          [[fallthrough]];

        // Evaluate
        case Kind::ITE:

        // Boolean kinds
        case Kind::NOT:
        case Kind::AND:

        // Bit-vector kinds
        case Kind::BV_NOT:
        case Kind::BV_AND:
        case Kind::BV_XOR:
        case Kind::BV_EXTRACT:
        case Kind::BV_COMP:
        case Kind::BV_ADD:
        case Kind::BV_MUL:
        case Kind::BV_ULT:
        case Kind::BV_SHL:
        case Kind::BV_SLT:
        case Kind::BV_SHR:
        case Kind::BV_ASHR:
        case Kind::BV_UDIV:
        case Kind::BV_UREM:
        case Kind::BV_CONCAT:

        // Floating-point kinds
        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_ABS:
        case Kind::FP_ADD:
        case Kind::FP_DIV:
        case Kind::FP_FMA:
        case Kind::FP_MUL:
        case Kind::FP_NEG:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_SQRT:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV: {
        EVALUATE:
          std::vector<Node> values;
          for (const Node& arg : cur)
          {
            values.push_back(cached_value(arg));
          }
          value = Evaluator::evaluate(nm, k, values, cur.indices());
        }
        break;

        // Array kinds
        case Kind::CONST_ARRAY:
          value = nm.mk_const_array(cur.type(), {cached_value(cur[0])});
          break;

        case Kind::STORE:
          value = nm.mk_node(Kind::STORE,
                             {cached_value(cur[0]),
                              cached_value(cur[1]),
                              cached_value(cur[2])});
          // Call array solver to normalize value
          value = d_array_solver.value(value);
          break;

        // Function kinds
        case Kind::LAMBDA: value = d_fun_solver.value(cur); break;

        // We should never reach other kinds.
        default: assert(false); break;
      }
      assert(value.is_value() || cur.type().is_array() || cur.type().is_fun()
             || cur.type().is_uninterpreted()
             || d_env.options().rewrite_level() == 0);
      cache_value(cur, value);
    }
    visit.pop_back();
  } while (!visit.empty());

  return cached_value(term);
}

void
SolverEngine::cache_value(const Node& term, const Node& value)
{
  auto it = d_value_cache.find(term);
  assert(it != d_value_cache.end());
  assert(it->second.is_null());
  assert(!value.is_null());
  it->second = value;
}

const Node&
SolverEngine::cached_value(const Node& term) const
{
  auto it = d_value_cache.find(term);
  assert(it != d_value_cache.end());
  assert(!it->second.is_null());
  return it->second;
}

void
SolverEngine::print_statistics()
{
  if (!d_logger.is_msg_enabled(1))
  {
    return;
  }
  if (d_num_printed_stats % 20 == 0)
  {
    // clang-format off
    Msg(1);
    Msg(1) << std::setw(2) << ""
           << std::setw(8) << ""
           << std::setw(8) << ""
           << std::setw(27) << "lemmas" << std::setw(13) << " "
           << std::setw(10) << "aig"
           << std::setw(10) << "aig"
           << std::setw(10) << "cnf"
           << std::setw(10) << "cnf";
    Msg(1) << std::setw(2) << "bv"
           << std::setw(8) << "seconds"
           << std::setw(8) << "MB"
           << std::setw(8) << "t"
           << std::setw(8) << "a"
           << std::setw(8) << "fp"
           << std::setw(8) << "fn"
           << std::setw(8) << "q"
           << std::setw(10) << "consts"
           << std::setw(10) << "ands"
           << std::setw(10) << "vars"
           << std::setw(10) << "clauses";
    Msg(1);
    // clang-format on
  }

  ++d_num_printed_stats;
  const auto& bb_stats = d_bv_solver.statistics_bitblast();
  const char* cur_bv_solver =
      d_bv_solver.cur_solver() == option::BvSolver::BITBLAST ? "s" : "p";
  // clang-format off
  Msg(1) << std::setw(2) << cur_bv_solver
         << std::setw(8)
         << std::setprecision(1)
         << std::fixed
         << d_stats.time_solve.elapsed() / 1000.0
         << std::setw(8)
         << util::current_memory_usage() / static_cast<double>(1 << 20)
         << std::setw(8) << d_stats.num_lemmas
         << std::setw(8) << d_stats.num_lemmas_array
         << std::setw(8) << d_stats.num_lemmas_fp
         << std::setw(8) << d_stats.num_lemmas_fun
         << std::setw(8) << d_stats.num_lemmas_quant
         << std::setw(10) << bb_stats.num_aig_consts
         << std::setw(10) << bb_stats.num_aig_ands
         << std::setw(10) << bb_stats.num_cnf_vars
         << std::setw(10) << bb_stats.num_cnf_clauses;
  // clang-format on
}

SolverEngine::Statistics::Statistics(util::Statistics& stats,
                                     const std::string& prefix)
    : num_lemmas(stats.new_stat<uint64_t>(prefix + "lemmas::total")),
      num_lemmas_array(stats.new_stat<uint64_t>(prefix + "lemmas::array")),
      num_lemmas_fp(stats.new_stat<uint64_t>(prefix + "lemmas::fp")),
      num_lemmas_fun(stats.new_stat<uint64_t>(prefix + "lemmas::fun")),
      num_lemmas_quant(stats.new_stat<uint64_t>(prefix + "lemmas::quant")),
      num_lemmas_abstr(stats.new_stat<uint64_t>(prefix + "lemmas::abstr")),
      num_lemmas_distinctn(
          stats.new_stat<uint64_t>(prefix + "lemmas::distinctn")),
      time_register_term(
          stats.new_stat<util::TimerStatistic>(prefix + "time_register_term")),
      time_solve(stats.new_stat<util::TimerStatistic>(prefix + "time_solve"))
{
}

}  // namespace bzla
