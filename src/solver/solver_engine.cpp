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

#include "env.h"
#include "printer/printer.h"
#include "rewrite/evaluator.h"
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
      d_quant_solver(context.env(), d_solver_state)
{
}

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
    // Reset term registration flag
    d_new_terms_registered = false;

    // Process lemmas generated in previous iteration.
    process_lemmas();

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
  assert(d_sat_state == Result::SAT);
  Log(2) << "get value for (in_solving: " << d_in_solving_mode << "): " << term;

  if (d_in_solving_mode)
  {
    process_term(term);
  }

  return _value(term);
}

void
SolverEngine::unsat_core(std::vector<Node>& core) const
{
  assert(d_sat_state == Result::UNSAT);
  d_bv_solver.unsat_core(core);
}

void
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
  }
}

void
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
    auto res = solve();
    assert(res == Result::SAT);
    (void) res;
  }
}

backtrack::BacktrackManager*
SolverEngine::backtrack_mgr()
{
  return &d_backtrack_mgr;
}

/* --- SolverEngine private ------------------------------------------------- */

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
  // Send assertion to bit-vector solver.
  auto [it, inserted] = d_register_assertion_cache.insert(assertion);
  if (inserted)
  {
    Log(2) << "register assertion (top: " << top_level << "): " << assertion;
    d_bv_solver.register_assertion(assertion, top_level, is_lemma);
    d_quant_solver.register_assertion(assertion);
  }
  process_term(assertion);
}

void
SolverEngine::process_term(const Node& term)
{
  util::Timer timer(d_stats.time_register_term);
  node::node_ref_vector visit{term};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    auto [it, inserted] = d_register_term_cache.insert(cur);
    if (inserted)
    {
      if (array::ArraySolver::is_theory_leaf(cur))
      {
        Log(2) << "register array term: " << cur;
        d_array_solver.register_term(cur);
        d_new_terms_registered = true;
      }
      else if (fun::FunSolver::is_theory_leaf(cur))
      {
        Log(2) << "register function term: " << cur;
        d_fun_solver.register_term(cur);
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
        if (fp::FpSolver::is_theory_leaf(cur))
        {
          Log(2) << "register floating-point term: " << cur;
          d_fp_solver.register_term(cur);
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
  auto it = d_register_term_cache.find(term);
  return it != d_register_term_cache.end();
}

void
SolverEngine::process_lemmas()
{
  for (const Node& lemma : d_lemmas)
  {
    process_assertion(lemma, true, true);
  }
  d_lemmas.clear();
}

Node
SolverEngine::_value(const Node& term)
{
  NodeManager& nm = NodeManager::get();
  node_ref_vector visit{term};

  do
  {
    const Node& cur = visit.back();

    auto [it, inserted] = d_value_cache.emplace(cur, Node());
    if (inserted)
    {
      // During solving we query bit-vector solver for all Bool/bit-vector
      // assignments.
      if (d_in_solving_mode)
      {
        if (bv::BvSolver::is_leaf(cur))
        {
          continue;
        }
      }
      else
      {
        Kind k = cur.kind();
        if (k == Kind::APPLY || k == Kind::SELECT || k == Kind::FORALL
            || k == Kind::LAMBDA)
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
      if (!d_in_solving_mode && !registered(cur))
      {
        // If an unregistered quantifier is encountered, we cannot compute a
        // value without another solve() call. Hence, we return a null node
        // and handle this case in value().
        if (k == Kind::FORALL)
        {
          // Invalidate model cache as it may contain intermediate cache values
          // (value not fully computed).
          d_value_cache.clear();
          throw ComputeValueException(cur);
        }
        // Compute value of select based on current array model.
        else if (k == Kind::SELECT)
        {
          Log(3) << "unregistered select encountered: " << cur;
          value = d_array_solver.value(cur);
          goto CACHE_VALUE;
        }
        // Compute value of function application based on current function
        // model.
        else if (k == Kind::APPLY)
        {
          Log(3) << "unregistered apply encountered: " << cur;
          value = d_fun_solver.value(cur);
          goto CACHE_VALUE;
        }
        // Compute value of equality based on the corresponding theory solver's
        // model.
        else if (k == Kind::EQUAL)
        {
          const Type& type0 = cur[0].type();
          if (type0.is_fp() || type0.is_rm())
          {
            goto COMPUTE_FP_VALUE;
          }
          else if (type0.is_array())
          {
            Log(3) << "unregistered array equality encountered: " << cur;
            value = d_array_solver.value(cur);
            goto CACHE_VALUE;
          }
          else if (type0.is_fun() || type0.is_uninterpreted())
          {
            Log(3) << "unregistered function equality encountered: " << cur;
            value = d_fun_solver.value(cur);
            goto CACHE_VALUE;
          }
        }
        // Partial FP functions: no constant folding available, ask
        // floating-point solver for a value.
        else if (k == Kind::FP_TO_SBV || k == Kind::FP_TO_UBV
                 || k == Kind::FP_MIN || k == Kind::FP_MAX)
        {
          std::vector<Node> values;
          for (const Node& arg : cur)
          {
            values.push_back(cached_value(arg));
            assert(!values.back().is_null());
          }
          value =
              d_fp_solver.value(nm.mk_node(cur.kind(), values, cur.indices()));
          goto CACHE_VALUE;
        }
      }

      switch (k)
      {
        case Kind::VALUE: value = cur; break;

        case Kind::APPLY:
        case Kind::SELECT:
        case Kind::FORALL:
          // Just use value from bit-vector abstraction.
          [[fallthrough]];

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
          if (type0.is_bool())
          {
            value = nm.mk_value(cached_value(cur[0]).value<bool>()
                                == cached_value(cur[1]).value<bool>());
          }
          else if (type0.is_bv())
          {
            value = nm.mk_value(cached_value(cur[0]).value<BitVector>()
                                == cached_value(cur[1]).value<BitVector>());
          }
          else
          {
            // For all other equalities use the current value in the bit-vector
            // abstraction.
            value = d_bv_solver.value(cur);
          }
        }
        break;

        case Kind::ITE:
          value = cached_value(cur[0]).value<bool>() ? cached_value(cur[1])
                                                     : cached_value(cur[2]);
          break;

        // Boolean kinds
        case Kind::NOT:
          value = nm.mk_value(!cached_value(cur[0]).value<bool>());
          break;

        case Kind::AND:
          value = nm.mk_value(cached_value(cur[0]).value<bool>()
                              && cached_value(cur[1]).value<bool>());
          break;

        case Kind::OR:
          value = nm.mk_value(cached_value(cur[0]).value<bool>()
                              || cached_value(cur[1]).value<bool>());
          break;

        // Bit-vector kinds
        case Kind::BV_NOT:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvnot());
          break;

        case Kind::BV_DEC:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvdec());
          break;

        case Kind::BV_INC:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvinc());
          break;

        case Kind::BV_AND:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvand(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_XOR:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvxor(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_EXTRACT:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvextract(
              cur.index(0), cur.index(1)));
          break;

        case Kind::BV_COMP: {
          bool equal = cached_value(cur[0]).value<BitVector>()
                       == cached_value(cur[1]).value<BitVector>();
          value = nm.mk_value(BitVector::from_ui(1, equal ? 1 : 0));
        }
        break;

        case Kind::BV_ADD:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvadd(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_MUL:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvmul(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_ULT:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().compare(
                                  cached_value(cur[1]).value<BitVector>())
                              < 0);
          break;

        case Kind::BV_SHL:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvshl(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_SLT:
          value = nm.mk_value(
              cached_value(cur[0]).value<BitVector>().signed_compare(
                  cached_value(cur[1]).value<BitVector>())
              < 0);
          break;

        case Kind::BV_SHR:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvshr(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_ASHR:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvashr(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_UDIV:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvudiv(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_UREM:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvurem(
              cached_value(cur[1]).value<BitVector>()));
          break;

        case Kind::BV_CONCAT:
          value = nm.mk_value(cached_value(cur[0]).value<BitVector>().bvconcat(
              cached_value(cur[1]).value<BitVector>()));
          break;

        // Floating-point kinds

        // Partial floating-point operators should always have a consistent
        // value in the bit-vector abstraction. Unregistered case is handled
        // further above.
        case Kind::FP_TO_SBV:
        case Kind::FP_TO_UBV:
          assert(registered(cur));
          value = d_bv_solver.value(cur);
          break;

        case Kind::FP_MAX:
        case Kind::FP_MIN:
          assert(registered(cur));
          value = d_fp_solver.value(cur);
          break;

        // These FP kinds that are part of the bit-vector abstraction. Values
        // are computed differently depending on solving mode.
        case Kind::FP_IS_INF:
        case Kind::FP_IS_NAN:
        case Kind::FP_IS_NEG:
        case Kind::FP_IS_NORMAL:
        case Kind::FP_IS_POS:
        case Kind::FP_IS_SUBNORMAL:
        case Kind::FP_IS_ZERO:
        case Kind::FP_EQUAL:
        case Kind::FP_LEQ:
        case Kind::FP_LT:
          // During solving we use the current value in the bit-vector
          // abstraction.
          if (d_in_solving_mode)
          {
            value = d_bv_solver.value(cur);
            break;
          }
          [[fallthrough]];

        case Kind::FP_TO_FP_FROM_FP:
        case Kind::FP_ABS:
        case Kind::FP_ADD:
        case Kind::FP_DIV:
        case Kind::FP_FMA:
        case Kind::FP_FP:
        case Kind::FP_GEQ:
        case Kind::FP_GT:
        case Kind::FP_MUL:
        case Kind::FP_NEG:
        case Kind::FP_REM:
        case Kind::FP_RTI:
        case Kind::FP_SQRT:
        case Kind::FP_TO_FP_FROM_BV:
        case Kind::FP_TO_FP_FROM_SBV:
        case Kind::FP_TO_FP_FROM_UBV:
        case Kind::FP_SUB: {
        COMPUTE_FP_VALUE:
          std::vector<Node> values;
          for (const Node& arg : cur)
          {
            values.push_back(cached_value(arg));
            assert(!values.back().is_null());
          }
          value = Evaluator::evaluate(cur.kind(), values, cur.indices());
        }
        break;

        // Array kinds
        case Kind::CONST_ARRAY:
        case Kind::STORE: value = d_array_solver.value(cur); break;

        // Function kinds
        case Kind::LAMBDA: value = d_fun_solver.value(cur); break;

        // We should never reach other kinds.
        default: assert(false); break;
      }
    CACHE_VALUE:
      assert(value.is_value() || cur.type().is_array() || cur.type().is_fun()
             || cur.type().is_uninterpreted());
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
    : num_lemmas(stats.new_stat<uint64_t>(prefix + "lemmas")),
      num_lemmas_array(stats.new_stat<uint64_t>(prefix + "lemmas_array")),
      num_lemmas_fp(stats.new_stat<uint64_t>(prefix + "lemmas_fp")),
      num_lemmas_fun(stats.new_stat<uint64_t>(prefix + "lemmas_fun")),
      num_lemmas_quant(stats.new_stat<uint64_t>(prefix + "lemmas_quant")),
      time_register_term(
          stats.new_stat<util::TimerStatistic>(prefix + "time_register_term")),
      time_solve(stats.new_stat<util::TimerStatistic>(prefix + "time_solve"))
{
}

}  // namespace bzla
