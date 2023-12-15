/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "option/option.h"

#include <algorithm>
#include <cassert>

#include "config.h"

namespace bzla::option {

Option
operator++(Option& o)
{
  o = static_cast<Option>(static_cast<size_t>(o) + 1);
  return o;
}

/* --- OptionBase public ---------------------------------------------------- */

OptionBase::OptionBase(Options* options,
                       Option opt,
                       const char* desc,
                       const char* lng,
                       const char* shrt,
                       bool is_expert)
    : d_description(desc),
      d_long(lng),
      d_short(shrt),
      d_is_expert(is_expert),
      d_is_user_set(false)
{
  assert(options->d_name2option.find(lng) == options->d_name2option.end());
  options->d_name2option.emplace(lng, opt);
  if (shrt)
  {
    assert(options->d_name2option.find(shrt) == options->d_name2option.end());
    options->d_name2option.emplace(shrt, opt);
  }
}

OptionBase::~OptionBase() {}

/* --- OptionModeT private -------------------------------------------------- */

template <typename T>
std::vector<std::string>
OptionModeT<T>::modes() const
{
  std::vector<std::string> res;
  for (const auto& p : d_mode2string)
  {
    res.push_back(p.second);
  }
  return res;
}

template <typename T>
const std::string&
OptionModeT<T>::get_str() const
{
  return d_mode2string.at(d_value);
}

template <typename T>
void
OptionModeT<T>::set_str(const std::string& value, bool is_user_set)
{
  d_value = d_string2mode.at(value);
  d_is_user_set = is_user_set;
}

template <typename T>
const std::string&
OptionModeT<T>::dflt_str() const
{
  return d_mode2string.at(d_default);
}

template <typename T>
bool
OptionModeT<T>::is_valid(const std::string& value) const
{
  return d_string2mode.find(value) != d_string2mode.end();
}

/* --- Options public ------------------------------------------------------- */

Options::Options()
    : d_name2option(),
      // general
      log_level(
          this, Option::LOG_LEVEL, 0, 0, 3, "log level", "log-level", "l"),
      produce_models(this,
                     Option::PRODUCE_MODELS,
                     false,
                     "model production",
                     "produce-models",
                     "m"),
      produce_unsat_assumptions(this,
                                Option::PRODUCE_UNSAT_ASSUMPTIONS,
                                false,
                                "unsat assumptions production",
                                "produce-unsat-assumptions"),
      produce_unsat_cores(this,
                          Option::PRODUCE_UNSAT_CORES,
                          false,
                          "unsat core production",
                          "produce-unsat-cores"),
      seed(this,
           Option::SEED,
           42,
           0,
           UINT32_MAX,
           "seed for the random number generator",
           "seed",
           "s"),
      verbosity(this,
                Option::VERBOSITY,
                0,
                0,
                VERBOSITY_MAX,
                "verbosity level",
                "verbosity",
                "v"),
      time_limit_per(this,
                     Option::TIME_LIMIT_PER,
                     0,
                     0,
                     UINT64_MAX,
                     "time limit in milliseconds per satisfiability check",
                     "time-limit-per",
                     "T"),
      memory_limit(this,
                   Option::MEMORY_LIMIT,
                   0,
                   0,
                   UINT64_MAX,
                   "set maximum memory limit in MB",
                   "memory-limit",
                   "M"),

      // Bitwuzla-specific
      bv_solver(this,
                Option::BV_SOLVER,
                BvSolver::BITBLAST,
                {{BvSolver::BITBLAST, "bitblast"},
                 {BvSolver::PROP, "prop"},
                 {BvSolver::PREPROP, "preprop"}},
                "bv solver engine",
                "bv-solver"),
      sat_solver(this,
                 Option::SAT_SOLVER,
                 SatSolver::CADICAL,
                 {{SatSolver::CADICAL, "cadical"},
                  {SatSolver::CRYPTOMINISAT, "cms"},
                  {SatSolver::KISSAT, "kissat"}},
                 "backend SAT solver",
                 "sat-solver",
                 "S"),
      rewrite_level(this,
                    Option::REWRITE_LEVEL,
                    REWRITE_LEVEL_MAX,
                    0,
                    REWRITE_LEVEL_MAX,
                    "rewrite level",
                    "rewrite-level",
                    "rwl"),
      // BV: propagation-based local search engine
      prop_nprops(this,
                  Option::PROP_NPROPS,
                  0,
                  0,
                  UINT64_MAX,
                  "number of propagation steps used as a limit for "
                  "propagation-based local search engine",
                  "prop-nprops"),
      prop_nupdates(this,
                    Option::PROP_NUPDATES,
                    0,
                    0,
                    UINT64_MAX,
                    "number of model value updates used as a limit for "
                    "propagation-based local search engine",
                    "prop-nupdates"),
      prop_path_sel(this,
                    Option::PROP_PATH_SEL,
                    PropPathSelection::ESSENTIAL,
                    {{PropPathSelection::ESSENTIAL, "essential"},
                     {PropPathSelection::RANDOM, "random"}},
                    "propagation path selection mode for propagation-based "
                    "local search engine",
                    "prop-path-sel"),
      prop_prob_pick_inv_value(
          this,
          Option::PROP_PROB_PICK_INV_VALUE,
          990,
          0,
          PROB_100,
          "probability for producing inverse rather than consistent "
          "values (interpreted as <n>/1000)",
          "prop-prob-pick-inv-value"),
      prop_prob_pick_random_input(
          this,
          Option::PROP_PROB_PICK_RANDOM_INPUT,
          10,
          0,
          PROB_100,
          "probability for selecting a random input instead of an essential "
          "input (interpreted as <n>/1000)",
          "prop-prob-pick-rand-input"),
      prop_const_bits(this,
                      Option::PROP_CONST_BITS,
                      true,
                      "use constant bits propagation",
                      "prop-const-bits"),
      prop_ineq_bounds(this,
                       Option::PROP_INEQ_BOUNDS,
                       true,
                       "infer inequality bounds for invertibility conditions "
                       "and inverse value computation",
                       "prop-ineq-bounds"),
      prop_opt_lt_concat_sext(
          this,
          Option::PROP_OPT_LT_CONCAT_SEXT,
          true,
          "optimization for inverse value computation of inequalities over "
          "concat and sign extension operands",
          "prop-opt-lt-concat-sext"),
      prop_sext(this,
                Option::PROP_SEXT,
                true,
                "use sign_extend nodes for "
                "concats that represent sign_extend nodes for "
                "propagation-based local search engine",
                "prop-sext"),
      prop_normalize(this,
                     Option::PROP_NORMALIZE,
                     false,
                     "enable normalization for local search",
                     "prop-normalize"),

      // Preprocessing
      preprocess(
          this, Option::PREPROCESS, true, "enable preprocessing", "preprocess"),
      pp_contr_ands(this,
                    Option::PP_CONTRADICTING_ANDS,
                    false,
                    "enable contradicting ands preprocessing pass",
                    "pp-contr-ands"),
      pp_elim_bv_extracts(this,
                          Option::PP_ELIM_BV_EXTRACTS,
                          false,
                          "eliminate extract on BV constants",
                          "pp-elim-extracts"),
      pp_embedded_constr(this,
                         Option::PP_EMBEDDED_CONSTR,
                         true,
                         "enable embedded constraint preprocessing pass",
                         "pp-embedded"),
      pp_flatten_and(this,
                     Option::PP_FLATTEN_AND,
                     true,
                     "enable AND flattening preprocessing pass",
                     "pp-flatten-and"),
      pp_normalize(this,
                   Option::PP_NORMALIZE,
                   true,
                   "enable normalization pass",
                   "pp-normalize"),
      pp_normalize_share_aware(this,
                               Option::PP_NORMALIZE_SHARE_AWARE,
                               true,
                               "disable normalizations in normalization pass "
                               "that may yield blow-up on the bit-level",
                               "pp-normalize-share-aware"),
      pp_skeleton_preproc(this,
                          Option::PP_SKELETON_PREPROC,
                          true,
                          "enable skeleton preprocessing pass",
                          "pp-skeleton-preproc"),
      pp_variable_subst(this,
                        Option::PP_VARIABLE_SUBST,
                        true,
                        "enable variable substitution preprocessing pass",
                        "pp-variable-subst"),
      pp_variable_subst_norm_eq(
          this,
          Option::PP_VARIABLE_SUBST_NORM_EQ,
          true,
          "enable equality normalization via Gaussian elimination if variable "
          "substitution preprocessing pass is enabled",
          "pp-variable-subst-norm-eq"),
      pp_variable_subst_norm_diseq(
          this,
          Option::PP_VARIABLE_SUBST_NORM_DISEQ,
          false,
          "enable disequality normalization if variable substitution "
          "preprocessing pass is enabled",
          "pp-variable-subst-norm-diseq"),
      pp_variable_subst_norm_bv_ineq(
          this,
          Option::PP_VARIABLE_SUBST_NORM_BV_INEQ,
          false,
          "enable bit-vector unsigned inequality normalization if variable "
          "substitution preprocessing pass is enabled",
          "pp-variable-subst-norm-bv-ineq"),

      // Debugging
      dbg_rw_node_thresh(
          this,
          Option::DBG_RW_NODE_THRESH,
          0,
          0,
          UINT64_MAX,
          "warn threshold [#] for new nodes created through rewriting steps",
          "dbg-rw-node-thresh",
          nullptr,
          true),
      dbg_pp_node_thresh(this,
                         Option::DBG_PP_NODE_THRESH,
                         0,
                         0,
                         100,
                         "warn threshold [%] for new nodes created through "
                         "preprocessing in total",
                         "dbg-pp-node-thresh",
                         nullptr,
                         true),
      dbg_check_model(this,
                      Option::DBG_CHECK_MODEL,
                      config::is_debug_build,
                      "check model for each satisfiable query",
                      "check-model"),
      dbg_check_unsat_core(
          this,
          Option::DBG_CHECK_UNSAT_CORE,
          config::is_debug_build,
          "check unsat core model for each unsatisfiable query",
          "check-unsat-core")

{
}

/* -------------------------------------------------------------------------- */

bool
Options::is_bool(Option opt)
{
  return data(opt)->is_bool();
}

bool
Options::is_numeric(Option opt)
{
  return data(opt)->is_numeric();
}

bool
Options::is_mode(Option opt)
{
  return data(opt)->is_mode();
}

bool
Options::is_valid(const std::string& name) const
{
  return d_name2option.find(name) != d_name2option.end();
}

bool
Options::is_valid_mode(Option opt, const std::string& value)
{
  assert(data(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(data(opt))->is_valid(value);
}

std::vector<std::string>
Options::modes(Option opt)
{
  assert(data(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(data(opt))->modes();
}

Option
Options::option(const std::string& name) const
{
  assert(is_valid(name));
  return d_name2option.at(name);
}

Option
Options::option(const char* name) const
{
  assert(is_valid(name));
  return d_name2option.at(name);
}

const char*
Options::description(Option opt)
{
  return data(opt)->description();
}

const char*
Options::lng(Option opt)
{
  return data(opt)->lng();
}

const char*
Options::shrt(Option opt)
{
  return data(opt)->shrt();
}

template <>
void
Options::set(Option opt, const bool& value, bool is_user_set)
{
  assert(data(opt)->is_bool());
  assert(is_user_set || !data(opt)->d_is_user_set);
  reinterpret_cast<OptionBool*>(data(opt))->set(value, is_user_set);
}

template <>
void
Options::set(Option opt, const uint64_t& value, bool is_user_set)
{
  assert(data(opt)->is_numeric());
  assert(is_user_set || !data(opt)->d_is_user_set);
  reinterpret_cast<OptionNumeric*>(data(opt))->set(value, is_user_set);
}

template <>
void
Options::set(Option opt, const std::string& value, bool is_user_set)
{
  assert(data(opt)->is_mode());
  assert(is_user_set || !data(opt)->d_is_user_set);
  reinterpret_cast<OptionMode*>(data(opt))->set_str(value, is_user_set);
}

void
Options::set(const std::string& name,
             const std::string& value,
             bool is_user_set)
{
  auto it = d_name2option.find(name);
  assert(it != d_name2option.end());
  if (is_bool(it->second))
  {
    std::string v = value;
    v.erase(std::remove_if(v.begin(), v.end(), ::isspace), v.end());
    std::transform(v.begin(), v.end(), v.begin(), ::tolower);
    if (v == "0" || v == "false")
    {
      set<bool>(it->second, false, is_user_set);
    }
    else
    {
      assert(v == "1" || v == "true");
      set<bool>(it->second, true, is_user_set);
    }
  }
  else if (is_numeric(it->second))
  {
    set<uint64_t>(it->second, std::stoll(value), is_user_set);
  }
  else
  {
    assert(is_mode(it->second));
    set<std::string>(it->second, value, is_user_set);
  }
}

template <>
const bool&
Options::get(Option opt)
{
  assert(data(opt)->is_bool());
  return (*reinterpret_cast<OptionBool*>(data(opt)))();
}

template <>
const uint64_t&
Options::get(Option opt)
{
  assert(data(opt)->is_numeric());
  return (*reinterpret_cast<OptionNumeric*>(data(opt)))();
}

template <>
const std::string&
Options::get(Option opt)
{
  assert(data(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(data(opt))->get_str();
}

template <>
const bool&
Options::dflt(Option opt)
{
  assert(data(opt)->is_bool());
  return reinterpret_cast<OptionBool*>(data(opt))->dflt();
}

template <>
const uint64_t&
Options::dflt(Option opt)
{
  assert(data(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(data(opt))->dflt();
}

template <>
const std::string&
Options::dflt(Option opt)
{
  assert(data(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(data(opt))->dflt_str();
}

template <>
const uint64_t&
Options::min(Option opt)
{
  assert(data(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(data(opt))->min();
}

template <>
const uint64_t&
Options::max(Option opt)
{
  assert(data(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(data(opt))->max();
}

void
Options::finalize()
{
  if (produce_unsat_assumptions())
  {
    // we overrule the user here in case they disabled unsat cores, we must
    // enable unsat cores when enabling unsat assumptions
    produce_unsat_cores.set(true);
  }
  // configure default values for number of propagations and updates in case
  // of sequential portfolio bv solver configuration PREPROP
  if (bv_solver() == BvSolver::PREPROP)
  {
    if (!prop_nprops.d_is_user_set)
    {
      prop_nprops.set(10000);
    }
    if (!prop_nupdates.d_is_user_set)
    {
      prop_nupdates.set(2000000);
    }
  }
  // Disable preprocessing passes if not explicitely enabled by user
  if (!preprocess())
  {
    for (Option o = Option::PREPROCESS; o != Option::PP_OPT_END; ++o)
    {
      auto d = data(o);
      if (!d->d_is_user_set)
      {
        assert(d->is_bool());
        auto opt = static_cast<OptionBool*>(d);
        opt->set(false);
      }
    }
  }
}

/* --- Options private ------------------------------------------------------ */

OptionBase*
Options::data(Option opt)
{
  switch (opt)
  {
    case Option::LOG_LEVEL: return &log_level;
    case Option::PRODUCE_MODELS: return &produce_models;
    case Option::PRODUCE_UNSAT_ASSUMPTIONS: return &produce_unsat_assumptions;
    case Option::PRODUCE_UNSAT_CORES: return &produce_unsat_cores;
    case Option::SAT_SOLVER: return &sat_solver;
    case Option::SEED: return &seed;
    case Option::VERBOSITY: return &verbosity;
    case Option::TIME_LIMIT_PER: return &time_limit_per;
    case Option::MEMORY_LIMIT: return &memory_limit;

    case Option::BV_SOLVER: return &bv_solver;
    case Option::REWRITE_LEVEL: return &rewrite_level;

    case Option::PROP_NPROPS: return &prop_nprops;
    case Option::PROP_NUPDATES: return &prop_nupdates;
    case Option::PROP_PATH_SEL: return &prop_path_sel;
    case Option::PROP_PROB_PICK_INV_VALUE: return &prop_prob_pick_inv_value;
    case Option::PROP_PROB_PICK_RANDOM_INPUT:
      return &prop_prob_pick_random_input;
    case Option::PROP_CONST_BITS: return &prop_const_bits;
    case Option::PROP_INEQ_BOUNDS: return &prop_ineq_bounds;
    case Option::PROP_OPT_LT_CONCAT_SEXT: return &prop_opt_lt_concat_sext;
    case Option::PROP_SEXT: return &prop_sext;
    case Option::PROP_NORMALIZE: return &prop_normalize;

    case Option::PREPROCESS: return &preprocess;
    case Option::PP_CONTRADICTING_ANDS: return &pp_contr_ands;
    case Option::PP_ELIM_BV_EXTRACTS: return &pp_elim_bv_extracts;
    case Option::PP_EMBEDDED_CONSTR: return &pp_embedded_constr;
    case Option::PP_FLATTEN_AND: return &pp_flatten_and;
    case Option::PP_NORMALIZE: return &pp_normalize;
    case Option::PP_NORMALIZE_SHARE_AWARE: return &pp_normalize_share_aware;
    case Option::PP_SKELETON_PREPROC: return &pp_skeleton_preproc;
    case Option::PP_VARIABLE_SUBST: return &pp_variable_subst;
    case Option::PP_VARIABLE_SUBST_NORM_BV_INEQ:
      return &pp_variable_subst_norm_bv_ineq;
    case Option::PP_VARIABLE_SUBST_NORM_EQ: return &pp_variable_subst_norm_eq;
    case Option::PP_VARIABLE_SUBST_NORM_DISEQ:
      return &pp_variable_subst_norm_diseq;

    case Option::DBG_RW_NODE_THRESH: return &dbg_rw_node_thresh;
    case Option::DBG_PP_NODE_THRESH: return &dbg_pp_node_thresh;
    case Option::DBG_CHECK_MODEL: return &dbg_check_model;
    case Option::DBG_CHECK_UNSAT_CORE: return &dbg_check_unsat_core;

    case Option::PP_OPT_END:
    case Option::NUM_OPTIONS: assert(false);
  }
  return nullptr;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::option
