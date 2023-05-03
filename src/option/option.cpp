#include "option/option.h"

#include <algorithm>
#include <cassert>

namespace bzla::option {

/* --- OptionBase public ---------------------------------------------------- */

OptionBase::OptionBase(Options* options,
                       Option opt,
                       const char* desc,
                       const char* lng,
                       const char* shrt,
                       bool is_expert)
    : d_description(desc), d_long(lng), d_short(shrt), d_is_expert(is_expert)
{
  options->register_option(opt, this);
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
OptionModeT<T>::set_str(const std::string& value)
{
  d_value = d_string2mode.at(value);
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
    : d_options(),
      d_name2option(),
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
                "verbose",
                "v"),
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
      smt_comp_mode(
          this, Option::SMT_COMP_MODE, false, "SMT-COMP mode", "smt-comp-mode"),
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
                         "enable embedded contraint preprocessing pass",
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
      dbg_rw_node_inc(
          this,
          Option::DBG_RW_NODE_THRESH,
          0,
          0,
          UINT64_MAX,
          "warn threshold [#] for new nodes created through rewriting steps",
          "dbg-rw-node-thresh",
          nullptr,
          true),
      dbg_pp_node_inc(this,
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
                      true,
                      "check model for each satisfiable query",
                      "check-model"),
      dbg_check_unsat_core(
          this,
          Option::DBG_CHECK_UNSAT_CORE,
          true,
          "check unsat core model for each unsatisfiable query",
          "check-unsat-core")

{
  assert(d_options.size() == static_cast<size_t>(Option::NUM_OPTIONS));
}

/* -------------------------------------------------------------------------- */

bool
Options::is_bool(Option opt) const
{
  return d_options.at(opt)->is_bool();
}

bool
Options::is_numeric(Option opt) const
{
  return d_options.at(opt)->is_numeric();
}

bool
Options::is_mode(Option opt) const
{
  return d_options.at(opt)->is_mode();
}

bool
Options::is_valid(const std::string& name) const
{
  return d_name2option.find(name) != d_name2option.end();
}

bool
Options::is_valid_mode(Option opt, const std::string& value) const
{
  assert(d_options.at(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(d_options.at(opt))->is_valid(value);
}

std::vector<std::string>
Options::modes(Option opt) const
{
  assert(d_options.at(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(d_options.at(opt))->modes();
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
Options::description(Option opt) const
{
  return d_options.at(opt)->description();
}

const char*
Options::lng(Option opt) const
{
  return d_options.at(opt)->lng();
}

const char*
Options::shrt(Option opt) const
{
  return d_options.at(opt)->shrt();
}

template <>
void
Options::set(Option opt, const bool& value)
{
  assert(d_options.at(opt)->is_bool());
  reinterpret_cast<OptionBool*>(d_options.at(opt))->set(value);
}

template <>
void
Options::set(Option opt, const uint64_t& value)
{
  assert(d_options.at(opt)->is_numeric());
  reinterpret_cast<OptionNumeric*>(d_options.at(opt))->set(value);
}

template <>
void
Options::set(Option opt, const std::string& value)
{
  assert(d_options.at(opt)->is_mode());
  reinterpret_cast<OptionMode*>(d_options.at(opt))->set_str(value);
}

void
Options::set(const std::string& name, const std::string& value)
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
      set<bool>(it->second, false);
    }
    else
    {
      assert(v == "1" || v == "true");
      set<bool>(it->second, true);
    }
  }
  else if (is_numeric(it->second))
  {
    set<uint64_t>(it->second, std::stoll(value));
  }
  else
  {
    assert(is_mode(it->second));
    set<std::string>(it->second, value);
  }
}

template <>
const bool&
Options::get(Option opt) const
{
  assert(d_options.at(opt)->is_bool());
  return (*reinterpret_cast<OptionBool*>(d_options.at(opt)))();
}

template <>
const uint64_t&
Options::get(Option opt) const
{
  assert(d_options.at(opt)->is_numeric());
  return (*reinterpret_cast<OptionNumeric*>(d_options.at(opt)))();
}

template <>
const std::string&
Options::get(Option opt) const
{
  assert(d_options.at(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(d_options.at(opt))->get_str();
}

template <>
const bool&
Options::dflt(Option opt) const
{
  assert(d_options.at(opt)->is_bool());
  return reinterpret_cast<OptionBool*>(d_options.at(opt))->dflt();
}

template <>
const uint64_t&
Options::dflt(Option opt) const
{
  assert(d_options.at(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(d_options.at(opt))->dflt();
}

template <>
const std::string&
Options::dflt(Option opt) const
{
  assert(d_options.at(opt)->is_mode());
  return reinterpret_cast<OptionMode*>(d_options.at(opt))->dflt_str();
}

template <>
const uint64_t&
Options::min(Option opt) const
{
  assert(d_options.at(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(d_options.at(opt))->min();
}

template <>
const uint64_t&
Options::max(Option opt) const
{
  assert(d_options.at(opt)->is_numeric());
  return reinterpret_cast<OptionNumeric*>(d_options.at(opt))->max();
}

void
Options::finalize()
{
  if (produce_unsat_assumptions())
  {
    produce_unsat_cores.set(true);
  }
}

/* --- Options private ------------------------------------------------------ */

void
Options::register_option(Option opt, OptionBase* option)
{
  d_options[opt] = option;
  assert(d_name2option.find(option->d_long) == d_name2option.end());
  d_name2option.emplace(option->d_long, opt);
  if (option->d_short)
  {
    assert(d_name2option.find(option->d_short) == d_name2option.end());
    d_name2option.emplace(option->d_short, opt);
  }
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::option
