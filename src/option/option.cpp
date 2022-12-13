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
      d_lng2option(),
      // general
      incremental(this,
                  Option::INCREMENTAL,
                  false,
                  "incremental usage",
                  "incremental",
                  "i"),
      log_level(
          this, Option::LOG_LEVEL, 0, 0, 3, "log level", "log-level", "l"),
      produce_models(this,
                     Option::PRODUCE_MODELS,
                     false,
                     "model production",
                     "models",
                     "m"),
      produce_unsat_cores(this,
                          Option::PRODUCE_UNSAT_CORES,
                          false,
                          "unsat core production",
                          "unsat-cores"),
      sat_solver(this,
                 Option::SAT_SOLVER,
                 SatSolver::CADICAL,
                 {{SatSolver::CADICAL, "cadical"},
                  {SatSolver::CRYPTOMINISAT, "cms"},
                  {SatSolver::KISSAT, "kissat"},
                  {SatSolver::LINGELING, "lingeling"}},
                 "backend SAT solver",
                 "sat-solver",
                 "S"),
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
      bv_solver(this,
                Option::BV_SOLVER,
                BvSolver::BITBLAST,
                {{BvSolver::BITBLAST, "bitblast"},
                 {BvSolver::PROP, "prop"},
                 {BvSolver::PREPROP, "preprop"}},
                "bv solver engine",
                "bv-solver"),
      smt_comp_mode(
          this, Option::SMT_COMP_MODE, false, "SMT-COMP mode", "smt-comp-mode"),
      // propagation-based local search engine
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
                      "prop-ineq-bounds"),
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
                "prop-sext")
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
Options::is_valid(const std::string& lng) const
{
  return d_lng2option.find(lng) != d_lng2option.end();
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
Options::option(const std::string& lng) const
{
  assert(is_valid(lng));
  return d_lng2option.at(lng);
}

Option
Options::option(const char* lng) const
{
  assert(is_valid(lng));
  return d_lng2option.at(lng);
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
Options::set(const std::string& lng, const std::string& value)
{
  auto it = d_lng2option.find(lng);
  assert(it != d_lng2option.end());
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
    set<uint64_t>(it->second, std::stol(value));
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

/* --- Options private ------------------------------------------------------ */

void
Options::register_option(Option opt, OptionBase* option)
{
  d_options[opt] = option;
  d_lng2option.emplace(option->d_long, opt);
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::option
