#include "option/option.h"

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

/* --- OptionEnumT private -------------------------------------------------- */

template <typename T>
std::vector<std::string>
OptionEnumT<T>::modes() const
{
  std::vector<std::string> res;
  for (const auto& p : d_enum2string)
  {
    res.push_back(p.second);
  }
  return res;
}

template <typename T>
const std::string&
OptionEnumT<T>::get_str() const
{
  return d_enum2string.at(d_value);
}

template <typename T>
void
OptionEnumT<T>::set_str(const std::string& value)
{
  d_value = d_string2enum.at(value);
}

template <typename T>
const std::string&
OptionEnumT<T>::dflt_str() const
{
  return d_enum2string.at(d_default);
}

template <typename T>
bool
OptionEnumT<T>::is_valid(const std::string& value) const
{
  return d_string2enum.find(value) != d_string2enum.end();
}

/* --- Options public ------------------------------------------------------- */

Options::Options()
    : d_options(),
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
Options::is_enum(Option opt) const
{
  return d_options.at(opt)->is_enum();
}

bool
Options::is_valid_enum(Option opt, const std::string& value) const
{
  assert(d_options.at(opt)->is_enum());
  return reinterpret_cast<OptionEnum*>(d_options.at(opt))->is_valid(value);
}

std::vector<std::string>
Options::modes(Option opt) const
{
  assert(d_options.at(opt)->is_enum());
  return reinterpret_cast<OptionEnum*>(d_options.at(opt))->modes();
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
  assert(d_options.at(opt)->is_enum());
  reinterpret_cast<OptionEnum*>(d_options.at(opt))->set_str(value);
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
  assert(d_options.at(opt)->is_enum());
  return reinterpret_cast<OptionEnum*>(d_options.at(opt))->get_str();
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
  assert(d_options.at(opt)->is_enum());
  return reinterpret_cast<OptionEnum*>(d_options.at(opt))->dflt_str();
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

/* -------------------------------------------------------------------------- */
}  // namespace bzla::option
