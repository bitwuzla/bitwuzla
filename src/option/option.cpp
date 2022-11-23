#include "option/option.h"

#include <cassert>

namespace bzla::option {

/* --- OptionInfo public ---------------------------------------------------- */

OptionInfo::OptionInfo(Options* options,
                       Option opt,
                       const char* desc,
                       const char* lng,
                       const char* shrt,
                       bool is_expert)
    : d_description(desc), d_long(lng), d_short(shrt), d_is_expert(is_expert)
{
  options->register_option(opt, this);
}

OptionInfo::~OptionInfo() {}

const std::string&
OptionInfo::get_option_enum() const
{
  assert(false);
  static std::string s;
  return s;
}

/* --- OptionInfo private --------------------------------------------------- */

void
OptionInfo::set_option_enum(const std::string& value)
{
  (void) value;
  assert(false);
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

void
Options::set_option_bool(Option opt, bool value)
{
  assert(d_options.at(opt)->is_bool());
  reinterpret_cast<OptionBool*>(d_options.at(opt))->set(value);
}

void
Options::set_option_numeric(Option opt, uint64_t value)
{
  assert(d_options.at(opt)->is_numeric());
  reinterpret_cast<OptionNumeric*>(d_options.at(opt))->set(value);
}

void
Options::set_option_enum(Option opt, const std::string& value)
{
  assert(d_options.at(opt)->is_enum());
  d_options.at(opt)->set_option_enum(value);
}

bool
Options::get_option_bool(Option opt) const
{
  assert(d_options.at(opt)->is_bool());
  return (*reinterpret_cast<OptionBool*>(d_options.at(opt)))();
}

uint64_t
Options::get_option_numeric(Option opt) const
{
  assert(d_options.at(opt)->is_numeric());
  return (*reinterpret_cast<OptionNumeric*>(d_options.at(opt)))();
}

const std::string&
Options::get_option_enum(Option opt) const
{
  assert(d_options.at(opt)->is_enum());
  return d_options.at(opt)->get_option_enum();
}

}  // namespace bzla::option
