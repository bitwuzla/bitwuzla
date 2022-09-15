#include "option/option.h"

#include <cassert>

namespace bzla::options {

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

  /* --- OptionInfo private ---------------------------------------------------
   */

  void
  OptionInfo::set_option_enum(const std::string& value)
  {
    (void) value;
    assert(false);
  }

/* --- Options public ------------------------------------------------------- */

  Options::Options()
      : d_options(),
        incremental(this,
                    Option::INCREMENTAL,
                    false,
                    "incremental usage",
                    "incremental",
                    "i"),
        log_level(
            this, Option::LOG_LEVEL, 0, 0, 3, "log level", "log-level", "l"),
        sat_solver(this,
                   Option::SAT_SOLVER,
                   SatSolver::CADICAL,
                   {{SatSolver::CADICAL, "cadical"},
                    {SatSolver::CRYPTOMINISAT, "cms"},
                    {SatSolver::KISSAT, "kissat"},
                    {SatSolver::LINGELING, "lingeling"}},
                   "sat solver",
                   "sat-engine",
                   "SE")
  {
    assert(d_options.size() == static_cast<size_t>(Option::NUM_OPTIONS));
}

/* --- Options private ------------------------------------------------------ */

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

}  // namespace bzla::options
