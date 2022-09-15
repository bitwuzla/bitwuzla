#include "option/option.h"

#include <cassert>

namespace bzla::options {

/* --- OptionInfo::Enum public ---------------------------------------------- */

OptionInfo::Enum::Enum(uint64_t val, const Enum2StringMap& enum2string)
    : d_value(val), d_default(val), d_enum2string(enum2string)
{
  for (const auto& p : enum2string)
  {
    d_string2enum.emplace(p.second, p.first);
  }
}

/* --- Options public ------------------------------------------------------- */

Options::Options() : d_options(static_cast<size_t>(Option::NUM_OPTIONS))
{
  init(Option::INCREMENTAL,
       incremental,
       false,
       "incremental usage",
       "incremental",
       "i");
  init(Option::LOG_LEVEL, log_level, 0, 0, 3, "log level", "log-level", "l");
  init(Option::SAT_SOLVER,
       sat_solver,
       SatSolver::CADICAL,
       {{SatSolver::CADICAL, "cadical"},
        {SatSolver::CRYPTOMINISAT, "cms"},
        {SatSolver::KISSAT, "kissat"},
        {SatSolver::LINGELING, "lingeling"}},
       "sat solver",
       "sat-engine",
       "SE");
  assert(d_num_initialized == static_cast<size_t>(Option::NUM_OPTIONS));
}

void
Options::init(Option name,
              bool& option,
              bool value,
              const char* desc,
              const char* lng,
              const char* shrt,
              bool is_expert)
{
  assert(desc);
  assert(lng);

  d_num_initialized++;
  option                               = value;
  d_options[static_cast<size_t>(name)] = {value, desc, lng, shrt, is_expert};
}

template <typename T>
void
Options::init(Option name,
              T& option,
              T value,
              const OptionInfo::Enum2StringMap& enum2string,
              const char* desc,
              const char* lng,
              const char* shrt,
              bool is_expert)
{
  assert(desc);
  assert(lng);
  d_num_initialized++;
  option                               = value;
  d_options[static_cast<size_t>(name)] = {
      static_cast<uint64_t>(value), enum2string, desc, lng, shrt, is_expert};
}

void
Options::init(Option name,
              uint64_t& option,
              uint64_t value,
              uint64_t min,
              uint64_t max,
              const char* desc,
              const char* lng,
              const char* shrt,
              bool is_expert)
{
  assert(min <= value);
  assert(value <= max);
  assert(desc);
  assert(lng);

  d_num_initialized++;
  option                               = value;
  d_options[static_cast<size_t>(name)] = {
      value, min, max, desc, lng, shrt, is_expert};
}

}  // namespace bzla::options
