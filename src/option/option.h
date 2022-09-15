#ifndef BZLA_OPTION_OPTION_H_INCLUDED
#define BZLA_OPTION_OPTION_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <memory>
#include <unordered_map>
#include <variant>
#include <vector>

namespace bzla::options {

enum class Option
{
  SAT_ENGINE,   // enum
  INCREMENTAL,  // bool
  LOGLEVEL,     // numeric

  NUM_OPTIONS
};

enum SatSolver
{
  CADICAL,
  CRYPTOMINISAT,
  KISSAT,
  LINGELING,
};

class OptionInfo
{
 public:
  struct Boolean
  {
    Boolean(bool val, bool dflt) : d_value(val), d_default(dflt) {}
    bool d_value;
    bool d_default;
  };

  struct Enum
  {
    Enum(uint64_t val,
         uint64_t dflt,
         const std::unordered_map<const char*, uint64_t> string2enum,
         const std::unordered_map<uint64_t, const char*> enum2string)
        : d_value(val),
          d_default(dflt),
          d_string2enum(string2enum),
          d_enum2string(enum2string)
    {
    }
    uint64_t d_value;
    uint64_t d_default;
    std::unordered_map<const char*, uint64_t> d_string2enum;
    std::unordered_map<uint64_t, const char*> d_enum2string;
  };

  struct Numeric
  {
    Numeric(uint64_t val, uint64_t dflt, uint64_t min, uint64_t max)
        : d_value(val), d_default(dflt), d_min(min), d_max(max)
    {
    }
    uint64_t d_value;
    uint64_t d_default;
    uint64_t d_min;
    uint64_t d_max;
  };

  OptionInfo() {}

  OptionInfo(bool value,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr)
      : d_value(Boolean(value, value)),
        d_description(desc),
        d_long(lng),
        d_short(shrt)
  {
  }
  OptionInfo(uint64_t value,
             const std::unordered_map<const char*, uint64_t> string2enum,
             const std::unordered_map<uint64_t, const char*> enum2string,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr)
      : d_value(Enum(value, value, string2enum, enum2string)),
        d_description(desc),
        d_long(lng),
        d_short(shrt)
  {
  }
  OptionInfo(uint64_t value,
             uint64_t min,
             uint64_t max,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr)
      : d_value(Numeric(value, value, min, max)),
        d_description(desc),
        d_long(lng),
        d_short(shrt)
  {
  }

  std::variant<std::monostate, Boolean, Enum, Numeric> d_value;
  const char* d_description;
  const char* d_long;
  const char* d_short;
};

struct Options
{
  bool incremental;
  uint64_t log_level;
  SatSolver sat_solver;

  Options() : d_info(static_cast<size_t>(Option::NUM_OPTIONS))
  {
    init(Option::INCREMENTAL,
         incremental,
         false,
         "incremental usage",
         "incremental",
         "i");
    init(Option::LOGLEVEL, log_level, 0, 0, 3, "log level", "loglevel", "l");
    init(Option::SAT_ENGINE,
         sat_solver,
         SatSolver::CADICAL,
         {{"cadical", SatSolver::CADICAL},
          {"cms", SatSolver::CRYPTOMINISAT},
          {"kissat", SatSolver::KISSAT},
          {"lingeling", SatSolver::LINGELING}},
         {{SatSolver::CADICAL, "cadical"},
          {SatSolver::CRYPTOMINISAT, "cms"},
          {SatSolver::KISSAT, "kissat"},
          {SatSolver::LINGELING, "lingeling"}},
         "sat solver",
         "sat-engine",
         "SE");
  }

  void init(Option name,
            bool& option,
            bool value,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr)
  {
    d_num_initialized++;
    option                            = value;
    d_info[static_cast<size_t>(name)] = {value, desc, lng, shrt};
  }

  template <typename T>
  void init(Option name,
            T& option,
            T value,
            const std::unordered_map<const char*, uint64_t> string2enum,
            const std::unordered_map<uint64_t, const char*> enum2string,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr)
  {
    d_num_initialized++;
    option                            = value;
    d_info[static_cast<size_t>(name)] = {static_cast<uint64_t>(value),
                                         string2enum,
                                         enum2string,
                                         desc,
                                         lng,
                                         shrt};
  }

  void init(Option name,
            uint64_t& option,
            uint64_t value,
            uint64_t min,
            uint64_t max,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr)
  {
    d_num_initialized++;
    option                            = value;
    d_info[static_cast<size_t>(name)] = {value, min, max, desc, lng, shrt};
  }

 private:
  size_t d_num_initialized = 0;
  std::vector<OptionInfo> d_info;
};

}  // namespace bzla::options

#endif
