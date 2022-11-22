#ifndef BZLA_OPTION_OPTION_H_INCLUDED
#define BZLA_OPTION_OPTION_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace bzla::option {

/* -------------------------------------------------------------------------- */

enum class Option
{
  INCREMENTAL,  // bool
  LOG_LEVEL,    // numeric
  SAT_SOLVER,   // enum
  SEED,         // numeric
  VERBOSITY,    // numeric

  BV_SOLVER,  // enum

  PROP_NPROPS,                  // numeric
  PROP_NUPDATES,                // numeric
  PROP_PATH_SEL,                // enum
  PROP_PROB_PICK_INV_VALUE,     // numeric
  PROP_PROB_PICK_RANDOM_INPUT,  // numeric
  PROP_CONST_BITS,              // bool
  PROP_INEQ_BOUNDS,             // bool
  PROP_OPT_LT_CONCAT_SEXT,      // bool
  PROP_SEXT,                    // bool

  UNDEFINED,  // temporary, until API is done
  NUM_OPTIONS,
};

/* -------------------------------------------------------------------------- */

enum class BvSolver
{
  BITBLAST,
  PROP,
  PREPROP,
};

enum class SatSolver
{
  CADICAL,
  CRYPTOMINISAT,
  KISSAT,
  LINGELING,
};

enum class PropPathSelection
{
  ESSENTIAL,
  RANDOM,
};

/* -------------------------------------------------------------------------- */

class Options;

/** The base class for option info data. */
class OptionInfo
{
  friend Options;

 public:
  /**
   * Constructor.
   * @param options   The associated options object.
   * @param opt       The corresponding option.
   * @param desc      The option description (used for CLI help message).
   * @param lng       The long name of the option (`--<lng>` for the CLI).
   * @param shrt      The short name of the option (`-<shrt>` for the CLI).
   * @param is_expert True if this is an expert option.
   */
  OptionInfo(Options* options,
             Option opt,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false);
  OptionInfo() = delete;
  virtual ~OptionInfo();

  /** @return True if this option is a Boolean option. */
  virtual bool is_bool() const { return false; }
  /** @return True if this option is a numeric option. */
  virtual bool is_numeric() const { return false; }
  /** @return True if this option is an option that takes an enum value. */
  virtual bool is_enum() const { return false; }

 protected:
  /**
   * Set current value of enum option.
   * @param value The string representation of the enum value.
   */
  virtual void set_option_enum(const std::string& value);
  /**
   * Get the string representation of the current value of an enum options.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @return The current value of an enum option.
   */
  virtual const std::string& get_option_enum() const;

  /** The option description. */
  const char* d_description;
  /** The long name of the option (`--<lng>` in the CLI). */
  const char* d_long;
  /** The short name of the option (`-<shrt>` in the CLI). */
  const char* d_short;
  /** True if this is an expert option. */
  bool d_is_expert;
};

/** Option info data for Boolean options. */
class OptionBool : public OptionInfo
{
 public:
  /**
   * Constructor.
   *
   * @note On construction, given Boolean value determines the initial and the
   *       default value of the option.
   *
   * @param options   The associated options object.
   * @param opt       The corresponding option.
   * @param value     The initial and default value of the option.
   * @param desc      The option description (used for CLI help message).
   * @param lng       The long name of the option (`--<lng>` for the CLI).
   * @param shrt      The short name of the option (`-<shrt>` for the CLI).
   * @param is_expert True if this is an expert option.
   */
  OptionBool(Options* options,
             Option opt,
             bool value,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : OptionInfo(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value)
  {
  }
  OptionBool() = delete;

  bool is_bool() const override { return true; }

  /**
   * Get the current value of a Boolean option.
   * @return The current value of a Boolean option.
   */
  bool operator()() const { return d_value; }
  /**
   * Set the current value of a Boolean option.
   * @param value The current value.
   */
  void set(bool value) { d_value = value; }

 private:
  /** The current value. */
  bool d_value;
  /** The default value. */
  bool d_default;
};

/** Option info data for numeric options. */
class OptionNumeric : public OptionInfo
{
 public:
  /**
   * Constructor.
   *
   * @note On construction, given uint64_t value determines the initial and the
   *       default integer value of a numeric option.
   *
   * @param options   The associated options object.
   * @param opt       The corresponding option.
   * @param value     The initial and default value of the option.
   * @param min       The minimum value of the option.
   * @param max       The maximum value of the option.
   * @param desc      The option description (used for the CLI help message).
   * @param lng       The long name of the option (`--<lng>` in the CLI).
   * @param shrt      The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert True if this is an expert option.
   */
  OptionNumeric(Options* options,
                Option opt,
                uint64_t value,
                uint64_t min,
                uint64_t max,
                const char* desc,
                const char* lng,
                const char* shrt = nullptr,
                bool is_expert   = false)
      : OptionInfo(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value),
        d_min(min),
        d_max(max)
  {
  }
  OptionNumeric() = delete;

  bool is_numeric() const override { return true; }

  /**
   * Get the current value of a numeric option.
   * @return The current value of a numeric option.
   */
  uint64_t operator()() const { return d_value; }
  /**
   * Set the current value of a numeric option.
   * @param value The current value.
   */
  void set(uint64_t value) { d_value = value; }

 private:
  /** The current value. */
  uint64_t d_value;
  /** The default value. */
  uint64_t d_default;
  /** The minimum value. */
  uint64_t d_min;
  /** The maximum value. */
  uint64_t d_max;
};

/** Option info data for options that take enum values. */
template <typename T>
class OptionEnum : public OptionInfo
{
  using String2EnumMap = std::unordered_map<std::string, T>;
  using Enum2StringMap = std::unordered_map<T, std::string>;

 public:
  /**
   * Constructor.
   *
   * @note On construction, given uint64_t value determines the initial and the
   *       default enum value of the option.
   *
   * @param options     The associated options object.
   * @param opt         The corresponding option.
   * @param value       The initial and default value of the option.
   * @param enum2string A map from option enum value to its string
   *                    representation for the CLI.
   * @param desc        The option description (used for the CLI help message).
   * @param lng         The long name of the option (`--<lng>` in the CLI).
   * @param shrt        The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert   True if this is an expert option.
   */
  OptionEnum(Options* options,
             Option opt,
             T value,
             const Enum2StringMap& enum2string,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : OptionInfo(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_enum2string(enum2string)
  {
    for (const auto& p : enum2string)
    {
      d_string2enum.emplace(p.second, p.first);
    }
  }
  OptionEnum() = delete;

  bool is_enum() const override { return true; }
  T operator()() const { return d_value; }

 private:
  const std::string& get_option_enum() const override
  {
    return d_enum2string.at(d_value);
  }

  void set_option_enum(const std::string& value) override
  {
    d_value = d_string2enum.at(value);
  }

  /** The current enum value. */
  T d_value;
  /** The default enum value. */
  T d_default;
  /** A map from enum value to its string representation for the CLI. */
  Enum2StringMap d_enum2string;
  /** A map from string representation for the CLI to enum value. */
  String2EnumMap d_string2enum;
};

/* -------------------------------------------------------------------------- */

class Options
{
  /* Note: d_options must be initialized first since initialization of public
   *       option members depends on it */

  friend OptionInfo;

 private:
  /** The registered options. */
  std::unordered_map<Option, OptionInfo*> d_options;

 public:
  static constexpr uint64_t VERBOSITY_MAX = 4;
  static constexpr uint64_t PROB_100      = 1000;
  static constexpr uint64_t PROB_50       = 500;

  /** Constructor. */
  Options();

  // general options
  OptionBool incremental;
  OptionNumeric log_level;
  OptionEnum<SatSolver> sat_solver;
  OptionNumeric seed;
  OptionNumeric verbosity;

  OptionEnum<BvSolver> bv_solver;

  // BV: propagation-based local search engine
  OptionNumeric prop_nprops;
  OptionNumeric prop_nupdates;
  OptionEnum<PropPathSelection> prop_path_sel;
  OptionNumeric prop_prob_pick_inv_value;
  OptionNumeric prop_prob_pick_random_input;
  OptionBool prop_const_bits;
  OptionBool prop_ineq_bounds;
  OptionBool prop_opt_lt_concat_sext;
  OptionBool prop_sext;

  /**
   * Set current value of Boolean option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param value The value.
   */
  void set_option_bool(Option opt, bool value);
  /**
   * Set current value of numeric option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param value The value.
   */
  void set_option_numeric(Option opt, uint64_t value);
  /**
   * Set current value of enum option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param value The string representation of the enum value.
   */
  void set_option_enum(Option opt, const std::string& value);

  /**
   * Get the current value of a Boolean option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param opt The option.
   * @return The current value of a Boolean option.
   */
  bool get_option_bool(Option opt) const;
  /**
   * Get the current value of a numeric option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param opt The option.
   * @return The current value of a numeric option.
   */
  uint64_t get_option_numeric(Option opt) const;
  /**
   * Get the string representation of the current value of an enum options.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param opt The option.
   * @return The current value of an enum option.
   */
  const std::string& get_option_enum(Option opt) const;

 private:
  /**
   * Register option.
   * @note This is mainly necessary to have access to options via their enum
   *       identifier from external (the API).
   * @param opt  The option.
   * @param info The associated option info data.
   */
  void register_option(Option opt, OptionInfo* info) { d_options[opt] = info; }
};

/* -------------------------------------------------------------------------- */
}  // namespace bzla::option

#endif
