#ifndef BZLA_OPTION_OPTION_H_INCLUDED
#define BZLA_OPTION_OPTION_H_INCLUDED

#include <cstddef>
#include <cstdint>
#include <memory>
#include <unordered_map>
#include <variant>
#include <vector>

namespace bzla::options {

/* -------------------------------------------------------------------------- */

enum class Option
{
  SAT_SOLVER,   // enum
  INCREMENTAL,  // bool
  LOG_LEVEL,    // numeric

  NUM_OPTIONS
};

/* -------------------------------------------------------------------------- */

enum SatSolver
{
  CADICAL,
  CRYPTOMINISAT,
  KISSAT,
  LINGELING,
};

/* -------------------------------------------------------------------------- */

class OptionInfo
{
 public:
  using String2EnumMap = std::unordered_map<const char*, uint64_t>;
  using Enum2StringMap = std::unordered_map<uint64_t, const char*>;

  /** The value data for Boolean options. */
  struct Boolean
  {
    /**
     * Constructor.
     *
     * On construction, given Boolean value determines the initial and the
     * default value of the option.
     *
     * @param val The boolean initial and default value of the option.
     */
    Boolean(bool val) : d_value(val), d_default(val) {}
    /** The current value of a Boolean option. */
    bool d_value;
    /** The default value of a Boolean option. */
    bool d_default;
  };

  /** The value data of options with enum values. */
  struct Enum
  {
    /**
     * Constructor.
     *
     * On construction, given uint64_t value determines the initial and the
     * default enum value of the option.
     *
     * @param val         The initial and default value of the option.
     * @param enum2string A map from option enum value to its string
     *                    representation for the CLI.
     */
    Enum(uint64_t val, const Enum2StringMap& enum2string);
    /** The current enum value of this option. */
    uint64_t d_value;
    /** The default enum value of this option. */
    uint64_t d_default;
    /** A map from enum value to its string representation for the CLI. */
    Enum2StringMap d_enum2string;
    /** A map from string representation for the CLI to enum value. */
    String2EnumMap d_string2enum;
  };

  /** The value data of options with numeric values. */
  struct Numeric
  {
    /**
     * Constructor.
     *
     * On construction, given uint64_t value determines the initial and the
     * default integer value of a numeric option.
     *
     * @param val The initial and default value of a numeric option, must be
     *            `>= min` and `<= max`.
     * @param min The minimum value of the option.
     * @param max The maximum value of the option.
     */
    Numeric(uint64_t val, uint64_t min, uint64_t max)
        : d_value(val), d_default(val), d_min(min), d_max(max)
    {
    }
    /** The current value of a numeric options. */
    uint64_t d_value;
    /** The default value of a numeric option. */
    uint64_t d_default;
    /** The minimum value of a numeric option. */
    uint64_t d_min;
    /** The maximum value of a numeric option. */
    uint64_t d_max;
  };

  /**
   * Constructor for Boolean options.
   * @param value     The initial and default value of the option.
   * @param desc      The option description (used for CLI help message).
   * @param lng       The long name of the option (`--<lng>` for the CLI).
   * @param shrt      The short name of the option (`-<shrt>` for the CLI).
   * @param is_expert True if this is an expert option.
   */
  OptionInfo(bool value,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : d_value(Boolean(value)),
        d_description(desc),
        d_long(lng),
        d_short(shrt),
        d_is_expert(is_expert)
  {
  }
  /**
   * Constructor for options that take enum values.
   * @param value       The initial and default value of the option.
   * @param enum2string A map from option enum value to its string
   *                    representation for the CLI.
   * @param desc        The option description (used for the CLI help message).
   * @param lng         The long name of the option (`--<lng>` in the CLI).
   * @param shrt        The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert   True if this is an expert option.
   */
  OptionInfo(uint64_t value,
             const Enum2StringMap& enum2string,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : d_value(Enum(value, enum2string)),
        d_description(desc),
        d_long(lng),
        d_short(shrt),
        d_is_expert(is_expert)
  {
  }
  /**
   * Constructor for numeric options.
   * @param value     The initial and default value of the option.
   * @param min       The minimum value of the option.
   * @param max       The maximum value of the option.
   * @param desc      The option description (used for the CLI help message).
   * @param lng       The long name of the option (`--<lng>` in the CLI).
   * @param shrt      The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert True if this is an expert option.
   */
  OptionInfo(uint64_t value,
             uint64_t min,
             uint64_t max,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : d_value(Numeric(value, min, max)),
        d_description(desc),
        d_long(lng),
        d_short(shrt),
        d_is_expert(is_expert)
  {
  }
  /** Default constructor. */
  OptionInfo() {}

  /** The option value data. */
  std::variant<std::monostate, Boolean, Enum, Numeric> d_value;
  /** The option description. */
  const char* d_description;
  /** The long name of the option (`--<lng>` in the CLI). */
  const char* d_long;
  /** The short name of the option (`-<shrt>` in the CLI). */
  const char* d_short;
  /** True if this is an expert option. */
  bool d_is_expert;
};

/* -------------------------------------------------------------------------- */

class Options
{
 public:
  /** Constructor. */
  Options();

  /**
   * Initialize and add Boolean option.
   *
   * @param name      The option to add.
   * @param option    The member that serves as a short cut to the current
   *                  value of the option.
   * @param value     The initial and default value of the option.
   * @param desc      The option description (used for CLI help message).
   * @param lng       The long name of the option (`--<lng>` for the CLI).
   * @param shrt      The short name of the option (`-<shrt>` for the CLI).
   * @param is_expert True if this is an expert option.
   */
  void init(Option name,
            bool& option,
            bool value,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr,
            bool is_expert   = false);

  /**
   * Initialize and add option that takes enum values.
   *
   * @param name      The option to add.
   * @param option    The member that serves as a short cut to the current
   *                  value of the option.
   * @param value       The initial and default value of the option.
   * @param enum2string A map from option enum value to its string
   *                    representation for the CLI.
   * @param desc        The option description (used for the CLI help message).
   * @param lng         The long name of the option (`--<lng>` in the CLI).
   * @param shrt        The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert   True if this is an expert option.
   */
  template <typename T>
  void init(Option name,
            T& option,
            T value,
            const OptionInfo::Enum2StringMap& enum2string,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr,
            bool is_expert   = false);

  /**
   * Initialize and add numeric option.
   *
   * @param name      The option to add.
   * @param option    The member that serves as a short cut to the current
   *                  value of the option.
   * @param value     The initial and default value of the option.
   * @param min       The minimum value of the option.
   * @param max       The maximum value of the option.
   * @param desc      The option description (used for the CLI help message).
   * @param lng       The long name of the option (`--<lng>` in the CLI).
   * @param shrt      The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert True if this is an expert option.
   */
  void init(Option name,
            uint64_t& option,
            uint64_t value,
            uint64_t min,
            uint64_t max,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr,
            bool is_expert   = false);

  /** @return current value data of given option. */
  template <typename T>
  const T& operator[](Option opt) const
  {
    return std::get<T>(d_options[static_cast<size_t>(opt)].d_value);
  }

  /** @return The current value of Boolean option `opt`. */
  bool get_option_bool(Option opt) const
  {
    return this->operator[]<OptionInfo::Boolean>(opt).d_value;
  }

  /* Short cuts to default values of options. ----------------------- */
  /** Option::INCREMENTAL */
  bool incremental;
  /** Option::LOG_LEVEL */
  uint64_t log_level;
  /** Option::SAT_SOLVER */
  SatSolver sat_solver;

 private:
  /** The number of added and initialized options. */
  size_t d_num_initialized = 0;
  /** The options. */
  std::vector<OptionInfo> d_options;
};

/* -------------------------------------------------------------------------- */
}  // namespace bzla::options

#endif
