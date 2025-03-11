/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_OPTION_OPTION_H_INCLUDED
#define BZLA_OPTION_OPTION_H_INCLUDED

#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

namespace bzla::option {

/* -------------------------------------------------------------------------- */

enum class Option
{
  LOG_LEVEL,                  // numeric
  PRODUCE_MODELS,             // bool
  PRODUCE_UNSAT_ASSUMPTIONS,  // bool
  PRODUCE_UNSAT_CORES,        // bool
  SEED,                       // numeric
  VERBOSITY,                  // numeric
  TIME_LIMIT_PER,             // numeric
  MEMORY_LIMIT,               // numeric
  NTHREADS,                   // numeric

  BV_SOLVER,      // enum
  REWRITE_LEVEL,  // numeric
  SAT_SOLVER,     // enum

  WRITE_AIGER,  // str
  WRITE_CNF,    // str

  PROP_NPROPS,                  // numeric
  PROP_NUPDATES,                // numeric
  PROP_PATH_SEL,                // enum
  PROP_PROB_PICK_INV_VALUE,     // numeric
  PROP_PROB_PICK_RANDOM_INPUT,  // numeric
  PROP_CONST_BITS,              // bool
  PROP_INEQ_BOUNDS,             // bool
  PROP_OPT_LT_CONCAT_SEXT,      // bool
  PROP_SEXT,                    // bool

  // Abstraction module
  ABSTRACTION,                 // bool
  ABSTRACTION_BV_SIZE,         // numeric
  ABSTRACTION_EAGER_REFINE,    // bool
  ABSTRACTION_VALUE_LIMIT,     // numeric
  ABSTRACTION_VALUE_ONLY,      // bool
  ABSTRACTION_ASSERT,          // bool
  ABSTRACTION_ASSERT_REFS,     // bool
  ABSTRACTION_INITIAL_LEMMAS,  // bool
  ABSTRACTION_INC_BITBLAST,    // bool
  ABSTRACTION_BV_ADD,          // bool
  ABSTRACTION_BV_MUL,          // bool
  ABSTRACTION_BV_UDIV,         // bool
  ABSTRACTION_BV_UREM,         // bool
  ABSTRACTION_EQUAL,           // bool
  ABSTRACTION_ITE,             // bool

  // Preprocessing options for enabling/disabling passes
  PREPROCESS,             // bool
  PP_CONTRADICTING_ANDS,  // bool
  PP_ELIM_BV_EXTRACTS,    // bool
  PP_ELIM_BV_UDIV,        // bool
  PP_EMBEDDED_CONSTR,     // bool
  PP_FLATTEN_AND,         // bool
  PP_NORMALIZE,           // bool
  PP_SKELETON_PREPROC,    // bool
  PP_VARIABLE_SUBST,      // bool
  PP_OPT_END,

  // Preprocessing pass options for configuring passes
  PP_VARIABLE_SUBST_NORM_BV_INEQ,  // bool
  PP_VARIABLE_SUBST_NORM_EQ,       // bool
  PP_VARIABLE_SUBST_NORM_DISEQ,    // bool

  DBG_RW_NODE_THRESH,    // numeric
  DBG_PP_NODE_THRESH,    // numeric
  DBG_CHECK_MODEL,       // bool
  DBG_CHECK_UNSAT_CORE,  // bool

  NUM_OPTIONS,
};

// Overload increment operator for option enums.
Option operator++(Option& o);

/* -------------------------------------------------------------------------- */

enum class BvNumberFormat
{
  BIN,
  DEC,
  HEX,
};

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
};

enum class PropPathSelection
{
  ESSENTIAL,
  RANDOM,
};

/* -------------------------------------------------------------------------- */

class Options;

/** The base class for option info data. */
class OptionBase
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
  OptionBase(Options* options,
             Option opt,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false);
  OptionBase() = delete;
  virtual ~OptionBase();

  /** @return True if this option is a Boolean option. */
  virtual bool is_bool() { return false; }
  /** @return True if this option is a numeric option. */
  virtual bool is_numeric() { return false; }
  /** @return True if this option is a numeric option that allows increments. */
  virtual bool is_numeric_inc() { return false; }
  /**
   * @return True if this option is an option that takes a mode (an enum value).
   */
  virtual bool is_mode() { return false; }
  /** @return True if this option is a string option. */
  virtual bool is_str() { return false; }

  /** @return The description of this option. */
  const char* description() const { return d_description; }
  /** @return The long name of this option. */
  const char* lng() const { return d_long; }
  /** @return The short name of this option. */
  const char* shrt() const { return d_short; }

  /** @return True if this option was set from outside. */
  bool is_user_set() const { return d_is_user_set; }

 protected:
  /** The option description. */
  const char* d_description;
  /** The long name of the option (`--<lng>` in the CLI). */
  const char* d_long;
  /** The short name of the option (`-<shrt>` in the CLI). */
  const char* d_short;
  /** True if this is an expert option. */
  bool d_is_expert;
  /** True if this option was configured from outside. */
  bool d_is_user_set;
};

/** Option info data for Boolean options. */
class OptionBool : public OptionBase
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
      : OptionBase(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value)
  {
  }
  OptionBool() = delete;

  bool is_bool() override { return true; }

  /**
   * Set the current value of a Boolean option.
   * @param value       The current value.
   * @param is_user_set True if this option was configured from outside.
   */
  void set(bool value, bool is_user_set = false)
  {
    d_value       = value;
    d_is_user_set = is_user_set;
  }

  /**
   * Get the current value of a Boolean option.
   * @return The current value of a Boolean option.
   */
  const bool& operator()() const { return d_value; }

  /** @return The default value of this option. */
  const bool& dflt() const { return d_default; }

 private:
  /** The current value. */
  bool d_value;
  /** The default value. */
  bool d_default;
};

/** Option info data for numeric options. */
class OptionNumeric : public OptionBase
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
                bool is_expert   = false,
                bool allow_inc   = false)
      : OptionBase(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value),
        d_min(min),
        d_max(max),
        d_allow_inc(allow_inc)
  {
  }
  OptionNumeric() = delete;

  bool is_numeric() override { return true; }

  bool is_numeric_inc() override { return d_allow_inc; }

  /**
   * Set the current value of a numeric option.
   * @param value       The current value.
   * @param is_user_set True if this option was configured from outside.
   */
  void set(uint64_t value, bool is_user_set = false)
  {
    d_value       = value;
    d_is_user_set = is_user_set;
  }

  /**
   * Get the current value of a numeric option.
   * @return The current value of a numeric option.
   */
  const uint64_t& operator()() const { return d_value; }

  /** @return The default value of this option. */
  const uint64_t& dflt() const { return d_default; }
  /** @return The minimum value of this option. */
  const uint64_t& min() const { return d_min; }
  /** @return The maximum value of this option. */
  const uint64_t& max() const { return d_max; }

 private:
  /** The current value. */
  uint64_t d_value;
  /** The default value. */
  uint64_t d_default;
  /** The minimum value. */
  uint64_t d_min;
  /** The maximum value. */
  uint64_t d_max;
  /** Allow no value to increment option. */
  bool d_allow_inc;
};

/**
 * Base class for option info data for options that have modes (take enum
 * values).
 */
class OptionMode : public OptionBase
{
 public:
  OptionMode(Options* options,
             Option opt,
             const char* desc,
             const char* lng,
             const char* shrt = nullptr,
             bool is_expert   = false)
      : OptionBase(options, opt, desc, lng, shrt, is_expert)
  {
  }

  OptionMode() = delete;

  bool is_mode() override { return true; }

  /**
   * Set current mode.
   * @param value The string representation of the mode value.
   * @param is_user_set True if this option was configured from outside.
   */
  virtual void set_str(const std::string& value, bool is_user_set = false) = 0;
  /**
   * Get the string representation of the current value of a option with modes.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @return The current value of an option that has modes.
   */
  virtual const std::string& get_str() const = 0;
  /**
   * Get the string representation of the default value of an option with modes.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @return The default value of an option that has modes.
   */
  virtual const std::string& dflt_str() const = 0;
  /**
   * Determine if the given string is a valid mode for an option with modes.
   * @param value The mode.
   * @return True if it is valid.
   */
  virtual bool is_valid(const std::string& value) const = 0;
  /** @return A vector of string representations of available modes. */
  virtual std::vector<std::string> modes() const = 0;
};

/** Option info data for options that have modes (take enum values). */
template <typename T>
class OptionModeT : public OptionMode
{
  using String2ModeMap = std::unordered_map<std::string, T>;
  using Mode2StringMap = std::unordered_map<T, std::string>;

 public:
  /**
   * Constructor.
   *
   * @note On construction, given uint64_t value determines the initial and the
   *       default mode (enum value) of the option.
   *
   * @param options     The associated options object.
   * @param opt         The corresponding option.
   * @param value       The initial and default value of the option.
   * @param mode2string A map from option mode value to its string
   *                    representation for the CLI.
   * @param desc        The option description (used for the CLI help message).
   * @param lng         The long name of the option (`--<lng>` in the CLI).
   * @param shrt        The short name of the option (`-<shrt>` in the CLI).
   * @param is_expert   True if this is an expert option.
   */
  OptionModeT(Options* options,
              Option opt,
              T value,
              const Mode2StringMap& mode2string,
              const char* desc,
              const char* lng,
              const char* shrt = nullptr,
              bool is_expert   = false)
      : OptionMode(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value),
        d_mode2string(mode2string)
  {
    for (const auto& p : mode2string)
    {
      d_string2mode.emplace(p.second, p.first);
    }
  }
  OptionModeT() = delete;

  const T& operator()() const { return d_value; }

  /** @return The default value of this option. */
  const T& dflt() const { return d_default; }

  std::string mode_to_string(T mode) { return d_mode2string.at(mode); }

 private:
  std::vector<std::string> modes() const override;
  const std::string& get_str() const override;
  void set_str(const std::string& value, bool is_user_set = false) override;
  const std::string& dflt_str() const override;
  bool is_valid(const std::string& value) const override;

  /** The current mode. */
  T d_value;
  /** The default mode. */
  T d_default;
  /** A map from mode to its string representation for the CLI. */
  Mode2StringMap d_mode2string;
  /** A map from string representation for the CLI to mode. */
  String2ModeMap d_string2mode;
};

class OptionStr : public OptionBase
{
 public:
  /**
   * Constructor.
   *
   * @note On construction, given string value determines the initial and the
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
  OptionStr(Options* options,
            Option opt,
            const std::string& value,
            const char* desc,
            const char* lng,
            const char* shrt = nullptr,
            bool is_expert   = false)
      : OptionBase(options, opt, desc, lng, shrt, is_expert),
        d_value(value),
        d_default(value)
  {
  }
  OptionStr() = delete;

  bool is_str() override { return true; }

  /**
   * Set the current value of a string option.
   * @param value       The current value.
   * @param is_user_set True if this option was configured from outside.
   */
  void set(const std::string& value, bool is_user_set = false)
  {
    d_value       = value;
    d_is_user_set = is_user_set;
  }

  /**
   * Get the current value of a string option.
   * @return The current value of a string option.
   */
  const std::string& operator()() const { return d_value; }

  /** @return The default value of this option. */
  const std::string& dflt() const { return d_default; }

 private:
  /** The current value. */
  std::string d_value;
  /** The default value. */
  std::string d_default;
};

/* -------------------------------------------------------------------------- */

class Options
{
  // Note: d_name2option must be initialized first since initialization of
  //       public option members depends on it

  friend OptionBase;

 private:
  /** Map short and long option name to option. */
  std::unordered_map<std::string, Option> d_name2option;

 public:
  static constexpr uint8_t VERBOSITY_MAX = 4;
  static constexpr uint64_t PROB_100     = 1000;
  static constexpr uint64_t PROB_50      = 500;

  /** Constructor. */
  Options();

  // general options
  OptionNumeric log_level;
  OptionBool produce_models;
  OptionBool produce_unsat_assumptions;
  OptionBool produce_unsat_cores;
  OptionNumeric seed;
  OptionNumeric verbosity;
  OptionNumeric time_limit_per;
  OptionNumeric memory_limit;
  OptionNumeric nthreads;

  // Bitwuzla-specific options
  OptionModeT<BvSolver> bv_solver;
  OptionModeT<SatSolver> sat_solver;
  OptionStr write_aiger;
  OptionStr write_cnf;
  OptionNumeric rewrite_level;

  // BV: propagation-based local search engine
  OptionNumeric prop_nprops;
  OptionNumeric prop_nupdates;
  OptionModeT<PropPathSelection> prop_path_sel;
  OptionNumeric prop_prob_pick_inv_value;
  OptionNumeric prop_prob_pick_random_input;
  OptionBool prop_const_bits;
  OptionBool prop_ineq_bounds;
  OptionBool prop_opt_lt_concat_sext;
  OptionBool prop_sext;

  OptionBool abstraction;
  OptionNumeric abstraction_bv_size;
  OptionBool abstraction_eager_refine;
  OptionNumeric abstraction_value_limit;
  OptionBool abstraction_value_only;
  OptionBool abstraction_assert;
  OptionNumeric abstraction_assert_refs;
  OptionBool abstraction_initial_lemmas;
  OptionBool abstraction_inc_bitblast;
  OptionBool abstraction_bv_add;
  OptionBool abstraction_bv_mul;
  OptionBool abstraction_bv_udiv;
  OptionBool abstraction_bv_urem;
  OptionBool abstraction_eq;
  OptionBool abstraction_ite;

  // Preprocessing
  OptionBool preprocess;
  OptionBool pp_contr_ands;
  OptionBool pp_elim_bv_extracts;
  OptionBool pp_elim_bv_udiv;
  OptionBool pp_embedded_constr;
  OptionBool pp_flatten_and;
  OptionBool pp_normalize;
  OptionBool pp_skeleton_preproc;
  OptionBool pp_variable_subst;
  OptionBool pp_variable_subst_norm_eq;
  OptionBool pp_variable_subst_norm_diseq;
  OptionBool pp_variable_subst_norm_bv_ineq;

  // Debug options
  OptionNumeric dbg_rw_node_thresh;
  OptionNumeric dbg_pp_node_thresh;
  OptionBool dbg_check_model;
  OptionBool dbg_check_unsat_core;

  /** @return True if the given option is a Boolean option. */
  bool is_bool(Option opt);
  /** @return True if the given option is a numeric option. */
  bool is_numeric(Option opt);
  /** @return True if the given option is a numeric option that allows
   * increments. */
  bool is_numeric_inc(Option opt);
  /** @return True if the given option is an option with modes. */
  bool is_mode(Option opt);
  /** @return True if the given option is a string option. */
  bool is_str(Option opt);

  /** @return True if given string is a valid short or long option name. */
  bool is_valid(const std::string& name) const;

  /**
   * @return True if the given value is a valid mode for an option with modes.
   */
  bool is_valid_mode(Option opt, const std::string& value);

  /** @return The description of the given option. */
  const char* description(Option opt);
  /** @return The long name of the given option. */
  const char* lng(Option opt);
  /** @return The short name of the given option. */
  const char* shrt(Option opt);

  /**
   * @return The string representations of all valid modes for an option with
   *         modes.
   */
  std::vector<std::string> modes(Option opt);

  /** @return Option associated with the given long option name. */
  Option option(const std::string& name) const;
  Option option(const char* name) const;

  /**
   * Set current value of option.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @param opt         The option to set.
   * @param value       The value to set.
   * @param is_user_set True if this option was configured from outside.
   */
  template <typename T>
  void set(Option opt, const T& value, bool is_user_set = false);

  /**
   * Set current value of option, configured via the long option name and
   * its value in string representation.
   * @note This is mainly necessary for easy configuration of options via
   *       the command line in main.
   * @param lng         The long name of the option to set.
   * @param value       The string representation of the value to set.
   * @param is_user_set True if this option was configured from outside.
   */
  void set(const std::string& lng,
           const std::string& value,
           bool is_user_set = false);

  /**
   * Get the current value of option.
   * @param opt The option to query.
   * @note This is mainly necessary to have access to options via their mod
   *       identifier from external (the API).
   * @return The current value.
   */
  template <typename T>
  const T& get(Option opt);

  /**
   * Get the minimum value of option.
   * @param opt The option to query.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @return The minimum value.
   */
  template <typename T>
  const T& min(Option opt);

  /**
   * Get the maximum value of option.
   * @param opt The option to query.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @return The maximum value.
   */
  template <typename T>
  const T& max(Option opt);

  /**
   * Get the maximum value of option.
   * @param opt The option to query.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @return The maximum value.
   */
  template <typename T>
  const T& dflt(Option opt);

  /**
   * Finalize options, this enables/disables options depending on the currently
   * configured options.
   */
  void finalize();

 private:
  /**
   * Get pointer to option data.
   * @note This is mainly necessary to have access to options via their mode
   *       identifier from external (the API).
   * @param opt  The option.
   * @return The associated option data.
   */
  OptionBase* data(Option opt);
};

// explicit instantiations
template <>
void Options::set(Option opt, const bool& value, bool is_user_set);
template <>
void Options::set(Option opt, const uint64_t& value, bool is_user_set);
template <>
void Options::set(Option opt, const std::string& value, bool is_user_set);

template <>
const bool& Options::get(Option opt);
template <>
const uint64_t& Options::get(Option opt);
template <>
const std::string& Options::get(Option opt);

template <>
const bool& Options::dflt(Option opt);
template <>
const uint64_t& Options::dflt(Option opt);
template <>
const std::string& Options::dflt(Option opt);

template <>
const uint64_t& Options::min(Option opt);
template <>
const uint64_t& Options::max(Option opt);

/* -------------------------------------------------------------------------- */

/**
 * The exception thrown incompatible options result in an unrecoverable error,
 * e.g., when the selected SAT solver is not compiled in.
 */
class Exception : public std::exception
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  Exception(const std::string& msg) : d_msg(msg) {}
  /**
   * Get the exception message.
   * @return The exception message.
   */
  const std::string& msg() const { return d_msg; }

  const char* what() const noexcept override { return d_msg.c_str(); }

 private:
  /** The exception message. */
  std::string d_msg;
};
}  // namespace bzla::option

#endif
