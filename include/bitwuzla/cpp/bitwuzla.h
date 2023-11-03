/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_CPP_H_INCLUDED
#define BITWUZLA_API_CPP_H_INCLUDED

#include <bitwuzla/enums.h>
#include <bitwuzla/option.h>

#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <variant>
#include <vector>

// TODO mark functions that may change in the future as experimental for release

/* -------------------------------------------------------------------------- */

namespace bzla {
class Node;
class Type;
class SolvingContext;
class Terminator;
namespace option {
class Options;
}
}  // namespace bzla

namespace bitwuzla {
class Term;
class Sort;
}  // namespace bitwuzla

/* -------------------------------------------------------------------------- */

namespace std {

template <>
struct hash<bitwuzla::Sort>
{
  /**
   * Hash function for Sort.
   * @param sort The sort.
   * @return The hash value of the sort.
   */
  size_t operator()(const bitwuzla::Sort &sort) const;
};

template <>
struct hash<bitwuzla::Term>
{
  /**
   * Hash function for Term.
   * @param term The term.
   * @return The hash value of the term.
   */
  size_t operator()(const bitwuzla::Term &term) const;
};

}  // namespace std

/* -------------------------------------------------------------------------- */

namespace bitwuzla {

/* -------------------------------------------------------------------------- */
/* Library info                                                               */
/* -------------------------------------------------------------------------- */

/** \addtogroup cpp_libinfo
 *  @{
 */

/**
 * Get copyright information.
 * @return A string with the copyright information.
 */
const char* copyright();
/**
 * Get version information.
 * @return A string with the version information.
 */
const char* version();
/**
 * Get git information.
 * @return A string with the git information.
 */
const char* git_id();

/** @} */

/* -------------------------------------------------------------------------- */
/* Exception                                                                  */
/* -------------------------------------------------------------------------- */

class Exception : public std::exception
{
 public:
  /**
   * Constructor.
   * @param msg The exception message.
   */
  Exception(const std::string &msg);
  /**
   * Constructor.
   * @param stream The exception message given as a std::stringstream.
   */
  Exception(const std::stringstream &stream);
  /**
   * Get the exception message.
   * @return The exception message.
   */
  const std::string &msg() const;

  const char *what() const noexcept override;

 protected:
  /** The exception message. */
  std::string d_msg;
};

/* -------------------------------------------------------------------------- */
/* Output stream configuration.                                               */
/* -------------------------------------------------------------------------- */

/** Struct to configure bit-vector number format via stream manipulator. */
struct set_bv_format
{
  /**
   * Constructor.
   * @param format The number format: `2` for binary, `10` for decimal and
   *               `16` for hexadecimal.
   */
  set_bv_format(uint8_t format);
  /** @return The configured format. */
  uint8_t format() const { return d_format; }

 private:
  /** The configured number format. */
  uint8_t d_format;
};

/**
 * Configure output stream with bit-vector number format.
 * @note When printing floating-point values, configuring the bit-vector
 *       output format to hexadecimal number format will be ignored and
 *       defaulted to binary. Floating-point values are printed via operator
 *       `fp` and hexadecimal format would require mixing binary and hexadecimal
 *       format as hexadecimal format requires that the size of the bit-vector
 *       is divisible by 4.
 * @param out The output stream.
 * @param f   The bit-vector format.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &ostream, const set_bv_format &f);

/* -------------------------------------------------------------------------- */
/* Options                                                                    */
/* -------------------------------------------------------------------------- */

// Note: enum class Option is declared in api/option.h

class Bitwuzla;
struct OptionInfo;

class Options
{
  friend Bitwuzla;
  friend OptionInfo;

 public:
  /** Constructor. */
  Options();
  /** Destructor. */
  ~Options();
  /** Copy constructor. */
  Options(const Options &options);
  /** Copy assignment. */
  Options &operator=(const Options &options);
  /**
   * Determine if given string is a valid short or long option name.
   * @param name The name.
   * @return True if given string is a option name.
   */
  bool is_valid(const std::string &name) const;
  /**
   * Determine if given option is a Boolean option.
   * @param option The option to query.
   * @return True if `option` is a Boolean option.
   */
  bool is_bool(Option option) const;
  /**
   * Determine if given option is a numeric option.
   * @param option The option to query.
   * @return True if `option` is a numeric option.
   */
  bool is_numeric(Option option) const;
  /**
   * Determine if given option is an option with a mode.
   * @param option The option to query.
   * @return True if `option` is an option with a mode.
   */
  bool is_mode(Option option) const;

  /** @return The short name of this option. */
  const char *shrt(Option option) const;
  /** @return The long name of this option. */
  const char *lng(Option option) const;
  /** @return The description of this option. */
  const char *description(Option option) const;

  /** @return The modes of this option. */
  std::vector<std::string> modes(Option option) const;

  /** @return The option associated to the given short or long option name. */
  Option option(const char *name) const;

  /**
   * Set Boolean or numeric option.
   *
   * @param option The option.
   * @param value The option value.
   */
  void set(Option option, uint64_t value);
  /**
   * Set option value for options with different modes.
   *
   * @param option The option.
   * @param mode The option mode.
   */
  void set(Option option, const std::string &mode);
  /**
   * Set option value for options with different modes.
   *
   * @param option The option.
   * @param mode The option mode.
   */
  void set(Option option, const char *mode);
  /**
   * Set current value of option, configured via the long option name and
   * its value in string representation.
   * @param lng The long name of the option to set.
   * @param value The string representation of the value to set.
   */
  void set(const std::string &lng, const std::string &value);

  /**
   * Set options via command line arguments.
   *
   * Supports the following command line option format:
   *  Short option names:
   *    -short      ... {"-short"}
   *    -short=val  ... {"-short=val"}
   *    -short val  ... {"-short", "val"}
   *
   *  Long option names:
   *    --long      ... {"--long"}
   *    --long=val  ... {"--long=val"}
   *    --long val  ... {"--long", "val"}
   *
   * @param args List of command line options.
   */
  void set(const std::vector<std::string> &args);

  /**
   * Get the current value of a Boolean or numeric option.
   *
   * @param option The option.
   * @return The option value.
   */
  uint64_t get(Option option) const;
  /**
   * Get the current value of an option with modes.
   *
   * @param option The option.
   * @return The option value.
   */
  const std::string &get_mode(Option option) const;

 private:
  /** The wrapped internal options. */
  std::unique_ptr<bzla::option::Options> d_options;
};

/**
 * The struct holding all information about an option.
 */
struct OptionInfo
{
  /** The kind of the associated option. */
  enum class Kind
  {
    BOOL,
    NUMERIC,
    MODE,
  };

  /** The option value data of a Boolean option. */
  struct Bool
  {
    /** Current Boolean option value. */
    bool cur;
    /** Default Boolean option value. */
    bool dflt;
  };
  /** The option value data of a numeric option. */
  struct Numeric
  {
    /** Current numeric option value. */
    uint64_t cur;
    /** Default numeric option value. */
    uint64_t dflt;
    /** Minimum numeric option value. */
    uint64_t min;
    /** Maximum numeric option value. */
    uint64_t max;
  };
  /** The option value data of an option with modes. */
  struct Mode
  {
    /** Current mode option value. */
    std::string cur;
    /** Default mode option value. */
    std::string dflt;
    /** List of available modes. */
    std::vector<std::string> modes;
  };

  /**
   * Constructor.
   * @param options The option configuration to query for the given option.
   * @param option The option to query.
   */
  OptionInfo(const Options &options, Option option);
  /** Default constructor. */
  OptionInfo() {}
  /** Destructor. */
  ~OptionInfo() {}

  /** The associated option. */
  Option opt;
  /** The kind of the option. */
  Kind kind;
  /** Short option name. */
  const char *shrt;
  /** Long option name. */
  const char *lng;
  /** Option description. */
  const char *description;

  /** The values. */
  std::variant<Bool, Numeric, Mode> values;

  /**
   * Additionall getter for values.
   * @note This is mainly needed for Cython.
   * @return The value wrapper of this option info.
   */
  template <class T>
  T value() const;
};

/**
 * Get Bool option info wrapper.
 * @return The option info wrapper.
 */
template <>
OptionInfo::Bool OptionInfo::value() const;

/**
 * Get Numeric option info wrapper.
 * @return The option info wrapper.
 */
template <>
OptionInfo::Numeric OptionInfo::value() const;

/**
 * Get Mode option info wrapper.
 * @return The option info wrapper.
 */
template <>
OptionInfo::Mode OptionInfo::value() const;

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

// Note: enum class Result is declared in api/enums.h

/**
 * Print result to output stream.
 * @param out The output stream.
 * @param result The result.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, Result result);

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

// Note: enum class Kind is declared in api/enums.h

/**
 * Print kind to output stream.
 * @param out The output stream.
 * @param kind The kind.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, Kind kind);

/* -------------------------------------------------------------------------- */
/* RoundingMode                                                               */
/* -------------------------------------------------------------------------- */

// Note: enum class RoundingMode is declared in api/enums.h

/**
 * Print rounding mode to output stream.
 * @param out The output stream.
 * @param rm The rounding mode.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, RoundingMode rm);

/* -------------------------------------------------------------------------- */
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

class Sort;

class Term
{
  friend Bitwuzla;
  friend bool operator==(const Term &, const Term &);
  friend bool operator!=(const Term &, const Term &);
  friend std::ostream &operator<<(std::ostream &, const Term &);
  friend std::hash<bitwuzla::Term>;
  friend Term mk_true();
  friend Term mk_false();
  friend Term mk_bv_zero(const Sort &);
  friend Term mk_bv_one(const Sort &);
  friend Term mk_bv_ones(const Sort &);
  friend Term mk_bv_min_signed(const Sort &);
  friend Term mk_bv_max_signed(const Sort &);
  friend Term mk_bv_value(const Sort &, const std::string &, uint8_t);
  friend Term mk_bv_value_uint64(const Sort &, uint64_t);
  friend Term mk_bv_value_int64(const Sort &, int64_t);
  friend Term mk_fp_pos_zero(const Sort &);
  friend Term mk_fp_neg_zero(const Sort &);
  friend Term mk_fp_pos_inf(const Sort &);
  friend Term mk_fp_neg_inf(const Sort &);
  friend Term mk_fp_nan(const Sort &);
  friend Term mk_fp_value(const Term &, const Term &, const Term &);
  friend Term mk_fp_value(const Sort &, const Term &, const std::string &);
  friend Term mk_fp_value(const Sort &,
                          const Term &,
                          const std::string &,
                          const std::string &);
  friend Term mk_rm_value(RoundingMode);
  friend Term mk_const_array(const Sort &, const Term &);
  friend Term mk_term(Kind,
                      const std::vector<Term> &,
                      const std::vector<uint64_t> &);
  friend Term mk_const(const Sort &, std::optional<const std::string>);
  friend Term mk_var(const Sort &, std::optional<const std::string>);
  friend Term substitute_term(const Term &,
                              const std::unordered_map<Term, Term> &);
  friend void substitute_terms(std::vector<Term> &terms,
                               const std::unordered_map<Term, Term> &);

 public:
  /** Default constructor, creates null term. */
  Term();
  /** Destructor. */
  ~Term();

  /**
   * Determine if this term is a null term.
   * @return True if this term is a null term.
   */
  bool is_null() const;

  /**
   * Get the id of this term.
   * @return The term id.
   */
  uint64_t id() const;

  /**
   * Get the kind of this term.
   * @return The kind.
   */
  Kind kind() const;

  /**
   * Get the sort of this term.
   * @return The sort of the term.
   */
  Sort sort() const;

  /**
   * Get the number of child terms of this term.
   * @return The number of children of this term.
   */
  size_t num_children() const;

  /**
   * Get the child terms of this term.
   * @return The children of this term as a vector of terms.
   */
  std::vector<Term> children() const;

  /**
   * Get child at position `index`.
   *
   * @note Only valid to call if num_children() > 0.
   *
   * @param index The position of the child.
   * @return The child node at position `index`.
   */
  Term operator[](size_t index) const;

  /**
   * Get the number of indices of this term.
   * @return The number of indices of this term.
   */
  size_t num_indices() const;

  /**
   * Get the indices of an indexed term.
   *
   * Requires that given term is an indexed term.
   *
   * @return The indices of this term as a vector of indices.
   */
  std::vector<uint64_t> indices() const;

  /**
   * Get the symbol of this term.
   * @return The symbol of this term.
   */
  std::optional<std::reference_wrapper<const std::string>> symbol() const;

#if 0
  /**
   * Set the symbol of this term.
   * @param symbol The symbol.
   */
  void set_symbol(
      std::optional<std::reference_wrapper<const std::string>> symbol);
#endif

  /**
   * Determine if this term is a constant.
   * @return True if this term is a constant.
   */
  bool is_const() const;

  /**
   * Determine if this term is a variable.
   * @return True if this term is a variable.
   */
  bool is_variable() const;

  /**
   * Determine if this term is a value.
   * @return True if this term is a value.
   */
  bool is_value() const;

  /**
   * Determine if this term is Boolean value true.
   * @return True if this term is Boolean value true.
   */
  bool is_true() const;

  /**
   * Determine if this term is Boolean value false.
   * @return True if this term is Boolean value false.
   */
  bool is_false() const;

  /**
   * Determine if this term is a bit-vector value representing zero.
   * @return True if this term is a bit-vector zero value.
   */
  bool is_bv_value_zero() const;

  /**
   * Determine if this term is a bit-vector value representing one.
   * @return True if this term is a bit-vector one value.
   */
  bool is_bv_value_one() const;

  /**
   * Determine if this term is a bit-vector value with all bits set to one.
   * @return True if this term is a bit-vector value with all bits set to one.
   */
  bool is_bv_value_ones() const;

  /**
   * Determine if this term is a bit-vector minimum signed value.
   * @return True if this term is a bit-vector value with the most significant
   *         bit set to 1 and all other bits set to 0.
   */
  bool is_bv_value_min_signed() const;

  /**
   * Determine if this term is a bit-vector maximum signed value.
   * @return True if this term is a bit-vector value with the most significant
   *         bit set to 0 and all other bits set to 1.
   */
  bool is_bv_value_max_signed() const;

  /**
   * Determine if this term is a floating-point positive zero (`+zero`) value.
   * @return True if this term is a floating-point +zero value.
   */
  bool is_fp_value_pos_zero() const;

  /**
   * Determine if this term is a floating-point value negative zero (`-zero`).
   * @return True if this term is a floating-point value negative zero.
   */
  bool is_fp_value_neg_zero() const;

  /**
   * Determine if this term is a floating-point positive infinity (`+oo`) value.
   * @return True if this term is a floating-point +oo value.
   */
  bool is_fp_value_pos_inf() const;

  /**
   * Determine if this term is a floating-point negative infinity (-oo) value.
   * @return True if this term is a floating-point -oo value.
   */
  bool is_fp_value_neg_inf() const;

  /**
   * Determine if this term is a floating-point NaN value.
   * @return True if this term is a floating-point NaN value.
   */
  bool is_fp_value_nan() const;

  /**
   * Determine if this term is a rounding mode RNA value.
   * @return True if this term is a roundindg mode RNA value.
   */
  bool is_rm_value_rna() const;

  /**
   * Determine if this term is a rounding mode RNE value.
   * @return True if this term is a rounding mode RNE value.
   */
  bool is_rm_value_rne() const;

  /**
   * Determine if this term is a rounding mode RTN value.
   * @return True if this term is a rounding mode RTN value.
   */
  bool is_rm_value_rtn() const;

  /**
   * Determine if this term is a rounding mode RTP value.
   * @return True if this term is a rounding mode RTP value.
   */
  bool is_rm_value_rtp() const;

  /**
   * Determine if this term is a rounding mode RTZ value.
   * @return True if this term is a rounding mode RTZ value.
   */
  bool is_rm_value_rtz() const;

  /**
   * Get the SMT-LIB v2 string representation of this term.
   * @note Floating-point values are represented in terms of operator `fp`.
   *       Their component bit-vector values can only be printed in binary or
   *       decimal format. If base `16` is configured, the format for
   *       floating-point component bit-vector values defaults to binary format.
   * @param base The base of the string representation of bit-vector values;
   *             `2` for binary, `10` for decimal, and `16` for hexadecimal.
   * @return A string representation of this term.
   */
  std::string str(uint8_t base = 2) const;

  /**
   * Get value from value term.
   *
   * This function is instantiated for types
   * - `bool` for Boolean values
   * - `RoundingMode` for rounding mode values
   * - `std::string` for any value
   *   (Boolean, RoundingMode, bit-vector and floating-point)
   * - `std::tuple<std::string, std::string, std::string>`
   *   for floating-point values
   *
   * In case of string representations of values (the `std::string` and
   * `std::tuple<std::string, std::string, std::string>` instantions of
   * this function), this returns the raw value string (as opposed to
   * str(), which returns the SMT-LIB v2 representation of a term).
   * For example, this function returns "010" for a bit-vector value 2 of size
   * 3, while str() returns "#b010".
   *
   * @note For the general `std::string` instantiation case, the returned
   *       string for floating-point values is always the binary IEEE-754
   *       representation of the value (parameter `base` is ignored).
   *       Parameter `base` always configures the numeric base for bit-vector
   *       values, and for floating-point values in case of the tuple of
   *       strings instantiation. It is always ignored for Boolean and
   *       RoundingMode values.
   *
   * @tparam T   The type of the value representation. `bool` for Boolean
   *             values; `RoundingMode` for rounding mode values;
   *             `std::tuple<std::string, std::string, std::string>` for
   *             floating-point values (IEEE-754 representation as strings
   *             for sign bit, exponent and significand); and, generally,
   *             `std::string` for any value type.
   * @param base The numeric base for bit-vector values; `2` for binary, `10`
   *             for decimal, and `16` for hexadecimal. Always ignored for
   *             Boolean and RoundingMode values.
   */
  template <class T>
  T value(uint8_t base = 2) const;

 private:
  /** Convert vector of terms to internal nodes. */
  static std::vector<bzla::Node> term_vector_to_nodes(
      const std::vector<Term> &terms);
  /** Convert vector of internal nodes to terms. */
  static std::vector<bitwuzla::Term> node_vector_to_terms(
      const std::vector<bzla::Node> &nodes);
  /** Constructor from internal node. */
  Term(const bzla::Node &node);
  /** The internal node wrapped by this term. */
  std::shared_ptr<bzla::Node> d_node;
};

#ifndef DOXYGEN_SKIP
/**
 * Get Boolean representation of Boolean value term.
 * @param base Ignored for this template instantiation.
 * @return Boolean representation of value term.
 */
template <>
bool Term::value(uint8_t base) const;

/**
 * Get representation of rounding mode value term.
 * @param base Ignored for this template instantiation.
 * @return The RoundingMode representation of the given rounding mode value.
 */
template <>
RoundingMode Term::value(uint8_t base) const;

/**
 * Get string representation of Boolean, bit-vector, floating-point, or
 * rounding mode value term.
 *
 * @param base The base of the string representation of bit-vector values; `2`
 *             for binary, `10` for decimal, and `16` for hexadecimal.
 *
 * @return String representation of the value term.
 *
 * @note Parameter `base` is ignored for Boolean and RoundingMode values.
 */
template <>
std::string Term::value(uint8_t base) const;

/**
 * Get string of IEEE 754 standard representation of floating-point value term.
 *
 * @param base The base in which the output strings are given; 2 for
 *             binary, 10 for decimal, and 16 for hexadecimal.
 *
 * @return A tuple of string repsentations <sign, exponent, significand>.
 */
template <>
std::tuple<std::string, std::string, std::string> Term::value(
    uint8_t base) const;
#endif

/**
 * Syntactical equality operator.
 *
 * @param a The first term.
 * @param b The second term.
 * @return True if the given terms are equal.
 */
bool operator==(const Term &a, const Term &b);

/**
 * Syntactical disequality operator.
 *
 * @param a The first term.
 * @param b The second term.
 * @return True if the given terms are disequal.
 */
bool operator!=(const Term &a, const Term &b);

/**
 * Print term to output stream.
 * @param out The output stream.
 * @param term The term.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, const Term &term);

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

class Sort
{
  friend Bitwuzla;
  friend Term;
  friend bool operator==(const Sort &a, const Sort &b);
  friend bool operator!=(const Sort &a, const Sort &b);
  friend std::ostream &operator<<(std::ostream &out, const Sort &sort);
  friend std::hash<bitwuzla::Sort>;
  friend Sort mk_array_sort(const Sort &, const Sort &);
  friend Sort mk_bool_sort();
  friend Sort mk_bv_sort(uint64_t);
  friend Sort mk_fp_sort(uint64_t, uint64_t);
  friend Sort mk_fun_sort(const std::vector<Sort> &, const Sort &);
  friend Sort mk_uninterpreted_sort(std::optional<const std::string>);
  friend Sort mk_rm_sort();
  friend Term mk_bv_zero(const Sort &);
  friend Term mk_bv_one(const Sort &);
  friend Term mk_bv_ones(const Sort &);
  friend Term mk_bv_min_signed(const Sort &);
  friend Term mk_bv_max_signed(const Sort &);
  friend Term mk_bv_value(const Sort &, const std::string &, uint8_t);
  friend Term mk_bv_value_uint64(const Sort &, uint64_t);
  friend Term mk_bv_value_int64(const Sort &, int64_t);
  friend Term mk_fp_pos_zero(const Sort &);
  friend Term mk_fp_neg_zero(const Sort &);
  friend Term mk_fp_pos_inf(const Sort &);
  friend Term mk_fp_neg_inf(const Sort &);
  friend Term mk_fp_nan(const Sort &);
  friend Term mk_fp_value(const Sort &, const Term &, const std::string &);
  friend Term mk_fp_value(const Sort &,
                          const Term &,
                          const std::string &,
                          const std::string &);
  friend Term mk_const_array(const Sort &, const Term &);
  friend Term mk_term(Kind,
                      const std::vector<Term> &,
                      const std::vector<uint64_t> &);
  friend Term mk_const(const Sort &, std::optional<const std::string>);
  friend Term mk_var(const Sort &, std::optional<const std::string>);

 public:
  /** Default constructor, creates null sort. */
  Sort();
  /** Destructor. */
  ~Sort();

  /**
   * Determine if this sort is a null sort.
   * @return True if this sort is a null sort.
   */
  bool is_null() const;

  /**
   * Get the id of this sort.
   * @return The sort id.
   */
  uint64_t id() const;

  /**
   * Get the size of a bit-vector sort.
   *
   * Requires that given sort is a bit-vector sort.
   *
   * @return The size of the bit-vector sort.
   */
  uint64_t bv_size() const;
  /**
   * Get the exponent size of a floating-point sort.
   *
   * Requires that given sort is a floating-point sort.
   *
   * @return The exponent size of the floating-point sort.
   */
  uint64_t fp_exp_size() const;
  /**
   * Get the significand size of a floating-point sort.
   *
   * Requires that given sort is a floating-point sort.
   *
   * @return The significand size of the floating-point sort.
   */
  uint64_t fp_sig_size() const;
  /**
   * Get the index sort of an array sort.
   *
   * Requires that given sort is an array sort.
   *
   * @return The index sort of the array sort.
   */
  Sort array_index() const;

  /**
   * Get the element sort of an array sort.
   *
   * Requires that given sort is an array sort.
   *
   * @return The element sort of the array sort.
   */
  Sort array_element() const;

  /**
   * Get the domain sorts of a function sort.
   *
   * Requires that given sort is a function sort.
   *
   * @return The domain sorts of the function sort.
   */
  std::vector<Sort> fun_domain() const;

  /**
   * Get the codomain sort of a function sort.
   *
   * Requires that given sort is a function sort.
   *
   * @return The codomain sort of the function sort.
   */
  Sort fun_codomain() const;

  /**
   * Get the arity of a function sort.
   * @return The number of arguments of the function sort.
   */
  size_t fun_arity() const;

  /**
   * Get the symbol of an uninterpreted sort.
   * @return The symbol.
   */
  std::optional<std::string> uninterpreted_symbol() const;

  /**
   * Determine if this sort is an array sort.
   * @return True if this sort is an array sort.
   */
  bool is_array() const;

  /**
   * Determine if this sort is a Boolean sort.
   * @return True if this sort is a Boolean sort.
   */
  bool is_bool() const;

  /**
   * Determine if this sort is a bit-vector sort.
   * @return True if `sort` is a bit-vector sort.
   */
  bool is_bv() const;

  /**
   * Determine if this sort is a floating-point sort.
   * @return True if this sort is a floating-point sort.
   */
  bool is_fp() const;

  /**
   * Determine if this sort is a function sort.
   * @return True if this sort is a function sort.
   */
  bool is_fun() const;

  /**
   * Determine if this sort is a Roundingmode sort.
   * @return True if this sort is a Roundingmode sort.
   */
  bool is_rm() const;

  /**
   * Determine if this sort is an uninterpreted sort.
   * @return True if this sort is an uninterpreted sort.
   */
  bool is_uninterpreted() const;

  /**
   * Get string representation of this sort.
   * @return String representation of this sort.
   */
  std::string str() const;

 private:
  /** Convert vector of sorts to internal types. */
  static std::vector<bzla::Type> sort_vector_to_types(
      const std::vector<Sort> &sorts);
  /** Constructor from internal type. */
  Sort(const bzla::Type &type);
  /** The internal type wrapped by this sort. */
  std::shared_ptr<bzla::Type> d_type;
};

/**
 * Syntactical equality operator.
 *
 * @param a The first sort.
 * @param b The second sort.
 * @return True if the given sorts are equal.
 */
bool operator==(const Sort &a, const Sort &b);

/**
 * Syntactical disequality operator.
 *
 * @param a The first sort.
 * @param b The second sort.
 * @return True if the given sorts are disequal.
 */
bool operator!=(const Sort &a, const Sort &b);

/**
 * Print sort to output stream.
 * @param out The output stream.
 * @param sort The sort.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, const Sort &sort);

/* -------------------------------------------------------------------------- */
/* Terminator                                                                 */
/* -------------------------------------------------------------------------- */

/** The termination callback configuration. */
class Terminator
{
 public:
  /** Destructor. */
  virtual ~Terminator();
  /**
   * Termination function.
   * If terminator has been connected, Bitwuzla calls this function periodically
   * to determine if the connected instance should be terminated.
   * @return True if the associated instance of Bitwuzla should be terminated.
   */
  virtual bool terminate() = 0;
};

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

/** The Bitwuzla solver instance. */
class Bitwuzla
{
 public:
  /**
   * Constructor.
   * @param options The associated options instance. Options must be configured
   *                at this point.
   */
  Bitwuzla(const Options &options = Options());
  /** Destructor. */
  ~Bitwuzla();

  /** Disallow copy construction. */
  Bitwuzla(const Bitwuzla &bitwuzla) = delete;
  /** Disallow copy assignment. */
  Bitwuzla &operator=(const Bitwuzla &bitwuzla) = delete;

  /**
   * Connect or disconnect associated termination configuration instance.
   * @note Only one terminator can be connected at a time. This will disconnect
   *       a previously connected terminator before connecting a new one.
   * @param terminator The terminator instance. Nullptr disconnects the
   *                   currently associated terminator.
   */
  void configure_terminator(Terminator *terminator);

  /**
   * Push context levels.
   *
   * @param nlevels The number of context levels to push.
   *
   * @see
   *   * `Options::set()`
   */
  void push(uint32_t nlevels);
  /**
   * Pop context levels.
   *
   * @param nlevels The number of context levels to pop.
   *
   * @see
   *   * `Options::set()`
   */
  void pop(uint32_t nlevels);

  /**
   * Assert formula.
   *
   * @param term The formula to assert.
   */
  void assert_formula(const Term &term);

  /**
   * Get the set of currently asserted formulas.
   * @return The assertion formulas.
   */
  std::vector<Term> get_assertions();

  /**
   * Determine if an assumption is an unsat assumption.
   *
   * Unsat assumptions are assumptions that force an input formula to become
   * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
   * failed assumptions in MiniSAT.
   *
   * Requires that the last `check_sat()` query returned `Result::UNSAT`.
   *
   * @param term The assumption to check for.
   *
   * @return True if given assumption is an unsat assumption.
   *
   * @see
   *   * `Options::set()`
   *   * `check_sat()`
   */
  bool is_unsat_assumption(const Term &term);
  /**
   * Get the set of unsat assumptions.
   *
   * Unsat assumptions are assumptions that force an input formula to become
   * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
   * failed assumptions in MiniSAT.
   *
   * Requires that the last `check_sat()` query returned `Result::UNSAT`.
   *
   * @return A vctor with unsat assumptions.
   *
   * @see
   *   * `Options::set()`
   *   * `check_sat()`
   */
  std::vector<Term> get_unsat_assumptions();
  /**
   * Get the unsat core (unsat assertions).
   *
   * The unsat core consists of the set of assertions that force an input
   * formula to become unsatisfiable.
   *
   * Requires that the last `check_sat()` query returned `Result::UNSAT`.
   *
   * @return A vector with unsat assertions.
   *
   * @see
   *   * `assert()`
   *   * `check_sat()`
   */
  std::vector<Term> get_unsat_core();

  /**
   * Simplify the current input formula.
   *
   * @note Each call to `Bitwuzla::check_sat()` simplifies the input formula as
   *       a preprocessing step. It is not necessary to call this function
   *       explicitly in the general case.
   *
   * @see
   *   * `assert_formula()`
   */
  void simplify();

  /**
   * Check satisfiability of current input formula.
   *
   * An input formula consists of assertions added via `assert_formula()`.
   * The search for a solution can by guided by making assumptions via
   * passing a vector of assumptions to `check_sat()`.
   *
   * @note Assertions and assumptions are combined via Boolean and.
   *
   * @return `Result::SAT` if the input formula is satisfiable and
   *         `Result::UNSAT` if it is unsatisfiable, and `Result::UNKNOWN`
   *         when neither satisfiability nor unsatisfiability was determined.
   *         This can happen when this Bitwuzla instance was terminated via a
   *         termination callback.
   *
   * @see
   *   * `assert_formula()`
   *   * `Options::set()`
   *   * `Result`
   */
  Result check_sat(const std::vector<Term> &assumptions = {});

  /**
   * Get a term representing the model value of a given term.
   *
   * Requires that the last `check_sat()` query returned
   * `Result::SAT`.
   *
   * @param term The term to query a model value for.
   * @return A term representing the model value of term `term`.
   * @see `check_sat()`
   */
  Term get_value(const Term &term);

  /**
   * Print the current input formula to the given output stream.
   *
   * @param out    The output stream.
   * @param format The output format for printing the formula. Currently, only
   *               `"smt2"` for the SMT-LIB v2 format is supported.
   */
  void print_formula(std::ostream &out,
                     const std::string &format = "smt2") const;

  /**
   * Get current statistics.
   * @return A map of strings of statistics entries, maps statistic name
   *         to value.
   */
  std::map<std::string, std::string> statistics() const;

 private:
  /** Helper called when solver state changes. */
  void solver_state_change();

  /** The associated solving context. */
  std::unique_ptr<bzla::SolvingContext> d_ctx;
  /** The result of the last check_sat() call. */
  Result d_last_check_sat = Result::UNKNOWN;
  /** The number of issued check-sat queries. */
  uint64_t d_n_sat_calls = 0;
  /** The associated terminator. */
  Terminator *d_terminator = nullptr;
  /** The internal terminator. */
  std::unique_ptr<bzla::Terminator> d_terminator_internal;
  /** Cache holding the current unsat core. */
  std::vector<Term> d_unsat_core;
  /** Cache the current set of assumptions. */
  std::unordered_set<Term> d_assumptions;
  /** True if d_unsat_core holds the current unsat core. */
  bool d_uc_is_valid = false;
  /** Indicates a pending pop from check-sat with assumptions. */
  bool d_pending_pop = false;
};

/* -------------------------------------------------------------------------- */
/* Sort creation                                                              */
/* -------------------------------------------------------------------------- */

/** \addtogroup cpp_sort_creation
 *  @{
 */

/**
 * Create an array sort.
 * @param index The index sort of the array sort.
 * @param element The element sort of the array sort.
 * @return An array sort which maps sort `index` to sort `element`.
 *
 * @see
 *   * `Sort::is_array()`
 *   * `Sort::array_get_index()`
 *   * `Sort::array_get_element()`
 */
Sort mk_array_sort(const Sort &index, const Sort &element);

/**
 * Create a Boolean sort.
 * @return A Boolean sort.
 */
Sort mk_bool_sort();

/**
 * Create a bit-vector sort of given size.
 * @param size The size of the bit-vector sort.
 * @return A bit-vector sort of given size.
 *
 * @see
 *   * `Sort::is_bv()`
 *   * `Sort::bv_size()`
 */
Sort mk_bv_sort(uint64_t size);

/**
 * Create a floating-point sort of given exponent and significand size.
 * @param exp_size The size of the exponent.
 * @param sig_size The size of the significand (including sign bit).
 * @return A floating-point sort of given format.
 *
 * @see
 *   * `Sort::is_fp()`
 *   * `Sort::fp_exp_size()`
 *   * `Sort::fp_sig_size()`
 */
Sort mk_fp_sort(uint64_t exp_size, uint64_t sig_size);

/**
 * Create a function sort.
 * @param domain   The domain sorts (the sorts of the arguments). The number of
 *                 sorts in this vector must match `arity`.
 * @param codomain The codomain sort (the sort of the return value).
 * @return A function sort of given domain and codomain sorts.
 *
 * @see
 *   * `Sort::is_fun()`
 *   * `Sort::fun_arity()`
 *   * `Sort::fun_domain_sorts()`
 *   * `Sort::fun_codomain()`
 */
Sort mk_fun_sort(const std::vector<Sort> &domain, const Sort &codomain);

/**
 * Create a Roundingmode sort.
 * @return A Roundingmode sort.
 * @see
 *   * `Sort::is_rm()`
 */
Sort mk_rm_sort();

/**
 * Create an uninterpreted sort.
 *
 * @note Only 0-arity uninterpreted sorts are supported.
 *
 * @param symbol The symbol of the sort.
 * @return An uninterpreted sort.
 *
 * @see
 *   * `Sort::is_uninterpreted()`
 */
Sort mk_uninterpreted_sort(
    std::optional<const std::string> symbol = std::nullopt);

/** @} */

/* -------------------------------------------------------------------------- */
/* Term creation                                                              */
/* -------------------------------------------------------------------------- */

/** \addtogroup cpp_term_creation
 *  @{
 */

/**
 * Create a true value.
 * @return A term representing true.
 */
Term mk_true();

/**
 * Create a false value.
 * @return A term representing false.
 */
Term mk_false();

/**
 * Create a bit-vector value zero.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value 0 of given sort.
 *
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_zero(const Sort &sort);

/**
 * Create a bit-vector value one.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value 1 of given sort.
 *
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_one(const Sort &sort);

/**
 * Create a bit-vector value where all bits are set to 1.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort
 *         where all bits are set to 1.
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_ones(const Sort &sort);

/**
 * Create a bit-vector minimum signed value.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 1 and all remaining bits are set to 0.
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_min_signed(const Sort &sort);

/**
 * Create a bit-vector maximum signed value.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 0 and all remaining bits are set to 1.
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_max_signed(const Sort &sort);

/**
 * Create a bit-vector value from its string representation.
 *
 * Parameter `base` determines the base of the string representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value A string representing the value.
 * @param base The base in which the string is given; `2` for binary, `10` for
 *             decimal, and `16` for hexadecimal.
 *
 * @return A term of kind Kind::VALUE, representing the bit-vector value
 *         of given sort.
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_value(const Sort &sort, const std::string &value, uint8_t base = 2);

/**
 * Create a bit-vector value from its unsigned integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind Kind::VALUE, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_value_uint64(const Sort &sort, uint64_t value);

/**
 * Create a bit-vector value from its signed integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind Kind::VALUE, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `mk_bv_sort()`
 */
Term mk_bv_value_int64(const Sort &sort, int64_t value);

/**
 * Create a floating-point positive zero value (SMT-LIB: `+zero`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive zero value of given
 *         floating-point sort.
 * @see
 *  * `mk_fp_sort()`
 */
Term mk_fp_pos_zero(const Sort &sort);

/**
 * Create a floating-point negative zero value (SMT-LIB: `-zero`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative zero value of given
 *         floating-point sort.
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_neg_zero(const Sort &sort);

/**
 * Create a floating-point positive infinity value (SMT-LIB: `+oo`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive infinity value of
 *         given floating-point sort.
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_pos_inf(const Sort &sort);

/**
 * Create a floating-point negative infinity value (SMT-LIB: `-oo`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative infinity value of
 *         given floating-point sort.
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_neg_inf(const Sort &sort);

/**
 * Create a floating-point NaN value.
 * @param sort The sort of the value.
 * @return A term representing the floating-point NaN value of given
 *         floating-point sort.
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_nan(const Sort &sort);

/**
 * Create a floating-point value from its IEEE 754 standard representation
 * given as three bit-vector values representing the sign bit, the exponent and
 * the significand.
 *
 * @param bv_sign The sign bit.
 * @param bv_exponent The exponent bit-vector value.
 * @param bv_significand The significand bit-vector value.
 *
 * @return A term of kind Kind::VALUE, representing the floating-point value.
 */
Term mk_fp_value(const Term &bv_sign,
                 const Term &bv_exponent,
                 const Term &bv_significand);

/**
 * Create a floating-point value from its real representation, given as a
 * decimal string, with respect to given rounding mode.
 *
 * @note Given rounding mode may be an arbitrary, non-value rounding mode term.
 *       If it is a value, the returned term will be a floating-point value,
 *       else a non-value floating-point term.
 *
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param real The decimal string representing a real value.
 *
 * @return A floating-point representation of the given real string. If `rm`
 *         is of kind Kind::VALUE the floating-point will be of kind
 *         Kind::VALUE, else it will be a non-value term.
 *
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_value(const Sort &sort, const Term &rm, const std::string &real);

/**
 * Create a floating-point value from its rational representation, given as a
 * two decimal strings representing the numerator and denominator, with respect
 * to given rounding mode.
 *
 * @note Given rounding mode may be an arbitrary, non-value rounding mode term.
 *       If it is a value, the returned term will be a floating-point value,
 *       else a non-value floating-point term.
 *
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param num The decimal string representing the numerator.
 * @param den The decimal string representing the denominator.
 *
 * @return A floating-point representation of the given rational string. If
 *         `rm` is of kind Kind::VALUE the floating-point will be of kind
 *         Kind::VALUE, else it will be a non-value term.
 *
 * @see
 *   * `mk_fp_sort()`
 */
Term mk_fp_value(const Sort &sort,
                 const Term &rm,
                 const std::string &num,
                 const std::string &den);

/**
 * Create a one-dimensional constant array of given sort, initialized with
 * given value.
 *
 * @param sort The sort of the array.
 * @param value The term to initialize the elements of the array with.
 *
 * @return A term of kind Kind::CONST_ARRAY, representing a constant
 *         array of given sort.
 *
 * @see
 *   * `mk_array_sort()`
 */
Term mk_const_array(const Sort &sort, const Term &term);

/**
 * Create a rounding mode value.
 * @param rm The rounding mode value.
 * @return A term of kind Kind::VALUE, representing the rounding mode value.
 *
 * @see
 *   * `RoundingMode`
 */
Term mk_rm_value(RoundingMode rm);

/**
 * Create a term of given kind with the given argument terms.
 *
 * @param kind The operator kind.
 * @param args The argument terms.
 * @param indices The indices of this term, empty if not indexed.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `Kind`
 */
Term mk_term(Kind kind,
             const std::vector<Term> &args,
             const std::vector<uint64_t> &indices = {});

/**
 * Create a (first-order) constant of given sort with given symbol.
 *
 * @param sort The sort of the constant.
 * @param symbol The symbol of the constant.
 *
 * @return A term of Kind::CONSTANT, representing the constant.
 *
 * @see
 *   * `mk_array_sort()`
 *   * `mk_bool_sort()`
 *   * `mk_bv_sort()`
 *   * `mk_fp_sort()`
 *   * `mk_fun_sort()`
 *   * `mk_rm_sort()`
 */
Term mk_const(const Sort &sort,
              std::optional<const std::string> symbol = std::nullopt);

/**
 * Create a variable of given sort with given symbol.
 *
 * @note This creates a variable to be bound by quantifiers or lambdas.
 *
 * @param sort The sort of the variable.
 * @param symbol The symbol of the variable.
 *
 * @return A term of Kind::VARIABLE, representing the variable.
 *
 * @see
 *   * `mk_bool_sort()`
 *   * `mk_bv_sort()`
 *   * `mk_fp_sort()`
 *   * `mk_fun_sort()`
 *   * `mk_rm_sort()`
 */
Term mk_var(const Sort &sort,
            std::optional<const std::string> symbol = std::nullopt);

/** @} */

/* -------------------------------------------------------------------------- */
/* Term substitution                                                          */
/* -------------------------------------------------------------------------- */

/** \addtogroup cpp_term_substitution
 *  @{
 */

/**
 * Substitute a set terms in a given term. The substitutions to perform are
 * represented as map from keys to be substituted with their corresponding
 * values in the given term.
 *
 * @param term The term in which the terms are to be substituted.
 * @param map  The substitution map.
 * @return The resulting term from this substitution.
 */
Term substitute_term(const Term &term,
                     const std::unordered_map<Term, Term> &map);

/**
 * Substitute a set of terms in a set of given terms. The substitutions to
 * perform are represented as map from keys to be substituted with their
 * corresponding values in the given terms.
 *
 * The terms in `terms` are replaced with the terms resulting from these
 * substitutions.
 *
 * @param terms The terms in which the terms are to be substituted.
 * @param map  The substitution map.
 */
void substitute_terms(std::vector<Term> &terms,
                      const std::unordered_map<Term, Term> &map);

/** @} */

/* -------------------------------------------------------------------------- */

}  // namespace bitwuzla

/* -------------------------------------------------------------------------- */

namespace std {

/**
 * Get string representation of given kind.
 * @param kind The kind.
 * @return The string representation.
 */
std::string to_string(bitwuzla::Kind kind);

/**
 * Get string representation of given rounding mode.
 * @param rm The roundingmode.
 * @return The string representation.
 */
std::string to_string(bitwuzla::RoundingMode rm);

/**
 * Get string representation of given result.
 * @param result The result.
 * @return The string representation.
 */
std::string to_string(bitwuzla::Result result);

}  // namespace std

#endif
