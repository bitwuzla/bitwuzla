#ifndef BITWUZLA_API_CPP_H_INCLUDED
#define BITWUZLA_API_CPP_H_INCLUDED

#include <functional>
#include <iostream>
#include <memory>
#include <optional>

#include "api/option.h"

/* -------------------------------------------------------------------------- */

namespace bzla {
class Node;
class Type;
class SolvingContext;
namespace option {
class Options;
}
}  // namespace bzla

/* -------------------------------------------------------------------------- */

namespace bitwuzla {

/* -------------------------------------------------------------------------- */

/**
 * Get copyright information.
 * @return A string with the copyright information.
 */
std::string copyright();
/**
 * Get version information.
 * @return A string with the version information.
 */
std::string version();
/**
 * Get git information.
 * @return A string with the git information.
 */
std::string git_id();

/* -------------------------------------------------------------------------- */

class Bitwuzla;

using Option = BitwuzlaOption;

class OptionInfo
{
  // TODO
};

class Options
{
  friend Bitwuzla;

 public:
  /**
   * Set option.
   *
   * @param option The option.
   * @param val The option value.
   *
   * @see
   *   * `Option`
   */
  void set(Option option, uint64_t value);
  /**
   * Set option.
   *
   * @param option The option.
   * @param val The option value.
   *
   * @see
   *   * `Option`
   */
  void set(Option option, bool value);

  /**
   * Set option value for options with different modes.
   *
   * @param option The option.
   * @param mode The option mode.
   *
   * @see
   *   * `Option`
   */
  void set(Option option, const std::string &mode);

  /**
   * Get the current value of a numeric option.
   *
   * @param option The option.
   * @return The option value.
   *
   * @see
   *   * `Option`
   */
  uint64_t get_numeric(Option option) const;
  /**
   * Get the current value of a Boolean option.
   *
   * @param option The option.
   * @return The option value.
   *
   * @see
   *   * `Option`
   */
  bool get_bool(Option option) const;
  /**
   * Get the current value of an option with modes.
   *
   * @param option The option.
   * @return The option value.
   *
   * @see
   *   * `Option`
   */
  const std::string &get_mode(Option option) const;

  /**
   * Get the details of an option.
   *
   * @param option The option.
   * @param info The option info to populate, will be valid until the next
   *             `bitwuzla_get_option_info` call.
   *
   * @see
   *   * `BitwuzlaOptionInfo`
   */
  const OptionInfo &get_info(Option option) const;

 private:
  /** The wrapped internal options. */
  std::unique_ptr<bzla::option::Options> d_options;
};

/* -------------------------------------------------------------------------- */

/** A satisfiability result. */
enum class Result
{
  SAT     = 10,  ///< sat
  UNSAT   = 20,  ///< unsat
  UNKNOWN = 0,   ///< unknown
};
/**
 * Print result to output stream.
 * @param out The output stream.
 * @param result The result.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, Result result);

/* -------------------------------------------------------------------------- */

/** The term kind. */
enum class Kind
{
  /*! First order constant. */
  CONSTANT,
  /*! Constant array. */
  CONST_ARRAY,
  /*! Value. */
  VALUE,
  /*! Bound variable. */
  VARIABLE,

  //////// operators

  //// Boolean
  /*! Boolean and.
   *
   *  SMT-LIB: \c and */
  AND,
  /*! Disequality.
   *
   * SMT-LIB: \c distinct */
  DISTINCT,
  /*! Equality.
   *
   * SMT-LIB: \c = */
  EQUAL,
  /*! Boolean if and only if.
   *
   * SMT-LIB: \c = */
  IFF,
  /*! Boolean implies.
   *
   * SMT-LIB: \c => */
  IMPLIES,
  /*! Boolean not.
   *
   * SMT-LIB: \c not */
  NOT,
  /*! Boolean or.
   *
   * SMT-LIB: \c or */
  OR,
  /*! Boolean xor.
   *
   * SMT-LIB: \c xor */
  XOR,

  //// Core
  /*! If-then-else.
   *
   * SMT-LIB: \c ite */
  ITE,

  //// Quantifiers
  /*! Existential quantification.
   *
   * SMT-LIB: \c exists */
  EXISTS,
  /*! Universal quantification.
   *
   * SMT-LIB: \c forall */
  FORALL,

  //// Functions
  /*! Function application. */
  APPLY,
  /*! Lambda. */
  LAMBDA,

  //// Arrays
  /*! Array select.
   *
   *  SMT-LIB: \c select */
  ARRAY_SELECT,
  /*! Array store.
   *
   * SMT-LIB: \c store */
  ARRAY_STORE,

  //// Bit-vectors
  /*! Bit-vector addition.
   *
   *  SMT-LIB: \c bvadd */
  BV_ADD,
  /*! Bit-vector and.
   *
   * SMT-LIB: \c bvand */
  BV_AND,
  /*! Bit-vector arithmetic right shift.
   *
   * SMT-LIB: \c bvashr */
  BV_ASHR,
  /*! Bit-vector comparison.
   *
   * SMT-LIB: \c bvcomp */
  BV_COMP,
  /*! Bit-vector concat.
   *
   * SMT-LIB: \c concat */
  BV_CONCAT,
  /*! Bit-vector decrement.
   *
   * Decrement by one. */
  BV_DEC,
  /*! Bit-vector increment.
   *
   * Increment by one. */
  BV_INC,
  /*! Bit-vector multiplication.
   *
   * SMT-LIB: \c bvmul */
  BV_MUL,
  /*! Bit-vector nand.
   *
   * SMT-LIB: \c bvnand */
  BV_NAND,
  /*! Bit-vector negation (two's complement).
   *
   * SMT-LIB: \c bvneg */
  BV_NEG,
  /*! Bit-vector nor.
   *
   * SMT-LIB: \c bvnor */
  BV_NOR,
  /*! Bit-vector not (one's complement).
   *
   * SMT-LIB: \c bvnot */
  BV_NOT,
  /*! Bit-vector or.
   *
   * SMT-LIB: \c bvor */
  BV_OR,
  /*! Bit-vector and reduction.
   *
   * Bit-wise *and* reduction, all bits are *and*'ed together into a single bit.
   * This corresponds to bit-wise *and* reduction as known from Verilog. */
  BV_REDAND,
  /*! Bit-vector reduce or.
   *
   * Bit-wise *or* reduction, all bits are *or*'ed together into a single bit.
   * This corresponds to bit-wise *or* reduction as known from Verilog. */
  BV_REDOR,
  /*! Bit-vector reduce xor.
   *
   * Bit-wise *xor* reduction, all bits are *xor*'ed together into a single bit.
   * This corresponds to bit-wise *xor* reduction as known from Verilog. */
  BV_REDXOR,
  /*! Bit-vector rotate left (not indexed).
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_left. */
  BV_ROL,
  /*! Bit-vector rotate right.
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_right. */
  BV_ROR,
  /*! Bit-vector signed addition overflow test.
   *
   * Single bit to indicate if signed addition produces an overflow. */
  BV_SADD_OVERFLOW,
  /*! Bit-vector signed division overflow test.
   *
   * Single bit to indicate if signed division produces an overflow. */
  BV_SDIV_OVERFLOW,
  /*! Bit-vector signed division.
   *
   * SMT-LIB: \c bvsdiv */
  BV_SDIV,
  /*! Bit-vector signed greater than or equal.
   *
   * SMT-LIB: \c bvsle */
  BV_SGE,
  /*! Bit-vector signed greater than.
   *
   * SMT-LIB: \c bvslt */
  BV_SGT,
  /*! Bit-vector logical left shift.
   *
   * SMT-LIB: \c bvshl */
  BV_SHL,
  /*! Bit-vector logical right shift.
   *
   * SMT-LIB: \c bvshr */
  BV_SHR,
  /*! Bit-vector signed less than or equal.
   *
   * SMT-LIB: \c bvsle */
  BV_SLE,
  /*! Bit-vector signed less than.
   *
   * SMT-LIB: \c bvslt */
  BV_SLT,
  /*! Bit-vector signed modulo.
   *
   * SMT-LIB: \c bvsmod */
  BV_SMOD,
  /*! Bit-vector signed multiplication overflow test.
   *
   * SMT-LIB: \c bvsmod */
  BV_SMUL_OVERFLOW,
  /*! Bit-vector signed remainder.
   *
   * SMT-LIB: \c bvsrem */
  BV_SREM,
  /*! Bit-vector signed subtraction overflow test.
   *
   * Single bit to indicate if signed subtraction produces an overflow. */
  BV_SSUB_OVERFLOW,
  /*! Bit-vector subtraction.
   *
   * SMT-LIB: \c bvsub */
  BV_SUB,
  /*! Bit-vector unsigned addition overflow test.
   *
   * Single bit to indicate if unsigned addition produces an overflow. */
  BV_UADD_OVERFLOW,
  /*! Bit-vector unsigned division.
   *
   * SMT-LIB: \c bvudiv */
  BV_UDIV,
  /*! Bit-vector unsigned greater than or equal.
   *
   * SMT-LIB: \c bvuge */
  BV_UGE,
  /*! Bit-vector unsigned greater than.
   *
   * SMT-LIB: \c bvugt */
  BV_UGT,
  /*! Bit-vector unsigned less than or equal.
   *
   * SMT-LIB: \c bvule */
  BV_ULE,
  /*! Bit-vector unsigned less than.
   *
   * SMT-LIB: \c bvult */
  BV_ULT,
  /*! Bit-vector unsigned multiplication overflow test.
   *
   * Single bit to indicate if unsigned multiplication produces an overflow. */
  BV_UMUL_OVERFLOW,
  /*! Bit-vector unsigned remainder.
   *
   * SMT-LIB: \c bvurem */
  BV_UREM,
  /*! Bit-vector unsigned subtraction overflow test.
   *
   * Single bit to indicate if unsigned subtraction produces an overflow. */
  BV_USUB_OVERFLOW,
  /*! Bit-vector xnor.
   *
   * SMT-LIB: \c bvxnor */
  BV_XNOR,
  /*! Bit-vector xor.
   *
   * SMT-LIB: \c bvxor */
  BV_XOR,
  // indexed
  /*! Bit-vector extract.
   *
   * SMT-LIB: \c extract (indexed) */
  BV_EXTRACT,
  /*! Bit-vector repeat.
   *
   * SMT-LIB: \c repeat (indexed) */
  BV_REPEAT,
  /*! Bit-vector rotate left by integer.
   *
   * SMT-LIB: \c rotate_left (indexed) */
  BV_ROLI,
  /*! Bit-vector rotate right by integer.
   *
   * SMT-LIB: \c rotate_right (indexed) */
  BV_RORI,
  /*! Bit-vector sign extend.
   *
   * SMT-LIB: \c sign_extend (indexed) */
  BV_SIGN_EXTEND,
  /*! Bit-vector zero extend.
   *
   * SMT-LIB: \c zero_extend (indexed) */
  BV_ZERO_EXTEND,
  /*! Floating-point to_fp from IEEE 754 bit-vector.
   *
   * SMT-LIB: \c to_fp (indexed) */

  //// Floating-point arithmetic
  /*! Floating-point absolute value.
   *
   * SMT-LIB: \c fp.abs */
  FP_ABS,
  /*! Floating-point addition.
   *
   * SMT-LIB: \c fp.add */
  FP_ADD,
  /*! Floating-point division.
   *
   * SMT-LIB: \c fp.div */
  FP_DIV,
  /*! Floating-point equality.
   *
   * SMT-LIB: \c fp.eq */
  FP_EQUAL,
  /*! Floating-point fused multiplcation and addition.
   *
   * SMT-LIB: \c fp.fma */
  FP_FMA,
  /*! Floating-point IEEE 754 value.
   *
   * SMT-LIB: \c fp */
  FP_FP,
  /*! Floating-point greater than or equal.
   *
   * SMT-LIB: \c fp.geq */
  FP_GE,
  /*! Floating-point greater than.
   *
   * SMT-LIB: \c fp.gt */
  FP_GT,
  /*! Floating-point is infinity tester.
   *
   * SMT-LIB: \c fp.isInfinite */
  FP_IS_INF,
  /*! Floating-point is Nan tester.
   *
   * SMT-LIB: \c fp.isNaN */
  FP_IS_NAN,
  /*! Floating-point is negative tester.
   *
   * SMT-LIB: \c fp.isNegative */
  FP_IS_NEG,
  /*! Floating-point is normal tester.
   *
   * SMT-LIB: \c fp.isNormal */
  FP_IS_NORMAL,
  /*! Floating-point is positive tester.
   *
   * SMT-LIB: \c fp.isPositive */
  FP_IS_POS,
  /*! Floating-point is subnormal tester.
   *
   * SMT-LIB: \c fp.isSubnormal */
  FP_IS_SUBNORMAL,
  /*! Floating-point is zero tester.
   *
   * SMT-LIB: \c fp.isZero */
  FP_IS_ZERO,
  /*! Floating-point less than or equal.
   *
   * SMT-LIB: \c fp.leq */
  FP_LEQ,
  /*! Floating-point less than.
   *
   * SMT-LIB: \c fp.lt */
  FP_LT,
  /*! Floating-point max.
   *
   * SMT-LIB: \c fp.max */
  FP_MAX,
  /*! Floating-point min.
   *
   * SMT-LIB: \c fp.min */
  FP_MIN,
  /*! Floating-point multiplcation.
   *
   * SMT-LIB: \c fp.mul */
  FP_MUL,
  /*! Floating-point negation.
   *
   * SMT-LIB: \c fp.neg */
  FP_NEG,
  /*! Floating-point remainder.
   *
   * SMT-LIB: \c fp.rem */
  FP_REM,
  /*! Floating-point round to integral.
   *
   * SMT-LIB: \c fp.roundToIntegral */
  FP_RTI,
  /*! Floating-point round to square root.
   *
   * SMT-LIB: \c fp.sqrt */
  FP_SQRT,
  /*! Floating-point round to subtraction.
   *
   * SMT-LIB: \c fp.sqrt */
  FP_SUB,
  // indexed
  FP_TO_FP_FROM_BV,
  /*! Floating-point to_fp from floating-point.
   *
   * SMT-LIB: \c to_fp (indexed) */
  FP_TO_FP_FROM_FP,
  /*! Floating-point to_fp from signed bit-vector value.
   *
   * SMT-LIB: \c to_fp (indexed) */
  FP_TO_FP_FROM_SBV,
  /*! Floating-point to_fp from unsigned bit-vector value.
   *
   * SMT-LIB: \c to_fp_unsigned (indexed) */
  FP_TO_FP_FROM_UBV,
  /*! Floating-point to_sbv.
   *
   * SMT-LIB: \c fp.to_sbv (indexed) */
  FP_TO_SBV,
  /*! Floating-point to_ubv.
   *
   * SMT-LIB: \c fp.to_ubv (indexed) */
  FP_TO_UBV,
#ifndef DOXYGEN_SKIP
  NUM_KINDS,
#endif
};

/**
 * Print kind to output stream.
 * @param out The output stream.
 * @param kind The kind.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, Kind kind);

/* -------------------------------------------------------------------------- */

/**
 * Rounding mode for floating-point operations.
 *
 * For some floating-point operations, infinitely precise results may not be
 * representable in a given format. Hence, they are rounded modulo one of five
 * rounding modes to a representable floating-point number.
 *
 * \verbatim embed:rst:leading-asterisk
 * The following rounding modes follow the SMT-LIB theory for floating-point
 * arithmetic, which in turn is based on IEEE Standard 754 :cite:`IEEE754`.
 * The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
 * Standard 754.
 * \endverbatim
 */
enum class RoundingMode
{
  /*!
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   *
   * SMT-LIB: \c RNE \c roundNearestTiesToEven
   */
  RNE = 0,
  /*!
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   *
   * SMT-LIB: \c RNA \c roundNearestTiesToAway
   */
  RNA = 1,
  /*!
   * Round towards negative infinity (-oo).
   * The result shall be the format’s floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   *
   * SMT-LIB: \c RTN \c roundTowardNegative
   */
  RTN = 2,
  /*!
   * Round towards positive infinity (+oo).
   * The result shall be the format’s floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   *
   * SMT-LIB: \c RTP \c roundTowardPositive
   */
  RTP = 3,
  /*!
   * Round towards zero.
   * The result shall be the format’s floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   *
   * SMT-LIB: \c RTZ \c roundTowardZero
   */
  RTZ = 4,
};

/**
 * Print rounding mode to output stream.
 * @param out The output stream.
 * @param rm The rounding mode.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, RoundingMode rm);

/* -------------------------------------------------------------------------- */

class Sort;

class Term
{
  friend Bitwuzla;
  friend bool operator==(const Term &, const Term &);
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
  friend Term mk_fp_value_from_real(const Sort &,
                                    const Term &,
                                    const std::string &);
  friend Term mk_fp_value_from_rational(const Sort &,
                                        const Term &,
                                        const std::string &,
                                        const std::string &);
  friend Term mk_rm_value(RoundingMode);
  friend Term mk_term(Kind,
                      const std::vector<Term> &,
                      const std::vector<uint64_t>);
  friend Term mk_const(
      const Sort &, std::optional<std::reference_wrapper<const std::string>>);
  friend Term mk_var(const Sort &,
                     std::optional<std::reference_wrapper<const std::string>>);
  friend Term substitute_term(const Term &,
                              const std::unordered_map<Term, Term>);

 public:
  /** Default constructor, creates null term. */
  Term();
  /** Destructor. */
  ~Term();

  /**
   * Determine if this term is a null term.
   * @return If this term is a null term.
   */
  bool is_null() const;

  /**
   * Get the kind of this term.
   *
   * @return The kind.
   *
   * @see Kind
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
   * @return The symbol of this term. Empty if no symbol is defined.
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
  bool is_var() const;

  /**
   * Determine if this term is a value.
   * @return True if this term is a value.
   */
  bool is_value() const;

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
   * Determine if this term is a floating-point positive zero (+zero) value.
   * @return True if this term is a floating-point +zero value.
   */
  bool is_fp_value_pos_zero() const;

  /**
   * Determine if this term is a floating-point value negative zero (-zero).
   * @return True if this term is a floating-point value negative zero.
   */
  bool is_fp_value_neg_zero() const;

  /**
   * Determine if this term is a floating-point positive infinity (+oo) value.
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
   * Determine if this term is a constant array.
   * @return True if this term is a constant array.
   */
  bool is_const_array() const;

  /**
   * Get the string representation of this term.
   * @return A string representation of this term.
   */
  std::string str();

 private:
  /** Convert vector of terms to internal nodes. */
  static std::vector<bzla::Node> term_vector_to_nodes(
      const std::vector<Term> &terms);
  /** Constructor from internal node. */
  Term(const bzla::Node &node);
  /** The internal node wrapped by this term. */
  std::shared_ptr<bzla::Node> d_node;
};

/**
 * Syntactical equality operator.
 *
 * @param a The first term.
 * @param b The second term.
 * @return True if the given terms are equal.
 */
bool operator==(const Term &a, const Term &b);

/**
 * Print term to output stream.
 * @param out The output stream.
 * @param term The term.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, const Term &term);

/* -------------------------------------------------------------------------- */

class Sort
{
  friend Bitwuzla;
  friend Term;
  friend bool operator==(const Sort &a, const Sort &b);
  friend std::ostream &operator<<(std::ostream &out, const Sort &sort);
  friend std::hash<bitwuzla::Sort>;
  friend Sort mk_array_sort(const Sort &, const Sort &);
  friend Sort mk_bool_sort();
  friend Sort mk_bv_sort(uint64_t);
  friend Sort mk_fp_sort(uint64_t, uint64_t);
  friend Sort mk_fun_sort(const std::vector<Sort> &, const Sort &);
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
  friend Term mk_fp_value_from_real(const Sort &,
                                    const Term &,
                                    const std::string &);
  friend Term mk_fp_value_from_rational(const Sort &,
                                        const Term &,
                                        const std::string &,
                                        const std::string &);
  friend Term mk_term(Kind,
                      const std::vector<Term> &,
                      const std::vector<uint64_t>);
  friend Term mk_const(
      const Sort &, std::optional<std::reference_wrapper<const std::string>>);
  friend Term mk_var(const Sort &,
                     std::optional<std::reference_wrapper<const std::string>>);

 public:
  /** Default constructor, creates null sort. */
  Sort();
  /** Destructor. */
  ~Sort();

  /**
   * Determine if this sort is a null sort.
   * @return If this sort is a null sort.
   */
  bool is_null() const;

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
  Sort array_get_index() const;

  /**
   * Get the element sort of an array sort.
   *
   * Requires that given sort is an array sort.
   *
   * @return The element sort of the array sort.
   */
  Sort array_get_element() const;

  /**
   * Get the domain sorts of a function sort.
   *
   * The domain sorts are returned as an array of sorts of size `size`.
   * Requires that given sort is a function sort.
   *
   * @return The domain sorts of the function sort.
   */
  std::vector<Sort> fun_get_domain() const;

  /**
   * Get the codomain sort of a function sort.
   *
   * Requires that given sort is a function sort.
   *
   * @return The codomain sort of the function sort.
   */
  Sort fun_get_codomain() const;

  /**
   * Get the arity of a function sort.
   * @return The number of arguments of the function sort.
   */
  size_t fun_arity() const;

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
   * Get string representation of this sort.
   * @param format The output format for printing the term. Either `"btor"` for
   *               the BTOR format, or `"smt2"` for the SMT-LIB v2 format.
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
 * Print sort to output stream.
 * @param out The output stream.
 * @param sort The sort.
 * @return The output stream.
 */
std::ostream &operator<<(std::ostream &out, const Sort &sort);

/* -------------------------------------------------------------------------- */

class Bitwuzla
{
 public:
  Bitwuzla(const Options &options);
  ~Bitwuzla();

  /**
   * If termination callback function has been configured via
   * `set_termination_callback()`, call this termination function.
   *
   * @return True if this instance of Bitwuzla has been terminated.
   *
   * @see
   *   * `set_termination_callback`
   *   * `get_termination_callback_state`
   */
  bool terminate();
  /**
   * Configure a termination callback function.
   *
   * The `state` of the callback can be retrieved via
   * `get_termination_callback_state()`.
   *
   * @param fun The callback function. Returns a value != 0 if this instance
   *            of Bitwuzla has been terminated.
   * @param state The argument to the callback function.
   *
   * @see
   *   * `terminate`
   *   * `get_termination_callback_state`
   */
  void set_termination_callback(std::function<int32_t(void *)> fun,
                                void *state);
  /**
   * Get the state of the termination callback function.
   *
   * The returned object representing the state of the callback corresponds
   * to the `state` configured as argument to the callback function via
   * `set_termination_callback()`.
   *
   * @return The object passed as argument `state` to the callback function.
   *
   * @see
   *   * `terminate`
   *   * `set_termination_callback`
   */
  void *get_termination_callback_state();
  /**
   * Configure an abort callback function, which is called instead of exit
   * on abort conditions.
   *
   * TODO should be per instance
   * @note This function is not thread safe (the function pointer is maintained
   *       as a global variable). It you use threading, make sure to set the
   *       abort callback prior to creating threads.
   *
   * @param fun The callback function. The argument string explains the reason
   *            for the abort.
   */
  void set_abort_callback(std::function<void(const std::string &)> fun);

  /**
   * Push context levels.
   *
   * Requires that incremental solving has been enabled via
   * `Options::set_option()`.
   *
   * @note Assumptions added via `assume()` are not affected by context level
   *       changes and are only valid until the next `check_sat()` call, no
   *       matter at which level they were assumed.
   *
   * @param nlevels The number of context levels to push.
   *
   * @see
   *   * `Options::set_option`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
   */
  void push(uint32_t nlevels);
  /**
   * Pop context levels.
   *
   * Requires that incremental solving has been enabled via
   * `Options::set_option()`.
   *
   * @note Assumptions added via `assume()` are not affected by context level
   *       changes and are only valid until the next `check_sat()` call, no
   *       matter at which level they were assumed.
   *
   * @param nlevels The number of context levels to pop.
   *
   * @see
   *   * `Options::set_option`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
   */
  void pop(uint32_t nlevels);

  /**
   * Assert formula.
   *
   * @param term The formula to assert.
   */
  void assert_formula(const Term &term);
#if 0
  /**
   * Assume formula.
   *
   * Requires that incremental solving has been enabled via
   * `Options::set_option()`.
   *
   * @note Assumptions added via this function are not affected by context
   *       level changes and are only valid until the next `check_sat()`
   *       call, no matter at which level they were assumed.
   *
   * @param term The formula to assume.
   *
   * @see
   *   * `Options::set_option`
   *   * `is_unsat_assumption`
   *   * `get_unsat_assumptions`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
   */
  void assume_formula(const Term &term);
#endif

  /**
   * Determine if an assumption is an unsat assumption.
   *
   * Unsat assumptions are assumptions that force an input formula to become
   * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
   * failed assumptions in MiniSAT.
   *
   * Requires that incremental solving has been enabled via
   * `Options::set_option()`.
   *
   * Requires that the last `check_sat()` query returned `Result::UNSAT`.
   *
   * @param term The assumption to check for.
   *
   * @return True if given assumption is an unsat assumption.
   *
   * @see
   *   * `Options::set_option`
   *   * `assume_formula`
   *   * `check_sat`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
   */
  bool is_unsat_assumption(const Term &term);
  /**
   * Get the set of unsat assumptions.
   *
   * Unsat assumptions are assumptions that force an input formula to become
   * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
   * failed assumptions in MiniSAT.
   *
   * Requires that incremental solving has been enabled via
   * `Options::set_option()`.
   *
   * Requires that the last `check_sat()` query returned `Result::UNSAT`.
   *
   * @return A vctor with unsat assumptions.
   *
   * @see
   *   * `Options::set_option`
   *   * `assume_formula`
   *   * `check_sat`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
   */
  std::vector<Term> bitwuzla_get_unsat_assumptions();
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
   *   * `assert`
   *   * `check_sat`
   */
  std::vector<Term> bitwuzla_get_unsat_core();
#if 0
  /**
   * Reset all added assumptions.
   *
   * @see
   *   * `assume_formula`
   */
  void reset_assumptions();
#endif

  /**
   * Simplify the current input formula.
   *
   * @note Assumptions are not considered for simplification.
   *
   * @return `Result::SAT` if the input formula was simplified to true,
   *         `Result::UNSAT` if it was simplified to false, and
   *         `Result::UNKNOWN` otherwise.
   *
   * @see
   *   * `assert_formula`
   *   * `Result`
   */
  Result simplify();

  /**
   * Check satisfiability of current input formula.
   *
   * An input formula consists of assertions added via `assert_formula()`.
   * The search for a solution can by guided by making assumptions via
   * `assume_formula()`.
   *
   * @note Assertions and assumptions are combined via Boolean and.  Multiple
   *       calls to this function require enabling incremental solving via
   *       `Options::set_option()`.
   *
   * @return `Result::SAT` if the input formula is satisfiable and
   *         `Result::UNSAT` if it is unsatisfiable, and `Result::UNKNOWN`
   *         when neither satisfiability nor unsatisfiability was determined.
   *         This can happen when this Bitwuzla instance was terminated via a
   *         termination callback.
   *
   * @see
   *   * `assert_formula`
   *   * `assume_formula`
   *   * `Options::set_option`
   *   * `::BITWUZLA_OPT_INCREMENTAL`
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
   * @see `check_sat`
   */
  Term get_value(const Term &term);
  /**
   * Get string representation of the current model value of given bit-vector
   * term.
   * @param term The term to query a model value for.
   * @param base The base in which the resulting string is to be given. 2 for
   *             binary, 10 for decimal, and 16 for hexadecimal.
   * @return String representation of current model value of term \p term.
   */
  std::string get_bv_value(const Term &term, uint8_t base = 2);
  /**
   * Get string of IEEE 754 standard representation of the current model
   * value of given floating-point term.
   *
   * @param term The term to query a model value for.
   * @param base The base in which the resulting string is to be given. 2 for
   *             binary, 10 for decimal, and 16 for hexadecimal.
   * @return String representation of current model value of term \p term.
   */
  std::string get_fp_value(const Term &term, uint8_t base = 2);

  /**
   * Get string representation of the current model value of given rounding
   * mode term.
   *
   * @param term The rounding mode term to query a model value for.
   * @return The rounding mode enum value.
   */
  RoundingMode get_rm_value(const Term &term);

#if 0
  /**
   * Get the current model value of given array term.
   *
   * The string representation of `indices` and `values` can be queried via
   * `get_bv_value()`, `get_fp_value()`, and `get_rm_value()`.
   *
   * @param term The term to query a model value for.
   * @param indices Output parameter, stores list of indices. 1:1 mapping to
   *                `values`, i.e., `index[i] -> value[i]`.
   * @param values Output parameter, stores List of values of size `size`.
   * @param default_value Output parameter, the value of all other indices
   *                      not in `indices` and is set when base array is a
   *                      constant array.
   */
  void get_array_value(const Term &term,
                       std::vector<Term> &indices,
                       std::vector<Term> &values,
                       Term &default_value);

  /**
   * Get the current model value of given function term.
   *
   * The string representation of `args` and `values` can be queried via
   * `get_bv_value()`, `get_fp_value()`, and
   * `get_rm_value()`.
   *
   * @param term   The term to query a model value for.
   * @param args   Output parameter, stores list of argument lists (nested
   * lists);
   * @param values Output parameter, stores list of values.
   *
   * **Usage**
   * ```
   * std::vector<std::vector<Term>> args;
   * std::vector<Term> values;
   * bitwuzla.get_fun_value(f, args, values);
   *
   * for (size_t i = 0; i < size; ++i)
   * {
   *   // args[i] are argument lists of size arity = args[i].size()
   *   for (size_t j = 0; j < arity; ++j)
   *   {
   *     // args[i][j] corresponds to value of jth argument of function f
   *   }
   *   // values[i] corresponds to the value of
   *   // (f args[i][0] ... args[i][arity - 1])
   * }
   * ```
   */
  void get_fun_value(const Term &term,
                     std::vector<std::vector<Term>> args,
                     std::vector<Term> values);

  /**
   * Print a model for the current input formula to the given output stream.
   *
   * Requires that the last `check_sat()` query returned `Result::SAT`.
   *
   * @param out    The output stream.
   * @param format The output format for printing the model.
   *               Either `"btor"` for the BTOR format, or `"smt2"` for the
   *               SMT-LIB v2 format.
   *
   * @see
   *   * `check_sat`
   *   * `Result`
   */
  void print_model(std::ostream &out, const std::string &format);
#endif

  /**
   * Print the current input formula to the given output stream.
   *
   * @param out    The output stream.
   * @param format The output format for printing the formula.
   *               Either `"aiger_ascii"` for the AIGER ascii format,
   *               `"aiger_binary"` for the binary AIGER format, `"btor"` for
   *               the BTOR format, and `"smt2"` for the SMT-LIB v2 format.
   */
  void dump_formula(std::ostream &out, const std::string &format);

  /**
   * Parse input file.
   *
   * The format of the input file is auto detected.
   * Requires that no terms have been created yet.
   *
   * @param infile      The input file stream.
   * @param infile_name The name of the input file.
   * @param error_msg   Output parameter, stores an error message in case a
   *                    parse error occurred.
   * @param status      Output parameter, stores the status of the input in
   *                    case of SMT-LIB v2 input, if given.
   * @param is_smt2     Output parameter, stores true if parsed input file
   *                    has been detected as SMT-LIB v2 input, else false.
   *
   * @return `Result::SAT` if the input formula was simplified to true,
   *         `Result::UNSAT` if it was simplified to false, and
   *         `Result::UNKNOWN` otherwise.
   */
  Result parse(std::ifstream &infile,
               const std::string &infile_name,
               std::string &error_msg,
               Result &status,
               bool &is_smt2);
  /**
   * Parse input file, assumed to be given in the specified format.
   *
   * Requires that no terms have been created yet.
   *
   * @param format      The input format, also used for printing the model.
   *                    Either `"btor"` for the BTOR format, `"btor2"` for
   *                    the BTOR2 format, or `"smt2"` for the SMT-LIB v2
   *                    format.
   * @param infile      The input file stream.
   * @param infile_name The name of the input file.
   * @param error_msg   Output parameter, stores an error message in case a
   *                    parse error occurred.
   * @param status      Output parameter, stores the status of the input in
   *                    case of SMT-LIB v2 input, if given.
   *
   * @return `Result::SAT` if the input formula was simplified to true,
   *         `Result::UNSAT` if it was simplified to false,
   *         and `Result::UNKNOWN` otherwise.
   *
   * @see
   *   * `bitwuzla_parse`
   */
  Result parse(const std::string &format,
               std::ifstream &infile,
               const std::string &infile_name,
               std::string &error_msg,
               Result &status,
               bool &is_smt2);

 private:
  /** The associated solving context. */
  std::unique_ptr<bzla::SolvingContext> d_ctx;
  /** The result of the last check_sat() call. */
  Result d_last_check_sat;
};

/* -------------------------------------------------------------------------- */

/**
 * Create an array sort.
 * @param index The index sort of the array sort.
 * @param element The element sort of the array sort.
 * @return An array sort which maps sort `index` to sort `element`.
 *
 * @see
 *   * `Sort::is_array`
 *   * `Sort::array_get_index`
 *   * `Sort::array_get_element`
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
 *   * `Sort::is_bv`
 *   * `Sort::bv_size`
 */
Sort mk_bv_sort(uint64_t size);

/**
 * Create a floating-point sort of given exponent and significand size.
 * @param exp_size The size of the exponent.
 * @param sig_size The size of the significand (including sign bit).
 * @return A floating-point sort of given format.
 *
 * @see
 *   * `Sort::is_fp`
 *   * `Sort::fp_exp_size`
 *   * `Sort::fp_sig_size`
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
 *   * `Sort::is_fun`
 *   * `Sort::fun_arity`
 *   * `Sort::fun_domain_sorts`
 *   * `Sort::fun_codomain`
 */
Sort mk_fun_sort(const std::vector<Sort> &domain, const Sort &codomain);

/**
 * Create a Roundingmode sort.
 * @return A Roundingmode sort.
 * @see
 *   * `Sort::is_rm`
 */
Sort mk_rm_sort();

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
 *   * `mk_bv_sort`
 */
Term mk_bv_zero(const Sort &sort);

/**
 * Create a bit-vector value one.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value 1 of given sort.
 *
 * @see
 *   * `mk_bv_sort`
 */
Term mk_bv_one(const Sort &sort);

/**
 * Create a bit-vector value where all bits are set to 1.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort
 *         where all bits are set to 1.
 * @see
 *   * `mk_bv_sort`
 */
Term mk_bv_ones(const Sort &sort);

/**
 * Create a bit-vector minimum signed value.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 1 and all remaining bits are set to 0.
 * @see
 *   * `mk_bv_sort`
 */
Term mk_bv_min_signed(const Sort &sort);

/**
 * Create a bit-vector maximum signed value.
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 0 and all remaining bits are set to 1.
 * @see
 *   * `mk_bv_sort`
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
 * @param base The base in which the string is given. 2 for binary, 10 for
 *             decimal, and 16 for hexadecimal.
 *
 * @return A term of kind Kind::VALUE, representing the bit-vector value
 *         of given sort.
 * @see
 *   * `mk_bv_sort`
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
 *   * `mk_bv_sort`
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
 *   * `mk_bv_sort`
 */
Term mk_bv_value_int64(const Sort &sort, int64_t value);

/**
 * Create a floating-point positive zero value (SMT-LIB: `+zero`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive zero value of given
 *         floating-point sort.
 * @see
 *  * `mk_fp_sort`
 */
Term mk_fp_pos_zero(const Sort &sort);

/**
 * Create a floating-point negative zero value (SMT-LIB: `-zero`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative zero value of given
 *         floating-point sort.
 * @see
 *   * `mk_fp_sort`
 */
Term mk_fp_neg_zero(const Sort &sort);

/**
 * Create a floating-point positive infinity value (SMT-LIB: `+oo`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive infinity value of
 *         given floating-point sort.
 * @see
 *   * `mk_fp_sort`
 */
Term mk_fp_pos_inf(const Sort &sort);

/**
 * Create a floating-point negative infinity value (SMT-LIB: `-oo`).
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative infinity value of
 *         given floating-point sort.
 * @see
 *   * `mk_fp_sort`
 */
Term mk_fp_neg_inf(const Sort &sort);

/**
 * Create a floating-point NaN value.
 * @param sort The sort of the value.
 * @return A term representing the floating-point NaN value of given
 *         floating-point sort.
 * @see
 *   * `mk_fp_sort`
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
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param real The decimal string representing a real value.
 *
 * @return A term of kind Kind::VALUE, representing the floating-point
 *         value of given sort.
 *
 * @see
 *   * `mk_fp_sort`
 */
Term mk_fp_value_from_real(const Sort &sort,
                           const Term &rm,
                           const std::string &real);

/**
 * Create a floating-point value from its rational representation, given as a
 * two decimal strings representing the numerator and denominator, with respect
 * to given rounding mode.
 *
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param num The decimal string representing the numerator.
 * @param den The decimal string representing the denominator.
 *
 * @return A term of kind Kind::VALUE, representing the floating-point
 *         value of given sort.
 *
 * @see
 *   * `mk_fp_sort`
 */
Term mk_fp_value_from_rational(const Sort &sort,
                               const Term &rm,
                               const std::string &num,
                               const std::string &den);

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
             const std::vector<uint64_t> indices = {});

/**
 * Create a (first-order) constant of given sort with given symbol.
 *
 * @param sort The sort of the constant.
 * @param symbol The symbol of the constant.
 *
 * @return A term of Kind::CONSTANT, representing the constant.
 *
 * @see
 *   * `mk_array_sort`
 *   * `mk_bool_sort`
 *   * `mk_bv_sort`
 *   * `mk_fp_sort`
 *   * `mk_fun_sort`
 *   * `mk_rm_sort`
 */
Term mk_const(const Sort &sort,
              std::optional<std::reference_wrapper<const std::string>> symbol);

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
 *   * `mk_bool_sort`
 *   * `mk_bv_sort`
 *   * `mk_fp_sort`
 *   * `mk_fun_sort`
 *   * `mk_rm_sort`
 */
Term mk_var(const Sort &sort,
            std::optional<std::reference_wrapper<const std::string>> symbol);

/**
 * Substitute a set of keys with their corresponding values in the given
 * term.
 *
 * @param term The term in which the keys are to be substituted.
 * @param map  The substitution map.
 * @return The resulting term from this substitution.
 */
Term substitute_term(const Term &term,
                     const std::unordered_map<Term, Term> map);

/**
 * Substitute a set of keys with their corresponding values in the set of
 * given terms.
 *
 * The terms in `terms` are replaced with the terms resulting from this
 * substitutions.
 *
 * @param terms_size The size of the set of terms.
 * @param terms The terms in which the keys are to be substituted.
 * @param map_size The size of the substitution map.
 * @param map_keys The keys.
 * @param map_values The mapped values.
 */
void substitute_terms(std::vector<Term> &terms,
                      const std::unordered_map<Term, Term> map);

/* -------------------------------------------------------------------------- */

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

#endif
