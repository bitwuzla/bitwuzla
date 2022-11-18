/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BITWUZLA_API_C_H_INCLUDED
#define BITWUZLA_API_C_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "api/option.h"

/* -------------------------------------------------------------------------- */

#if __cplusplus
extern "C" {
#endif

/* -------------------------------------------------------------------------- */

/** The base for strings representing bit-vector values. */
enum BitwuzlaBVBase
{
  BITWUZLA_BV_BASE_BIN, ///< binary
  BITWUZLA_BV_BASE_DEC, ///< decimal
  BITWUZLA_BV_BASE_HEX, ///< hexadecimal
};
#ifndef DOXYGEN_SKIP
typedef enum BitwuzlaBVBase BitwuzlaBVBase;
#endif

/**
 * The option info struct holds all information about an option, which can
 * be queried via `bitwuzla_get_option_info`.
 *
 * @see
 *   * `bitwuzla_get_option_info`
 */
struct BitwuzlaOptionInfo
{
  /** The Bitwuzla option. */
  BitwuzlaOption opt;
  /** Short option name. */
  const char *shrt;
  /** Long option name. */
  const char *lng;
  /** Option description. */
  const char *desc;
  /** Indicates whether values are numeric or strings. */
  bool is_numeric;

  union
  {
    struct
    {
      /** Current option value. */
      uint32_t cur_val;
      /** Default option value. */
      uint32_t def_val;
      /** Minimum option value. */
      uint32_t min_val;
      /** Maximum option value. */
      uint32_t max_val;
    } numeric;

    struct
    {
      /** Current string option value. */
      const char *cur_val;
      /** Default string option value. */
      const char *def_val;
      /** Number of available string values. */
      size_t num_values;
      /** List of available string values. */
      const char **values;
    } string;
  };
};

#ifndef DOXYGEN_SKIP
typedef struct BitwuzlaOptionInfo BitwuzlaOptionInfo;
#endif

/** The term kind. */
enum BitwuzlaKind
{
  /*! First order constant. */
  BITWUZLA_KIND_CONST,
  /*! Constant array. */
  BITWUZLA_KIND_CONST_ARRAY,
  /*! Value. */
  BITWUZLA_KIND_VAL,
  /*! Bound variable. */
  BITWUZLA_KIND_VAR,

  // operators
  /*! Boolean and.
   *
   *  SMT-LIB: \c and */
  BITWUZLA_KIND_AND,
  /*! Function application. */
  BITWUZLA_KIND_APPLY,
  /*! Array select.
   *
   *  SMT-LIB: \c select */
  BITWUZLA_KIND_ARRAY_SELECT,
  /*! Array store.
   *
   * SMT-LIB: \c store */
  BITWUZLA_KIND_ARRAY_STORE,
  /*! Bit-vector addition.
   *
   *  SMT-LIB: \c bvadd */
  BITWUZLA_KIND_BV_ADD,
  /*! Bit-vector and.
   *
   * SMT-LIB: \c bvand */
  BITWUZLA_KIND_BV_AND,
  /*! Bit-vector arithmetic right shift.
   *
   * SMT-LIB: \c bvashr */
  BITWUZLA_KIND_BV_ASHR,
  /*! Bit-vector comparison.
   *
   * SMT-LIB: \c bvcomp */
  BITWUZLA_KIND_BV_COMP,
  /*! Bit-vector concat.
   *
   * SMT-LIB: \c concat */
  BITWUZLA_KIND_BV_CONCAT,
  /*! Bit-vector decrement.
   *
   * Decrement by one. */
  BITWUZLA_KIND_BV_DEC,
  /*! Bit-vector increment.
   *
   * Increment by one. */
  BITWUZLA_KIND_BV_INC,
  /*! Bit-vector multiplication.
   *
   * SMT-LIB: \c bvmul */
  BITWUZLA_KIND_BV_MUL,
  /*! Bit-vector nand.
   *
   * SMT-LIB: \c bvnand */
  BITWUZLA_KIND_BV_NAND,
  /*! Bit-vector negation (two's complement).
   *
   * SMT-LIB: \c bvneg */
  BITWUZLA_KIND_BV_NEG,
  /*! Bit-vector nor.
   *
   * SMT-LIB: \c bvnor */
  BITWUZLA_KIND_BV_NOR,
  /*! Bit-vector not (one's complement).
   *
   * SMT-LIB: \c bvnot */
  BITWUZLA_KIND_BV_NOT,
  /*! Bit-vector or.
   *
   * SMT-LIB: \c bvor */
  BITWUZLA_KIND_BV_OR,
  /*! Bit-vector and reduction.
   *
   * Bit-wise *and* reduction, all bits are *and*'ed together into a single bit.
   * This corresponds to bit-wise *and* reduction as known from Verilog. */
  BITWUZLA_KIND_BV_REDAND,
  /*! Bit-vector reduce or.
   *
   * Bit-wise *or* reduction, all bits are *or*'ed together into a single bit.
   * This corresponds to bit-wise *or* reduction as known from Verilog. */
  BITWUZLA_KIND_BV_REDOR,
  /*! Bit-vector reduce xor.
   *
   * Bit-wise *xor* reduction, all bits are *xor*'ed together into a single bit.
   * This corresponds to bit-wise *xor* reduction as known from Verilog. */
  BITWUZLA_KIND_BV_REDXOR,
  /*! Bit-vector rotate left (not indexed).
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_left. */
  BITWUZLA_KIND_BV_ROL,
  /*! Bit-vector rotate right.
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_right. */
  BITWUZLA_KIND_BV_ROR,
  /*! Bit-vector signed addition overflow test.
   *
   * Single bit to indicate if signed addition produces an overflow. */
  BITWUZLA_KIND_BV_SADD_OVERFLOW,
  /*! Bit-vector signed division overflow test.
   *
   * Single bit to indicate if signed division produces an overflow. */
  BITWUZLA_KIND_BV_SDIV_OVERFLOW,
  /*! Bit-vector signed division.
   *
   * SMT-LIB: \c bvsdiv */
  BITWUZLA_KIND_BV_SDIV,
  /*! Bit-vector signed greater than or equal.
   *
   * SMT-LIB: \c bvsle */
  BITWUZLA_KIND_BV_SGE,
  /*! Bit-vector signed greater than.
   *
   * SMT-LIB: \c bvslt */
  BITWUZLA_KIND_BV_SGT,
  /*! Bit-vector logical left shift.
   *
   * SMT-LIB: \c bvshl */
  BITWUZLA_KIND_BV_SHL,
  /*! Bit-vector logical right shift.
   *
   * SMT-LIB: \c bvshr */
  BITWUZLA_KIND_BV_SHR,
  /*! Bit-vector signed less than or equal.
   *
   * SMT-LIB: \c bvsle */
  BITWUZLA_KIND_BV_SLE,
  /*! Bit-vector signed less than.
   *
   * SMT-LIB: \c bvslt */
  BITWUZLA_KIND_BV_SLT,
  /*! Bit-vector signed modulo.
   *
   * SMT-LIB: \c bvsmod */
  BITWUZLA_KIND_BV_SMOD,
  /*! Bit-vector signed multiplication overflow test.
   *
   * SMT-LIB: \c bvsmod */
  BITWUZLA_KIND_BV_SMUL_OVERFLOW,
  /*! Bit-vector signed remainder.
   *
   * SMT-LIB: \c bvsrem */
  BITWUZLA_KIND_BV_SREM,
  /*! Bit-vector signed subtraction overflow test.
   *
   * Single bit to indicate if signed subtraction produces an overflow. */
  BITWUZLA_KIND_BV_SSUB_OVERFLOW,
  /*! Bit-vector subtraction.
   *
   * SMT-LIB: \c bvsub */
  BITWUZLA_KIND_BV_SUB,
  /*! Bit-vector unsigned addition overflow test.
   *
   * Single bit to indicate if unsigned addition produces an overflow. */
  BITWUZLA_KIND_BV_UADD_OVERFLOW,
  /*! Bit-vector unsigned division.
   *
   * SMT-LIB: \c bvudiv */
  BITWUZLA_KIND_BV_UDIV,
  /*! Bit-vector unsigned greater than or equal.
   *
   * SMT-LIB: \c bvuge */
  BITWUZLA_KIND_BV_UGE,
  /*! Bit-vector unsigned greater than.
   *
   * SMT-LIB: \c bvugt */
  BITWUZLA_KIND_BV_UGT,
  /*! Bit-vector unsigned less than or equal.
   *
   * SMT-LIB: \c bvule */
  BITWUZLA_KIND_BV_ULE,
  /*! Bit-vector unsigned less than.
   *
   * SMT-LIB: \c bvult */
  BITWUZLA_KIND_BV_ULT,
  /*! Bit-vector unsigned multiplication overflow test.
   *
   * Single bit to indicate if unsigned multiplication produces an overflow. */
  BITWUZLA_KIND_BV_UMUL_OVERFLOW,
  /*! Bit-vector unsigned remainder.
   *
   * SMT-LIB: \c bvurem */
  BITWUZLA_KIND_BV_UREM,
  /*! Bit-vector unsigned subtraction overflow test.
   *
   * Single bit to indicate if unsigned subtraction produces an overflow. */
  BITWUZLA_KIND_BV_USUB_OVERFLOW,
  /*! Bit-vector xnor.
   *
   * SMT-LIB: \c bvxnor */
  BITWUZLA_KIND_BV_XNOR,
  /*! Bit-vector xor.
   *
   * SMT-LIB: \c bvxor */
  BITWUZLA_KIND_BV_XOR,
  /*! Disequality.
   *
   * SMT-LIB: \c distinct */
  BITWUZLA_KIND_DISTINCT,
  /*! Equality.
   *
   * SMT-LIB: \c = */
  BITWUZLA_KIND_EQUAL,
  /*! Existential quantification.
   *
   * SMT-LIB: \c exists */
  BITWUZLA_KIND_EXISTS,
  /*! Universal quantification.
   *
   * SMT-LIB: \c forall */
  BITWUZLA_KIND_FORALL,
  /*! Floating-point absolute value.
   *
   * SMT-LIB: \c fp.abs */
  BITWUZLA_KIND_FP_ABS,
  /*! Floating-point addition.
   *
   * SMT-LIB: \c fp.add */
  BITWUZLA_KIND_FP_ADD,
  /*! Floating-point division.
   *
   * SMT-LIB: \c fp.div */
  BITWUZLA_KIND_FP_DIV,
  /*! Floating-point equality.
   *
   * SMT-LIB: \c fp.eq */
  BITWUZLA_KIND_FP_EQ,
  /*! Floating-point fused multiplcation and addition.
   *
   * SMT-LIB: \c fp.fma */
  BITWUZLA_KIND_FP_FMA,
  /*! Floating-point IEEE 754 value.
   *
   * SMT-LIB: \c fp */
  BITWUZLA_KIND_FP_FP,
  /*! Floating-point greater than or equal.
   *
   * SMT-LIB: \c fp.geq */
  BITWUZLA_KIND_FP_GEQ,
  /*! Floating-point greater than.
   *
   * SMT-LIB: \c fp.gt */
  BITWUZLA_KIND_FP_GT,
  /*! Floating-point is infinity tester.
   *
   * SMT-LIB: \c fp.isInfinite */
  BITWUZLA_KIND_FP_IS_INF,
  /*! Floating-point is Nan tester.
   *
   * SMT-LIB: \c fp.isNaN */
  BITWUZLA_KIND_FP_IS_NAN,
  /*! Floating-point is negative tester.
   *
   * SMT-LIB: \c fp.isNegative */
  BITWUZLA_KIND_FP_IS_NEG,
  /*! Floating-point is normal tester.
   *
   * SMT-LIB: \c fp.isNormal */
  BITWUZLA_KIND_FP_IS_NORMAL,
  /*! Floating-point is positive tester.
   *
   * SMT-LIB: \c fp.isPositive */
  BITWUZLA_KIND_FP_IS_POS,
  /*! Floating-point is subnormal tester.
   *
   * SMT-LIB: \c fp.isSubnormal */
  BITWUZLA_KIND_FP_IS_SUBNORMAL,
  /*! Floating-point is zero tester.
   *
   * SMT-LIB: \c fp.isZero */
  BITWUZLA_KIND_FP_IS_ZERO,
  /*! Floating-point less than or equal.
   *
   * SMT-LIB: \c fp.leq */
  BITWUZLA_KIND_FP_LEQ,
  /*! Floating-point less than.
   *
   * SMT-LIB: \c fp.lt */
  BITWUZLA_KIND_FP_LT,
  /*! Floating-point max.
   *
   * SMT-LIB: \c fp.max */
  BITWUZLA_KIND_FP_MAX,
  /*! Floating-point min.
   *
   * SMT-LIB: \c fp.min */
  BITWUZLA_KIND_FP_MIN,
  /*! Floating-point multiplcation.
   *
   * SMT-LIB: \c fp.mul */
  BITWUZLA_KIND_FP_MUL,
  /*! Floating-point negation.
   *
   * SMT-LIB: \c fp.neg */
  BITWUZLA_KIND_FP_NEG,
  /*! Floating-point remainder.
   *
   * SMT-LIB: \c fp.rem */
  BITWUZLA_KIND_FP_REM,
  /*! Floating-point round to integral.
   *
   * SMT-LIB: \c fp.roundToIntegral */
  BITWUZLA_KIND_FP_RTI,
  /*! Floating-point round to square root.
   *
   * SMT-LIB: \c fp.sqrt */
  BITWUZLA_KIND_FP_SQRT,
  /*! Floating-point round to subtraction.
   *
   * SMT-LIB: \c fp.sqrt */
  BITWUZLA_KIND_FP_SUB,
  /*! Boolean if and only if.
   *
   * SMT-LIB: \c = */
  BITWUZLA_KIND_IFF,
  /*! Boolean implies.
   *
   * SMT-LIB: \c => */
  BITWUZLA_KIND_IMPLIES,
  /*! If-then-else.
   *
   * SMT-LIB: \c ite */
  BITWUZLA_KIND_ITE,
  /*! Lambda. */
  BITWUZLA_KIND_LAMBDA,
  /*! Boolean not.
   *
   * SMT-LIB: \c not */
  BITWUZLA_KIND_NOT,
  /*! Boolean or.
   *
   * SMT-LIB: \c or */
  BITWUZLA_KIND_OR,
  /*! Boolean xor.
   *
   * SMT-LIB: \c xor */
  BITWUZLA_KIND_XOR,

  // indexed
  /*! Bit-vector extract.
   *
   * SMT-LIB: \c extract (indexed) */
  BITWUZLA_KIND_BV_EXTRACT,
  /*! Bit-vector repeat.
   *
   * SMT-LIB: \c repeat (indexed) */
  BITWUZLA_KIND_BV_REPEAT,
  /*! Bit-vector rotate left by integer.
   *
   * SMT-LIB: \c rotate_left (indexed) */
  BITWUZLA_KIND_BV_ROLI,
  /*! Bit-vector rotate right by integer.
   *
   * SMT-LIB: \c rotate_right (indexed) */
  BITWUZLA_KIND_BV_RORI,
  /*! Bit-vector sign extend.
   *
   * SMT-LIB: \c sign_extend (indexed) */
  BITWUZLA_KIND_BV_SIGN_EXTEND,
  /*! Bit-vector zero extend.
   *
   * SMT-LIB: \c zero_extend (indexed) */
  BITWUZLA_KIND_BV_ZERO_EXTEND,
  /*! Floating-point to_fp from IEEE 754 bit-vector.
   *
   * SMT-LIB: \c to_fp (indexed) */
  BITWUZLA_KIND_FP_TO_FP_FROM_BV,
  /*! Floating-point to_fp from floating-point.
   *
   * SMT-LIB: \c to_fp (indexed) */
  BITWUZLA_KIND_FP_TO_FP_FROM_FP,
  /*! Floating-point to_fp from signed bit-vector value.
   *
   * SMT-LIB: \c to_fp (indexed) */
  BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
  /*! Floating-point to_fp from unsigned bit-vector value.
   *
   * SMT-LIB: \c to_fp_unsigned (indexed) */
  BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
  /*! Floating-point to_sbv.
   *
   * SMT-LIB: \c fp.to_sbv (indexed) */
  BITWUZLA_KIND_FP_TO_SBV,
  /*! Floating-point to_ubv.
   *
   * SMT-LIB: \c fp.to_ubv (indexed) */
  BITWUZLA_KIND_FP_TO_UBV,
#ifndef DOXYGEN_SKIP
  BITWUZLA_NUM_KINDS,
#endif
};
#ifndef DOXYGEN_SKIP
typedef enum BitwuzlaKind BitwuzlaKind;
#endif

/**
 * Get the string representation of a term kind.
 * @return A string representation of the given term kind.
 */
const char *bitwuzla_kind_to_string(BitwuzlaKind kind);

/** A satisfiability result. */
enum BitwuzlaResult
{
  BITWUZLA_SAT     = 10, ///< sat
  BITWUZLA_UNSAT   = 20, ///< unsat
  BITWUZLA_UNKNOWN = 0,  ///< unknown
};
#ifndef DOXYGEN_SKIP
typedef enum BitwuzlaResult BitwuzlaResult;
#endif

/**
 * Get the string representation of a result.
 * @return A string representation of the given result.
 */
const char *bitwuzla_result_to_string(BitwuzlaResult result);

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
enum BitwuzlaRoundingMode
{
  /*!
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   *
   * SMT-LIB: \c RNE \c roundNearestTiesToEven
   */
  BITWUZLA_RM_RNE = 0,
  /*!
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   *
   * SMT-LIB: \c RNA \c roundNearestTiesToAway
   */
  BITWUZLA_RM_RNA = 1,
  /*!
   * Round towards negative infinity (-oo).
   * The result shall be the format’s floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   *
   * SMT-LIB: \c RTN \c roundTowardNegative
   */
  BITWUZLA_RM_RTN = 2,
  /*!
   * Round towards positive infinity (+oo).
   * The result shall be the format’s floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   *
   * SMT-LIB: \c RTP \c roundTowardPositive
   */
  BITWUZLA_RM_RTP = 3,
  /*!
   * Round towards zero.
   * The result shall be the format’s floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   *
   * SMT-LIB: \c RTZ \c roundTowardZero
   */
  BITWUZLA_RM_RTZ = 4,
#ifndef DOXYGEN_SKIP
  BITWUZLA_RM_MAX = 5,
#endif
};
#ifndef DOXYGEN_SKIP
typedef enum BitwuzlaRoundingMode BitwuzlaRoundingMode;
#endif

/**
 * Get the string representation of a rounding mode.
 * @return A string representation of the rounding mode.
 */
const char *bitwuzla_rm_to_string(BitwuzlaRoundingMode rm);

/** The Bitwuzla solver. */
typedef struct Bitwuzla Bitwuzla;
/** A Bitwuzla term. */
typedef struct BitwuzlaTerm BitwuzlaTerm;
/** A Bitwuzla sort. */
typedef struct BitwuzlaSort BitwuzlaSort;

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

/**
 * Create a new Bitwuzla instance.
 *
 * The returned instance must be deleted via `bitwuzla_delete()`.
 *
 * @return A pointer to the created Bitwuzla instance.
 *
 * @see
 *   * `bitwuzla_delete`
 */
Bitwuzla *bitwuzla_new(void);

/**
 * Delete a Bitwuzla instance.
 *
 * The given instance must have been created via `bitwuzla_new()`.
 *
 * @param bitwuzla The Bitwuzla instance to delete.
 *
 * @see
 *   * `bitwuzla_new`
 */
void bitwuzla_delete(Bitwuzla *bitwuzla);

/**
 * Reset a Bitwuzla instance.
 *
 * This deletes the given instance and creates a new instance in place.
 * The given instance must have been created via `bitwuzla_new()`.
 *
 * @note All sorts and terms associated with the given instance are released
 *       and thus invalidated.
 *
 * @param bitwuzla The Bitwuzla instance to reset.
 *
 * @see
 *   * `bitwuzla_new`
 */
void bitwuzla_reset(Bitwuzla *bitwuzla);

/**
 * Get copyright information.
 *
 * @param bitwuzla The Bitwuzla instance.
 */
const char *bitwuzla_copyright(Bitwuzla *bitwuzla);

/**
 * Get version information.
 *
 * @param bitwuzla The Bitwuzla instance.
 */
const char *bitwuzla_version(Bitwuzla *bitwuzla);

/**
 * Get git information.
 *
 * @param bitwuzla The Bitwuzla instance.
 */
const char *bitwuzla_git_id(Bitwuzla *bitwuzla);

/**
 * If termination callback function has been configured via
 * `bitwuzla_set_termination_callback()`, call this termination function.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return True if `bitwuzla` has been terminated.
 *
 * @see
 *   * `bitwuzla_set_termination_callback`
 *   * `bitwuzla_get_termination_callback_state`
 */
bool bitwuzla_terminate(Bitwuzla *bitwuzla);

/**
 * Configure a termination callback function.
 *
 * The `state` of the callback can be retrieved via
 * `bitwuzla_get_termination_callback_state()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param fun The callback function, returns a value != 0 if `bitwuzla` has
 *            been terminated.
 * @param state The argument to the callback function.
 *
 * @see
 *   * `bitwuzla_terminate`
 *   * `bitwuzla_get_termination_callback_state`
 */
void bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                       int32_t (*fun)(void *),
                                       void *state);

/**
 * Get the state of the termination callback function.
 *
 * The returned object representing the state of the callback corresponds to
 * the `state` configured as argument to the callback function via
 * `bitwuzla_set_termination_callback()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return The object passed as argument `state` to the callback function.
 *
 * @see
 *   * `bitwuzla_terminate`
 *   * `bitwuzla_set_termination_callback`
 */
void *bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla);

/**
 * Configure an abort callback function, which is called instead of exit
 * on abort conditions.
 *
 * @note This function is not thread safe (the function pointer is maintained
 *       as a global variable). It you use threading, make sure to set the
 *       abort callback prior to creating threads.
 *
 * @param fun The callback function, the argument `msg` explains the reason
 *            for the abort.
 */
void bitwuzla_set_abort_callback(void (*fun)(const char *msg));

/**
 * Set option.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 * @param val The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 */
void bitwuzla_set_option(Bitwuzla *bitwuzla,
                         BitwuzlaOption option,
                         uint32_t val);

/**
 * Set option value for string options.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 * @param val The option string value.
 *
 * @see
 *   * `BitwuzlaOption`
 */
void bitwuzla_set_option_str(Bitwuzla *bitwuzla,
                             BitwuzlaOption option,
                             const char *val);

/**
 * Get the current value of an option.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 *
 * @return The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 */
uint32_t bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option);

/**
 * Get the current value of an option as a string if option can be configured
 * via a string value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 *
 * @return The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 *   * `bitwuzla_set_option_str`
 */
const char* bitwuzla_get_option_str(Bitwuzla *bitwuzla, BitwuzlaOption option);

/**
 * Get the details of an option.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 * @param info The option info to populate, will be valid until the next
 *             `bitwuzla_get_option_info` call.
 *
 * @see
 *   * `BitwuzlaOptionInfo`
 */
void bitwuzla_get_option_info(Bitwuzla *bitwuzla,
                              BitwuzlaOption option,
                              BitwuzlaOptionInfo *info);

/**
 * Create an array sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param index The index sort of the array sort.
 * @param element The element sort of the array sort.
 *
 * @return An array sort which maps sort `index` to sort `element`.
 *
 * @see
 *   * `bitwuzla_sort_is_array`
 *   * `bitwuzla_sort_array_get_index`
 *   * `bitwuzla_sort_array_get_element`
 *   * `bitwuzla_term_is_array`
 *   * `bitwuzla_term_array_get_index_sort`
 *   * `bitwuzla_term_array_get_element_sort`
 */
const BitwuzlaSort *bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                                           const BitwuzlaSort *index,
                                           const BitwuzlaSort *element);

/**
 * Create a Boolean sort.
 *
 * @note A Boolean sort is a bit-vector sort of size 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A Boolean sort.
 */
const BitwuzlaSort *bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla);

/**
 * Create a bit-vector sort of given size.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size The size of the bit-vector sort.
 *
 * @return A bit-vector sort of given size.
 *
 * @see
 *   * `bitwuzla_sort_is_bv`
 *   * `bitwuzla_sort_bv_get_size`
 *   * `bitwuzla_term_is_bv`
 *   * `bitwuzla_term_bv_get_size`
 */
const BitwuzlaSort *bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size);

/**
 * Create a floating-point sort of given exponent and significand size.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param exp_size The size of the exponent.
 * @param sig_size The size of the significand (including sign bit).
 *
 * @return A floating-point sort of given format.
 *
 * @see
 *   * `bitwuzla_sort_is_fp`
 *   * `bitwuzla_sort_fp_get_exp_size`
 *   * `bitwuzla_sort_fp_get_sig_size`
 *   * `bitwuzla_term_is_fp`
 *   * `bitwuzla_term_fp_get_exp_size`
 *   * `bitwuzla_term_fp_get_sig_size`
 */
const BitwuzlaSort *bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla,
                                        uint32_t exp_size,
                                        uint32_t sig_size);

/**
 * Create a function sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param arity The number of arguments to the function.
 * @param domain The domain sorts (the sorts of the arguments). The number of
 *               sorts in this vector must match `arity`.
 * @param codomain The codomain sort (the sort of the return value).
 *
 * @return A function sort of given domain and codomain sorts.
 *
 * @see
 *   * `bitwuzla_sort_is_fun`
 *   * `bitwuzla_sort_fun_get_arity`
 *   * `bitwuzla_sort_fun_get_domain_sorts`
 *   * `bitwuzla_sort_fun_get_codomain`
 *   * `bitwuzla_term_is_fun`
 *   * `bitwuzla_term_fun_get_arity`
 *   * `bitwuzla_term_fun_get_domain_sorts`
 *   * `bitwuzla_term_fun_get_codomain_sort`
 */
const BitwuzlaSort *bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                                         uint32_t arity,
                                         const BitwuzlaSort *domain[],
                                         const BitwuzlaSort *codomain);

/**
 * Create a Roundingmode sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A Roundingmode sort.
 *
 * @see
 *   * `bitwuzla_sort_is_rm`
 *   * `bitwuzla_term_is_rm`
 */
const BitwuzlaSort *bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla);

/**
 * Create a true value.
 *
 * @note This creates a bit-vector value 1 of size 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A term representing the bit-vector value 1 of size 1.
 */
const BitwuzlaTerm *bitwuzla_mk_true(Bitwuzla *bitwuzla);

/**
 * Create a false value.
 *
 * @note This creates a bit-vector value 0 of size 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A term representing the bit-vector value 0 of size 1.
 */
const BitwuzlaTerm *bitwuzla_mk_false(Bitwuzla *bitwuzla);

/**
 * Create a bit-vector value zero.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value 0 of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla,
                                        const BitwuzlaSort *sort);

/**
 * Create a bit-vector value one.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value 1 of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_one(Bitwuzla *bitwuzla,
                                       const BitwuzlaSort *sort);

/**
 * Create a bit-vector value where all bits are set to 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value of given sort
 *         where all bits are set to 1.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla,
                                        const BitwuzlaSort *sort);

/**
 * Create a bit-vector minimum signed value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 1 and all remaining bits are set to 0.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla,
                                              const BitwuzlaSort *sort);
/**
 * Create a bit-vector maximum signed value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 0 and all remaining bits are set to 1.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla,
                                              const BitwuzlaSort *sort);

/**
 * Create a floating-point positive zero value (SMT-LIB: `+zero`).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point positive zero value of given
 *         floating-point sort.
 *
 * @see
 *  * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla,
                                            const BitwuzlaSort *sort);

/**
 * Create a floating-point negative zero value (SMT-LIB: `-zero`).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point negative zero value of given
 *         floating-point sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla,
                                            const BitwuzlaSort *sort);

/**
 * Create a floating-point positive infinity value (SMT-LIB: `+oo`).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point positive infinity value of
 *         given floating-point sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla,
                                           const BitwuzlaSort *sort);

/**
 * Create a floating-point negative infinity value (SMT-LIB: `-oo`).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point negative infinity value of
 *         given floating-point sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla,
                                           const BitwuzlaSort *sort);

/**
 * Create a floating-point NaN value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point NaN value of given
 *         floating-point sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla,
                                       const BitwuzlaSort *sort);

/**
 * Create a bit-vector value from its string representation.
 *
 * Parameter `base` determines the base of the string representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param value A string representing the value.
 * @param base The base in which the string is given.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 *   * `BitwuzlaBVBase`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                                         const BitwuzlaSort *sort,
                                         const char *value,
                                         BitwuzlaBVBase base);

/**
 * Create a bit-vector value from its unsigned integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
                                                const BitwuzlaSort *sort,
                                                uint64_t value);

/**
 * Create a bit-vector value from its signed integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_bv_value_int64(Bitwuzla *bitwuzla,
                                               const BitwuzlaSort *sort,
                                               int64_t value);

/**
 * Create a floating-point value from its IEEE 754 standard representation
 * given as three bit-vector values representing the sign bit, the exponent and
 * the significand.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param bv_sign The sign bit.
 * @param bv_exponent The exponent bit-vector value.
 * @param bv_significand The significand bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the floating-point
 *         value.
 */
const BitwuzlaTerm *bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                                         const BitwuzlaTerm *bv_sign,
                                         const BitwuzlaTerm *bv_exponent,
                                         const BitwuzlaTerm *bv_significand);

/**
 * Create a floating-point value from its real representation, given as a
 * decimal string, with respect to given rounding mode.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param real The decimal string representing a real value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the floating-point
 *         value of given sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_value_from_real(Bitwuzla *bitwuzla,
                                                   const BitwuzlaSort *sort,
                                                   const BitwuzlaTerm *rm,
                                                   const char *real);

/**
 * Create a floating-point value from its rational representation, given as a
 * two decimal strings representing the numerator and denominator, with respect
 * to given rounding mode.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param num The decimal string representing the numerator.
 * @param den The decimal string representing the denominator.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the floating-point
 *         value of given sort.
 *
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_fp_value_from_rational(Bitwuzla *bitwuzla,
                                                       const BitwuzlaSort *sort,
                                                       const BitwuzlaTerm *rm,
                                                       const char *num,
                                                       const char *den);

/**
 * Create a rounding mode value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param rm The rounding mode value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the rounding mode
 *         value.
 *
 * @see
 *   * `BitwuzlaRoundingMode`
 */
const BitwuzlaTerm *bitwuzla_mk_rm_value(Bitwuzla *bitwuzla,
                                         BitwuzlaRoundingMode rm);

/**
 * Create a term of given kind with one argument term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg The argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                                      BitwuzlaKind kind,
                                      const BitwuzlaTerm *arg);

/**
 * Create a term of given kind with two argument terms.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg0 The first argument to the operator.
 * @param arg1 The second argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                                      BitwuzlaKind kind,
                                      const BitwuzlaTerm *arg0,
                                      const BitwuzlaTerm *arg1);

/**
 * Create a term of given kind with three argument terms.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg0 The first argument to the operator.
 * @param arg1 The second argument to the operator.
 * @param arg2 The third argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                                      BitwuzlaKind kind,
                                      const BitwuzlaTerm *arg0,
                                      const BitwuzlaTerm *arg1,
                                      const BitwuzlaTerm *arg2);

/**
 * Create a term of given kind with the given argument terms.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param argc The number of argument terms.
 * @param args The argument terms.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term(Bitwuzla *bitwuzla,
                                     BitwuzlaKind kind,
                                     uint32_t argc,
                                     const BitwuzlaTerm *args[]);

/**
 * Create an indexed term of given kind with one argument term and one index.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg The argument term.
 * @param idx The index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
                                               BitwuzlaKind kind,
                                               const BitwuzlaTerm *arg,
                                               uint32_t idx);

/**
 * Create an indexed term of given kind with one argument term and two indices.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg The argument term.
 * @param idx0 The first index.
 * @param idx1 The second index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                                               BitwuzlaKind kind,
                                               const BitwuzlaTerm *arg,
                                               uint32_t idx0,
                                               uint32_t idx1);

/**
 * Create an indexed term of given kind with two argument terms and one index.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg0 The first argument term.
 * @param arg1 The second argument term.
 * @param idx The index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
                                               BitwuzlaKind kind,
                                               const BitwuzlaTerm *arg0,
                                               const BitwuzlaTerm *arg1,
                                               uint32_t idx);

/**
 * Create an indexed term of given kind with two argument terms and two indices.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg0 The first argument term.
 * @param arg1 The second argument term.
 * @param idx0 The first index.
 * @param idx1 The second index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
                                               BitwuzlaKind kind,
                                               const BitwuzlaTerm *arg0,
                                               const BitwuzlaTerm *arg1,
                                               uint32_t idx0,
                                               uint32_t idx1);

/**
 * Create an indexed term of given kind with the given argument terms and
 * indices.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param argc The number of argument terms.
 * @param args The argument terms.
 * @param idxc The number of indices.
 * @param idxs The indices.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
const BitwuzlaTerm *bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                                             BitwuzlaKind kind,
                                             uint32_t argc,
                                             const BitwuzlaTerm *args[],
                                             uint32_t idxc,
                                             const uint32_t idxs[]);

/**
 * Create a (first-order) constant of given sort with given symbol.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the constant.
 * @param symbol The symbol of the constant.
 *
 * @return A term of kind BITWUZLA_KIND_CONST, representing the constant.
 *
 * @see
 *   * `bitwuzla_mk_array_sort`
 *   * `bitwuzla_mk_bool_sort`
 *   * `bitwuzla_mk_bv_sort`
 *   * `bitwuzla_mk_fp_sort`
 *   * `bitwuzla_mk_fun_sort`
 *   * `bitwuzla_mk_rm_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_const(Bitwuzla *bitwuzla,
                                      const BitwuzlaSort *sort,
                                      const char *symbol);

/**
 * Create a one-dimensional constant array of given sort, initialized with
 * given value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the array.
 * @param value The term to initialize the elements of the array with.
 *
 * @return A term of kind BITWUZLA_KIND_CONST_ARRAY, representing a constant
 *         array of given sort.
 *
 * @see
 *   * `bitwuzla_mk_array_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                                            const BitwuzlaSort *sort,
                                            const BitwuzlaTerm *value);

/**
 * Create a variable of given sort with given symbol.
 *
 * @note This creates a variable to be bound by quantifiers or lambdas.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the variable.
 * @param symbol The symbol of the variable.
 *
 * @return A term of kind BITWUZLA_KIND_VAR, representing the variable.
 *
 * @see
 *   * `bitwuzla_mk_bool_sort`
 *   * `bitwuzla_mk_bv_sort`
 *   * `bitwuzla_mk_fp_sort`
 *   * `bitwuzla_mk_fun_sort`
 *   * `bitwuzla_mk_rm_sort`
 */
const BitwuzlaTerm *bitwuzla_mk_var(Bitwuzla *bitwuzla,
                                    const BitwuzlaSort *sort,
                                    const char *symbol);

/**
 * Push context levels.
 *
 * Requires that incremental solving has been enabled via
 * `bitwuzla_set_option()`.
 *
 * @note Assumptions added via this `bitwuzla_assume()` are not affected by
 *       context level changes and are only valid until the next
 *       `bitwuzla_check_sat()` call, no matter at which level they were
 *       assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to push.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 */
void bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels);

/**
 * Pop context levels.
 *
 * Requires that incremental solving has been enabled via
 * `bitwuzla_set_option()`.
 *
 * @note Assumptions added via this `bitwuzla_assume()` are not affected by
 *       context level changes and are only valid until the next
 *       `bitwuzla_check_sat()` call, no matter at which level they were
 *       assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to pop.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 */
void bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels);

/**
 * Assert formula.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The formula to assert.
 */
void bitwuzla_assert(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Assume formula.
 *
 * Requires that incremental solving has been enabled via
 * `bitwuzla_set_option()`.
 *
 * @note Assumptions added via this function are not affected by context level
 *       changes and are only valid until the next `bitwuzla_check_sat()` call,
 *       no matter at which level they were assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The formula to assume.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `bitwuzla_is_unsat_assumption`
 *   * `bitwuzla_get_unsat_assumptions`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 */
void bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Determine if an assumption is an unsat assumption.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that incremental solving has been enabled via
 * `bitwuzla_set_option()`.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The assumption to check for.
 *
 * @return True if given assumption is an unsat assumption.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `bitwuzla_assume`
 *   * `bitwuzla_check_sat`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 */
bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Get the set of unsat assumptions.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that incremental solving has been enabled via
 * `bitwuzla_set_option()`.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assumptions of size `size`.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `bitwuzla_assume`
 *   * `bitwuzla_check_sat`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 */
const BitwuzlaTerm **bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla,
                                                    size_t *size);

/**
 * Get the set unsat core (unsat assertions).
 *
 * The unsat core consists of the set of assertions that force an input formula
 * to become unsatisfiable.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assertions of size `size`.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `bitwuzla_check_sat`
 */
const BitwuzlaTerm **bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size);

/**
 * Assert all added assumptions.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @see
 *   * `bitwuzla_assume`
 */
void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla);

/**
 * Reset all added assumptions.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @see
 *   * `bitwuzla_assume`
 */
void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla);

/**
 * Simplify the current input formula.
 *
 * @note Assumptions are not considered for simplification.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return `::BITWUZLA_SAT` if the input formula was simplified to true,
 *         `::BITWUZLA_UNSAT` if it was simplified to false, and
 *         `::BITWUZLA_UNKNOWN` otherwise.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `BitwuzlaResult`
 */
BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla);

/**
 * Check satisfiability of current input formula.
 *
 * An input formula consists of assertions added via `bitwuzla_assert()`.
 * The search for a solution can by guided by making assumptions via
 * `bitwuzla_assume()`.
 *
 * @note Assertions and assumptions are combined via Boolean and.  Multiple
 *       calls to this function require enabling incremental solving via
 *       `bitwuzla_set_option()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return `::BITWUZLA_SAT` if the input formula is satisfiable and
 *         `::BITWUZLA_UNSAT` if it is unsatisfiable, and `::BITWUZLA_UNKNOWN`
 *         when neither satisfiability nor unsatisfiability was determined.
 *         This can happen when `bitwuzla` was terminated via a termination
 *         callback.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `bitwuzla_assume`
 *   * `bitwuzla_set_option`
 *   * `::BITWUZLA_OPT_INCREMENTAL`
 *   * `BitwuzlaResult`
 */
BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

/**
 * Get a term representing the model value of a given term.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_SAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 *
 * @return A term representing the model value of term `term`.
 *
 * @see `bitwuzla_check_sat`
 */
const BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla,
                                       const BitwuzlaTerm *term);

/**
 * Get string representation of the current model value of given bit-vector
 * term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 *
 * @return Binary string representation of current model value of term \p term.
 *         Return value is valid until next `bitwuzla_get_bv_value` call.
 */
const char *bitwuzla_get_bv_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Get string of IEEE 754 standard representation of the current model value of
 * given floating-point term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 * @param sign Binary string representation of the sign bit.
 * @param exponent Binary string representation of the exponent bit-vector
 *        value.
 * @param significand Binary string representation of the significand
 *        bit-vector value.
 */
void bitwuzla_get_fp_value(Bitwuzla *bitwuzla,
                           const BitwuzlaTerm *term,
                           const char **sign,
                           const char **exponent,
                           const char **significand);

/**
 * Get string representation of the current model value of given rounding mode
 * term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The rounding mode term to query a model value for.
 *
 * @return String representation of rounding mode (RNA, RNE, RTN, RTP, RTZ).
 */
const char *bitwuzla_get_rm_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Get the current model value of given array term.
 *
 * The string representation of `indices` and `values` can be queried via
 * `bitwuzla_get_bv_value()`, `bitwuzla_get_fp_value()`, and
 * `bitwuzla_get_rm_value()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 * @param indices List of indices of size `size`. 1:1 mapping to `values`,
 *                i.e., `index[i] -> value[i]`.
 * @param values List of values of size `size`.
 * @param size Size of `indices` and `values` list.
 * @param default_value The value of all other indices not in `indices` and
 *                      is set when base array is a constant array.
 */
void bitwuzla_get_array_value(Bitwuzla *bitwuzla,
                              const BitwuzlaTerm *term,
                              const BitwuzlaTerm ***indices,
                              const BitwuzlaTerm ***values,
                              size_t *size,
                              const BitwuzlaTerm **default_value);

/**
 * Get the current model value of given function term.
 *
 * The string representation of `args` and `values` can be queried via
 * `bitwuzla_get_bv_value()`, `bitwuzla_get_fp_value()`, and
 * `bitwuzla_get_rm_value()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 * @param args List of argument lists (nested lists) of size `size`. Each
 *             argument list is of size `arity`.
 * @param arity Size of each argument list in `args`.
 * @param values List of values of size `size`.
 * @param size Size of `indices` and `values` list.
 *
 * **Usage**
 * ```
 * size_t arity, size;
 * BitwuzlaTerm ***args, **values;
 * bitwuzla_get_fun_value(bzla, f, &args, &arity, &values, &size);
 *
 * for (size_t i = 0; i < size; ++i)
 * {
 *   // args[i] are argument lists of size arity
 *   for (size_t j = 0; j < arity; ++j)
 *   {
 *     // args[i][j] corresponds to value of jth argument of function f
 *   }
 *   // values[i] corresponds to the value of
 *   // (f args[i][0] ... args[i][arity - 1])
 * }
 * ```
 *
 */
void bitwuzla_get_fun_value(Bitwuzla *bitwuzla,
                            const BitwuzlaTerm *term,
                            const BitwuzlaTerm ****args,
                            size_t *arity,
                            const BitwuzlaTerm ***values,
                            size_t *size);

/**
 * Print a model for the current input formula.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_SAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The output format for printing the model. Either `"btor"` for
 *               the BTOR format, or `"smt2"` for the SMT-LIB v2 format.
 * @param file The file to print the model to.
 *
 * @see
 *   * `bitwuzla_check_sat`
 */
void bitwuzla_print_model(Bitwuzla *bitwuzla, const char *format, FILE *file);

/**
 * Print the current input formula.
 *
 * Requires that incremental solving is not enabled.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The output format for printing the formula. Either
 *               `"aiger_ascii"` for the AIGER ascii format, `"aiger_binary"`
 *               for the binary AIGER format, `"btor"` for the BTOR format, or
 *               `"smt2"` for the SMT-LIB v2 format.
 * @param file The file to print the formula to.
 */
void bitwuzla_dump_formula(Bitwuzla *bitwuzla, const char *format, FILE *file);

/**
 * Parse input file.
 *
 * The format of the input file is auto detected.  
 * Requires that no terms have been created yet.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param infile The input file.
 * @param infile_name The name of the input file.
 * @param outfile The output file.
 * @param error_msg Output parameter, stores an error message in case a parse
 *                  error occurred, else \c NULL.
 * @param parsed_status Output parameter, stores the status of the input in case
 *                      of SMT-LIB v2 input, if given.
 * @param parsed_smt2 Output parameter, true if parsed input file has been
 *                    detected as SMT-LIB v2 input.
 *
 * @return `::BITWUZLA_SAT` if the input formula was simplified to true,
 *         `::BITWUZLA_UNSAT` if it was simplified to false,
 *         and `::BITWUZLA_UNKNOWN` otherwise.
 *
 * @see
 *   * `bitwuzla_parse_format`
 */
BitwuzlaResult bitwuzla_parse(Bitwuzla *bitwuzla,
                              FILE *infile,
                              const char *infile_name,
                              FILE *outfile,
                              char **error_msg,
                              BitwuzlaResult *parsed_status,
                              bool *parsed_smt2);

/**
 * Parse input file, assumed to be given in the specified format.
 *
 * Requires that no terms have been created yet.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The input format for printing the model. Either `"btor"` for
 *               the BTOR format, `"btor2"` for the BTOR2 format, or `"smt2"`
 *               for the SMT-LIB v2 format.
 * @param infile The input file.
 * @param infile_name The name of the input file.
 * @param outfile The output file.
 * @param error_msg Output parameter, stores an error message in case a parse
 *                  error occurred, else \c NULL.
 * @param parsed_status Output parameter, stores the status of the input in case
 *                      of SMT-LIB v2 input, if given.
 *
 * @return `::BITWUZLA_SAT` if the input formula was simplified to true,
 *         `::BITWUZLA_UNSAT` if it was simplified to false,
 *         and ::BITWUZLA_UNKNOWN` otherwise.
 *
 * @see
 *   * `bitwuzla_parse`
 */
BitwuzlaResult bitwuzla_parse_format(Bitwuzla *bitwuzla,
                                     const char *format,
                                     FILE *infile,
                                     const char *infile_name,
                                     FILE *outfile,
                                     char **error_msg,
                                     BitwuzlaResult *parsed_status);

/**
 * Substitute a set of keys with their corresponding values in the given term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term in which the keys are to be substituted.
 * @param map_size The size of the substitution map.
 * @param map_keys The keys.
 * @param map_values The mapped values.
 *
 * @return The resulting term from this substitution.
 */
const BitwuzlaTerm *bitwuzla_substitute_term(Bitwuzla *bitwuzla,
                                             const BitwuzlaTerm *term,
                                             size_t map_size,
                                             const BitwuzlaTerm *map_keys[],
                                             const BitwuzlaTerm *map_values[]);

/**
 * Substitute a set of keys with their corresponding values in the set of given
 * terms.
 *
 * The terms in `terms` are replaced with the terms resulting from this
 * substitutions.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param terms_size The size of the set of terms.
 * @param terms The terms in which the keys are to be substituted.
 * @param map_size The size of the substitution map.
 * @param map_keys The keys.
 * @param map_values The mapped values.
 */
void bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
                               size_t terms_size,
                               const BitwuzlaTerm *terms[],
                               size_t map_size,
                               const BitwuzlaTerm *map_keys[],
                               const BitwuzlaTerm *map_values[]);

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Compute the hash value for a sort.
 *
 * @param sort The sort.
 *
 * @return The hash value of the sort.
 */
size_t bitwuzla_sort_hash(const BitwuzlaSort *sort);

/**
 * Get the size of a bit-vector sort.
 *
 * Requires that given sort is a bit-vector sort.
 *
 * @param sort The sort.
 *
 * @return The size of the bit-vector sort.
 */
uint32_t bitwuzla_sort_bv_get_size(const BitwuzlaSort *sort);

/**
 * Get the exponent size of a floating-point sort.
 *
 * Requires that given sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return The exponent size of the floating-point sort.
 */
uint32_t bitwuzla_sort_fp_get_exp_size(const BitwuzlaSort *sort);

/**
 * Get the significand size of a floating-point sort.
 *
 * Requires that given sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return The significand size of the floating-point sort.
 */
uint32_t bitwuzla_sort_fp_get_sig_size(const BitwuzlaSort *sort);

/**
 * Get the index sort of an array sort.
 *
 * Requires that given sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return The index sort of the array sort.
 */
const BitwuzlaSort *bitwuzla_sort_array_get_index(const BitwuzlaSort *sort);

/**
 * Get the element sort of an array sort.
 *
 * Requires that given sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return The element sort of the array sort.
 */
const BitwuzlaSort *bitwuzla_sort_array_get_element(const BitwuzlaSort *sort);

/**
 * Get the domain sorts of a function sort.
 *
 * The domain sorts are returned as an array of sorts of size `size`.
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 * @param size The size of the returned array.
 *
 * @return The domain sorts of the function sort.
 */
const BitwuzlaSort **bitwuzla_sort_fun_get_domain_sorts(
    const BitwuzlaSort *sort, size_t *size);

/**
 * Get the codomain sort of a function sort.
 *
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return The codomain sort of the function sort.
 */
const BitwuzlaSort *bitwuzla_sort_fun_get_codomain(const BitwuzlaSort *sort);

/**
 * Get the arity of a function sort.
 *
 * @param sort The sort.
 *
 * @return The number of arguments of the function sort.
 */
uint32_t bitwuzla_sort_fun_get_arity(const BitwuzlaSort *sort);

/**
 * Determine if two sorts are equal.
 *
 * @param sort0 The first sort.
 * @param sort1 The second sort.
 *
 * @return True if the given sorts are equal.
 */
bool bitwuzla_sort_is_equal(const BitwuzlaSort *sort0,
                            const BitwuzlaSort *sort1);

/**
 * Determine if a sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is an array sort.
 */
bool bitwuzla_sort_is_array(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a Boolean sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a Boolean sort.
 */
bool bitwuzla_sort_is_bool(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a bit-vector sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a bit-vector sort.
 */
bool bitwuzla_sort_is_bv(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a floating-point sort.
 */
bool bitwuzla_sort_is_fp(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a function sort.
 */
bool bitwuzla_sort_is_fun(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a Roundingmode sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a Roundingmode sort.
 */
bool bitwuzla_sort_is_rm(const BitwuzlaSort *sort);

/**
 * Print sort.
 *
 * @param sort The sort.
 * @param format The output format for printing the term. Either `"btor"` for
 *               the BTOR format, or `"smt2"` for the SMT-LIB v2 format. Note
 *               for the `"btor"` this function won't do anything since BTOR
 *               sorts are printed when printing the term via
 *               bitwuzla_term_dump.
 * @param file The file to print the term to.
 */
void bitwuzla_sort_dump(const BitwuzlaSort *sort,
                        const char *format,
                        FILE *file);

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Compute the hash value for a term.
 *
 * @param term The term.
 *
 * @return The hash value of the term.
 */
size_t bitwuzla_term_hash(const BitwuzlaTerm *term);

/**
 * Get the kind of a term.
 *
 * @param term The term.
 *
 * @return The kind of the given term.
 *
 * @see BitwuzlaKind
 */
BitwuzlaKind bitwuzla_term_get_kind(const BitwuzlaTerm *term);

/**
 * Get the child terms of a term.
 *
 * Returns \c NULL if given term does not have children.
 *
 * @param term The term.
 * @param size Output parameter, stores the number of children of `term`.
 *
 * @return The children of `term` as an array of terms.
 */
const BitwuzlaTerm **bitwuzla_term_get_children(const BitwuzlaTerm *term,
                                                size_t *size);

/**
 * Get the indices of an indexed term.
 *
 * Requires that given term is an indexed term.
 *
 * @param term The term.
 * @param size Output parameter, stores the number of indices of `term`.
 *
 * @return The children of `term` as an array of terms.
 */
uint32_t *bitwuzla_term_get_indices(const BitwuzlaTerm *term, size_t *size);

/**
 * Determine if a term is an indexed term.
 *
 * @param term The term.
 *
 * @return True if `term` is an indexed term.
 */
bool bitwuzla_term_is_indexed(const BitwuzlaTerm *term);

/**
 * Get the associated Bitwuzla instance of a term.
 *
 * @param term The term.
 *
 * @return The associated Bitwuzla instance.
 */
Bitwuzla *bitwuzla_term_get_bitwuzla(const BitwuzlaTerm *term);

/**
 * Get the sort of a term.
 *
 * @param term The term.
 *
 * @return The sort of the term.
 */
const BitwuzlaSort *bitwuzla_term_get_sort(const BitwuzlaTerm *term);

/**
 * Get the index sort of an array term.
 *
 * Requires that given term is an array or an array store term.
 *
 * @param term The term.
 *
 * @return The index sort of the array term.
 */
const BitwuzlaSort *bitwuzla_term_array_get_index_sort(
    const BitwuzlaTerm *term);

/**
 * Get the element sort of an array term.
 *
 * Requires that given term is an array or an array store term.
 *
 * @param term The term.
 *
 * @return The element sort of the array term.
 */
const BitwuzlaSort *bitwuzla_term_array_get_element_sort(
    const BitwuzlaTerm *term);

/**
 * Get the domain sorts of a function term.
 *
 * The domain sorts are returned as an array of sorts of size `size.
 * Requires that given term is an uninterpreted function, a lambda term, an
 * array store term, or an ite term over function terms.
 *
 * @param term The term.
 * @param size The size of the returned array. Optional, NULL is allowed.
 *
 * @return The domain sorts of the function term.
 */
const BitwuzlaSort **bitwuzla_term_fun_get_domain_sorts(
    const BitwuzlaTerm *term, size_t *size);

/**
 * Get the codomain sort of a function term.
 *
 * Requires that given term is an uninterpreted function, a lambda term, an
 * array store term, or an ite term over function terms.
 *
 * @param term The term.
 *
 * @return The codomain sort of the function term.
 */
const BitwuzlaSort *bitwuzla_term_fun_get_codomain_sort(
    const BitwuzlaTerm *term);

/**
 * Get the bit-width of a bit-vector term.
 *
 * Requires that given term is a bit-vector term.
 *
 * @param term The term.
 *
 * @return The bit-width of the bit-vector term.
 */
uint32_t bitwuzla_term_bv_get_size(const BitwuzlaTerm *term);

/**
 * Get the bit-width of the exponent of a floating-point term.
 *
 * Requires that given term is a floating-point term.
 *
 * @param term The term.
 *
 * @return The bit-width of the exponent of the floating-point term.
 */
uint32_t bitwuzla_term_fp_get_exp_size(const BitwuzlaTerm *term);

/**
 * Get the bit-width of the significand of a floating-point term.
 *
 * Requires that given term is a floating-point term.
 *
 * @param term The term.
 *
 * @return The bit-width of the significand of the floating-point term.
 */
uint32_t bitwuzla_term_fp_get_sig_size(const BitwuzlaTerm *term);

/**
 * Get the arity of a function term.
 *
 * Requires that given term is a function term.
 *
 * @param term The term.
 *
 * @return The arity of the function term.
 */
uint32_t bitwuzla_term_fun_get_arity(const BitwuzlaTerm *term);

/**
 * Get the symbol of a term.
 *
 * @param term The term.
 *
 * @return The symbol of `term`. \c NULL if no symbol is defined.
 */
const char *bitwuzla_term_get_symbol(const BitwuzlaTerm *term);

/**
 * Set the symbol of a term.
 *
 * @param term The term.
 * @param symbol The symbol.
 */
void bitwuzla_term_set_symbol(const BitwuzlaTerm *term, const char *symbol);

/**
 * Determine if the sorts of two terms are equal.
 *
 * @param term0 The first term.
 * @param term1 The second term.
 *
 * @return True if the sorts of `term0` and `term1` are equal.
 */
bool bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
                                 const BitwuzlaTerm *term1);

/**
 * Determine if a term is an array term.
 *
 * @param term The term.
 *
 * @return True if `term` is an array term.
 */
bool bitwuzla_term_is_array(const BitwuzlaTerm *term);

/**
 * Determine if a term is a constant.
 *
 * @param term The term.
 *
 * @return True if `term` is a constant.
 */
bool bitwuzla_term_is_const(const BitwuzlaTerm *term);

/**
 * Determine if a term is a function.
 *
 * @param term The term.
 *
 * @return True if `term` is a function.
 */
bool bitwuzla_term_is_fun(const BitwuzlaTerm *term);

/**
 * Determine if a term is a variable.
 *
 * @param term The term.
 *
 * @return True if `term` is a variable.
 */
bool bitwuzla_term_is_var(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bound variable.
 *
 * @param term The term.
 *
 * @return True if `term` is a variable and bound.
 */
bool bitwuzla_term_is_bound_var(const BitwuzlaTerm *term);

/**
 * Determine if a term is a value.
 *
 * @param term The term.
 *
 * @return True if `term` is a value.
 */
bool bitwuzla_term_is_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value.
 */
bool bitwuzla_term_is_bv_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point value.
 */
bool bitwuzla_term_is_fp_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode value.
 */
bool bitwuzla_term_is_rm_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a Boolean term.
 *
 * @param term The term.
 *
 * @return True if `term` is a Boolean term.
 */
bool bitwuzla_term_is_bool(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector term.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector term.
 */
bool bitwuzla_term_is_bv(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point term.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point term.
 */
bool bitwuzla_term_is_fp(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode term.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode term.
 */
bool bitwuzla_term_is_rm(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value representing zero.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector zero value.
 */
bool bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value representing one.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector one value.
 */
bool bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value with all bits set to one.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with all bits set to one.
 */
bool bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector minimum signed value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with the most significant bit
 *         set to 1 and all other bits set to 0.
 */
bool bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector maximum signed value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with the most significant bit
 *         set to 0 and all other bits set to 1.
 */
bool bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point positive zero (+zero) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point +zero value.
 */
bool bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point value negative zero (-zero).
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point value negative zero.
 */
bool bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point positive infinity (+oo) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point +oo value.
 */
bool bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point negative infinity (-oo) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point -oo value.
 */
bool bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point NaN value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point NaN value.
 */
bool bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode RNA value.
 *
 * @param term The term.
 *
 * @return True if `term` is a roundindg mode RNA value.
 */
bool bitwuzla_term_is_rm_value_rna(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode RNE value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RNE value.
 */
bool bitwuzla_term_is_rm_value_rne(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode RTN value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTN value.
 */
bool bitwuzla_term_is_rm_value_rtn(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode RTP value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTP value.
 */
bool bitwuzla_term_is_rm_value_rtp(const BitwuzlaTerm *term);

/**
 * Determine if a term is a rounding mode RTZ value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTZ value.
 */
bool bitwuzla_term_is_rm_value_rtz(const BitwuzlaTerm *term);

/**
 * Determine if a term is a constant array.
 *
 * @param term The term.
 *
 * @return True if `term` is a constant array.
 */
bool bitwuzla_term_is_const_array(const BitwuzlaTerm *term);

/**
 * Print term .
 *
 * @param term The term.
 * @param format The output format for printing the term. Either `"btor"` for the
 *               BTOR format, or `"smt2"` for the SMT-LIB v2 format.
 * @param file The file to print the term to.
 */
void bitwuzla_term_dump(const BitwuzlaTerm *term,
                        const char *format,
                        FILE *file);

/* -------------------------------------------------------------------------- */

#if __cplusplus
}
#endif

/* -------------------------------------------------------------------------- */
#endif
