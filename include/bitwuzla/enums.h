/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#if (!defined(BITWUZLA_API_USE_C_ENUMS)             \
     && !defined(BITWUZLA_API_ENUM_CPP_H_INCLUDED)) \
    || (defined(BITWUZLA_API_USE_C_ENUMS)           \
        && !defined(BITWUZLA_API_ENUM_C_H_INCLUDED))

#ifndef BITWUZLA_API_USE_C_ENUMS
namespace bitwuzla {
#define ENUM(name) class name
#define EVALUE(name) name
#else
#define ENUM(name) Bitwuzla##name
#endif

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

#ifdef BITWUZLA_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) BITWUZLA_##name
#endif

/** A satisfiability result. */
enum ENUM(Result)
{
  EVALUE(SAT)     = 10,  ///< sat
  EVALUE(UNSAT)   = 20,  ///< unsat
  EVALUE(UNKNOWN) = 0,   ///< unknown
};

#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(Result) ENUM(Result);
#endif
#endif

/* -------------------------------------------------------------------------- */
/* RoundingMode                                                               */
/* -------------------------------------------------------------------------- */

#ifdef BITWUZLA_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) BITWUZLA_RM_##name
#endif

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
enum ENUM(RoundingMode)
{
  /*!
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   *
   * **SMT-LIB:** \c RNE \c roundNearestTiesToEven
   */
  EVALUE(RNE) = 0,
  /*!
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   *
   * **SMT-LIB:** \c RNA \c roundNearestTiesToAway
   */
  EVALUE(RNA) = 1,
  /*!
   * Round towards negative infinity (-oo).
   * The result shall be the format’s floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   *
   * **SMT-LIB:** \c RTN \c roundTowardNegative
   */
  EVALUE(RTN) = 2,
  /*!
   * Round towards positive infinity (+oo).
   * The result shall be the format’s floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   *
   * **SMT-LIB:** \c RTP \c roundTowardPositive
   */
  EVALUE(RTP) = 3,
  /*!
   * Round towards zero.
   * The result shall be the format’s floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   *
   * **SMT-LIB:** \c RTZ \c roundTowardZero
   */
  EVALUE(RTZ) = 4,
#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
  EVALUE(MAX) = 5,
#endif
#endif
};

#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(RoundingMode) ENUM(RoundingMode);
#endif
#endif

/* -------------------------------------------------------------------------- */
/* Term Kind                                                                  */
/* -------------------------------------------------------------------------- */

#ifdef BITWUZLA_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) BITWUZLA_KIND_##name
#endif

/** The term kind. */
enum ENUM(Kind)
{
  /*! First order constant. */
  EVALUE(CONSTANT) = 0,
  /*! Constant array. */
  EVALUE(CONST_ARRAY),
  /*! Value. */
  EVALUE(VALUE),
  /*! Bound variable. */
  EVALUE(VARIABLE),

  //////// operators

  //// Boolean
  /*! Boolean and.
   *
   * **SMT-LIB:** \c and
   *
   * **Number of arguments:** \c >= 2
   *
   * **Arguments:** \f$Bool \times ... \times Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(AND),
  /*! Disequality.
   *
   * **SMT-LIB:** \c distinct
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$S \times ... \times S \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(DISTINCT),
  /*! Equality.
   *
   * **SMT-LIB:** \c =
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$S \times ... \times S \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(EQUAL),
  /*! Boolean if and only if.
   *
   * **SMT-LIB:** \c =
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$Bool \times ... \times Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(IFF),
  /*! Boolean implies.
   *
   * **SMT-LIB:** \c =>
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$Bool \times ... \times Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(IMPLIES),
  /*! Boolean not.
   *
   * **SMT-LIB:** \c not
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(NOT),
  /*! Boolean or.
   *
   * **SMT-LIB:** \c or
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$Bool \times ... \times Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(OR),
  /*! Boolean xor.
   *
   * **SMT-LIB:** \c xor
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$Bool \times ... \times Bool \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(XOR),

  //// Core
  /*! If-then-else.
   *
   * **SMT-LIB:** \c ite
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$Bool \times S  \times S \rightarrow S\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(ITE),

  //// Quantifiers
  /*! Existential quantification.
   *
   * **SMT-LIB:** \c exists
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$S_1 \times ...  \times S_n \times Bool \rightarrow
   * Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(EXISTS),
  /*! Universal quantification.
   *
   * **SMT-LIB:** \c forall
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$S_1 \times ...  \times S_n \times Bool \rightarrow
   * Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FORALL),

  //// Functions
  /*! Function application.
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$(S_1 \times ... \times S_n \rightarrow S) \times S_1
   * \times ...  \times S_n \rightarrow S\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(APPLY),
  /*! Lambda.
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$S_1 \times ... \times S_n \times S \rightarrow (S_1
   * \times ... \times S_n \rightarrow S)\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(LAMBDA),

  //// Arrays
  /*! Array select.
   *
   * **SMT-LIB:** \c select
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$(S_i \rightarrow S_e) \times S_i \rightarrow S_e\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(ARRAY_SELECT),
  /*! Array store.
   *
   * **SMT-LIB:** \c store
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$(S_i \rightarrow S_e) \times S_i \times S_e \rightarrow
   * (S_i \rightarrow S_e)\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(ARRAY_STORE),

  //// Bit-vectors
  /*! Bit-vector addition.
   *
   * **SMT-LIB:** \c bvadd
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ADD),
  /*! Bit-vector and.
   *
   * **SMT-LIB:** \c bvand
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_AND),
  /*! Bit-vector arithmetic right shift.
   *
   * **SMT-LIB:** \c bvashr
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ASHR),
  /*! Bit-vector comparison.
   *
   * **SMT-LIB:** \c bvcomp
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_1\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_COMP),
  /*! Bit-vector concat.
   *
   * **SMT-LIB:** \c concat
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_m \rightarrow BV_{n + ... +
   * m}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_CONCAT),
  /*! Bit-vector decrement.
   *
   * Decrement by one.
   *
   *  Number of arguments: 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   *  Create with:
   *  - **C**
   *    * `bitwuzla_mk_term1()`
   *    * `bitwuzla_mk_term()`
   *  - **C++**
   *    * `bitwuzla::mk_term()`
   */
  EVALUE(BV_DEC),
  /*! Bit-vector increment.
   *
   * Increment by one.
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_INC),
  /*! Bit-vector multiplication.
   *
   * **SMT-LIB:** \c bvmul
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *    * `bitwuzla::mk_term()`
   */
  EVALUE(BV_MUL),
  /*! Bit-vector nand.
   *
   * **SMT-LIB:** \c bvnand
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_NAND),
  /*! Bit-vector negation (two's complement).
   *
   * **SMT-LIB:** \c bvneg
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_NEG),
  /*! Bit-vector negation overflow test.
   *
   * Predicate indicating if bit-vector negation produces an overflow.
   *
   * **SMT-LIB:** \c bvnego
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_NEG_OVERFLOW),
  /*! Bit-vector nor.
   *
   * **SMT-LIB:** \c bvnor
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_NOR),
  /*! Bit-vector not (one's complement).
   *
   * **SMT-LIB:** \c bvnot
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_NOT),
  /*! Bit-vector or.
   *
   * **SMT-LIB:** \c bvor
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_OR),
  /*! Bit-vector and reduction.
   *
   * Bit-wise *and* reduction), all bits are *and*'ed together into a single
   * bit. This corresponds to bit-wise *and* reduction as known from Verilog.
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_1\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_REDAND),
  /*! Bit-vector reduce or.
   *
   * Bit-wise *or* reduction), all bits are *or*'ed together into a single
   * bit. This corresponds to bit-wise *or* reduction as known from Verilog.
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_1\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_REDOR),
  /*! Bit-vector reduce xor.
   *
   * Bit-wise *xor* reduction), all bits are *xor*'ed together into a single
   * bit. This corresponds to bit-wise *xor* reduction as known from Verilog.
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_1\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_REDXOR),
  /*! Bit-vector rotate left (not indexed).
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_left.
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ROL),
  /*! Bit-vector rotate right.
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_right.
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ROR),
  /*! Bit-vector signed addition overflow test.
   *
   * Predicate indicating if signed addition produces an overflow.
   *
   * **SMT-LIB:** \c bvsaddo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SADD_OVERFLOW),
  /*! Bit-vector signed division overflow test.
   *
   * Predicate indicating if signed division produces an overflow.
   *
   * **SMT-LIB:** \c bvsdivo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SDIV_OVERFLOW),
  /*! Bit-vector signed division.
   *
   * **SMT-LIB:** \c bvsdiv
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SDIV),
  /*! Bit-vector signed greater than or equal.
   *
   * **SMT-LIB:** \c bvsle
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SGE),
  /*! Bit-vector signed greater than.
   *
   * **SMT-LIB:** \c bvslt
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SGT),
  /*! Bit-vector logical left shift.
   *
   * **SMT-LIB:** \c bvshl
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SHL),
  /*! Bit-vector logical right shift.
   *
   * **SMT-LIB:** \c bvshr
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SHR),
  /*! Bit-vector signed less than or equal.
   *
   * **SMT-LIB:** \c bvsle
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SLE),
  /*! Bit-vector signed less than.
   *
   * **SMT-LIB:** \c bvslt
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SLT),
  /*! Bit-vector signed modulo.
   *
   * **SMT-LIB:** \c bvsmod
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SMOD),
  /*! Bit-vector signed multiplication overflow test.
   *
   * Predicate indicating if signed multiplication produces an overflow.
   *
   * **SMT-LIB:** \c bvsmulo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SMUL_OVERFLOW),
  /*! Bit-vector signed remainder.
   *
   * **SMT-LIB:** \c bvsrem
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SREM),
  /*! Bit-vector signed subtraction overflow test.
   *
   * Predicate indicatin if signed subtraction produces an overflow.
   *
   * **SMT-LIB:** \c bvssubo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SSUB_OVERFLOW),
  /*! Bit-vector subtraction.
   *
   * **SMT-LIB:** \c bvsub
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SUB),
  /*! Bit-vector unsigned addition overflow test.
   *
   * Predicate indicating if unsigned addition produces an overflow.
   *
   * **SMT-LIB:** \c bvuaddo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UADD_OVERFLOW),
  /*! Bit-vector unsigned division.
   *
   * **SMT-LIB:** \c bvudiv
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UDIV),
  /*! Bit-vector unsigned greater than or equal.
   *
   * **SMT-LIB:** \c bvuge
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UGE),
  /*! Bit-vector unsigned greater than.
   *
   * **SMT-LIB:** \c bvugt
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UGT),
  /*! Bit-vector unsigned less than or equal.
   *
   * **SMT-LIB:** \c bvule
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ULE),
  /*! Bit-vector unsigned less than.
   *
   * **SMT-LIB:** \c bvult
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ULT),
  /*! Bit-vector unsigned multiplication overflow test.
   *
   * Predicate indicating if unsigned multiplication produces an overflow.
   *
   * **SMT-LIB:** \c bvumulo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UMUL_OVERFLOW),
  /*! Bit-vector unsigned remainder.
   *
   * **SMT-LIB:** \c bvurem
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_UREM),
  /*! Bit-vector unsigned subtraction overflow test.
   *
   * Predicate indicating if unsigned subtraction produces an overflow.
   *
   * **SMT-LIB:** \c bvusubo
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_USUB_OVERFLOW),
  /*! Bit-vector xnor.
   *
   * **SMT-LIB:** \c bvxnor
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$BV_n \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_XNOR),
  /*! Bit-vector xor.
   *
   * **SMT-LIB:** \c bvxor
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$BV_n \times ... \times BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_XOR),
  /*! Bit-vector extract.
   *
   * **SMT-LIB:** \c extract (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 2 (\f$u\f$, \f$l\f$ with \f$u \geq l\f$)
   *
   * **Arguments:** \f$BV_n \rightarrow BV_{u - l + 1}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_EXTRACT),
  /*! Bit-vector repeat.
   *
   * **SMT-LIB:** \c repeat (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 1 (\f$i\f$ s.t. \f$i \cdot n\f$ fits into
   * `uint64_t`)
   *
   * **Arguments:** \f$BV_n \rightarrow BV_{n * i}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_REPEAT),
  /*! Bit-vector rotate left by integer.
   *
   * **SMT-LIB:** \c rotate_left (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ROLI),
  /*! Bit-vector rotate right by integer.
   *
   * **SMT-LIB:** \c rotate_right (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 1
   *
   * **Arguments:** \f$BV_n \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_RORI),
  /*! Bit-vector sign extend.
   *
   * **SMT-LIB:** \c sign_extend (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 1 (\f$i\f$ s.t. \f$i + n\f$ fits into `uint64_t`)
   *
   * **Arguments:** \f$BV_n \rightarrow BV_{n + i}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_SIGN_EXTEND),
  /*! Bit-vector zero extend.
   *
   * **SMT-LIB:** \c zero_extend (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 1 (\f$i\f$ s.t. \f$i + n\f$ fits into `uint64_t`)
   *
   * **Arguments:** \f$BV_n \rightarrow BV_{n + i}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(BV_ZERO_EXTEND),

  //// Floating-point arithmetic
  /*! Floating-point absolute value.
   *
   * **SMT-LIB:** \c fp.abs
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_ABS),
  /*! Floating-point addition.
   *
   * **SMT-LIB:** \c fp.add
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \times \mathit{FP}_{es}
   * \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_ADD),
  /*! Floating-point division.
   *
   * **SMT-LIB:** \c fp.div
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \times \mathit{FP}_{es}
   * \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_DIV),
  /*! Floating-point equality.
   *
   * **SMT-LIB:** \c fp.eq
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times ... \times \mathit{FP}_{es}
   * \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_EQUAL),
  /*! Floating-point fused multiplcation and addition.
   *
   * **SMT-LIB:** \c fp.fma
   *
   * **Number of Arguments:** 4
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \times \mathit{FP}_{es} \times
   * \mathit{FP}_{es} \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_FMA),
  /*! Floating-point IEEE 754 value.
   *
   * **SMT-LIB:** \c fp
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$BV_1 \times BV_e \times BV_{s-1} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_FP),
  /*! Floating-point greater than or equal.
   *
   * **SMT-LIB:** \c fp.geq
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times ... \times \mathit{FP}_{es}
   * \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_GEQ),
  /*! Floating-point greater than.
   *
   * **SMT-LIB:** \c fp.gt
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times ... \times \mathit{FP}_{es}
   * \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_GT),
  /*! Floating-point is infinity tester.
   *
   * **SMT-LIB:** \c fp.isInfinite
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_INF),
  /*! Floating-point is Nan tester.
   *
   * **SMT-LIB:** \c fp.isNaN
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_NAN),
  /*! Floating-point is negative tester.
   *
   * **SMT-LIB:** \c fp.isNegative
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_NEG),
  /*! Floating-point is normal tester.
   *
   * **SMT-LIB:** \c fp.isNormal
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_NORMAL),
  /*! Floating-point is positive tester.
   *
   * **SMT-LIB:** \c fp.isPositive
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_POS),
  /*! Floating-point is subnormal tester.
   *
   * **SMT-LIB:** \c fp.isSubnormal
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_SUBNORMAL),
  /*! Floating-point is zero tester.
   *
   * **SMT-LIB:** \c fp.isZero
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_IS_ZERO),
  /*! Floating-point less than or equal.
   *
   * **SMT-LIB:** \c fp.leq
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times ... \times \mathit{FP}_{es}
   * \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_LEQ),
  /*! Floating-point less than.
   *
   * **SMT-LIB:** \c fp.lt
   *
   * **Number of Arguments:** \c >= 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow Bool\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_LT),
  /*! Floating-point max.
   *
   * **SMT-LIB:** \c fp.max
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times \mathit{FP}_{es} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_MAX),
  /*! Floating-point min.
   *
   * **SMT-LIB:** \c fp.min
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times \mathit{FP}_{es} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_MIN),
  /*! Floating-point multiplcation.
   *
   * **SMT-LIB:** \c fp.mul
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \times \mathit{FP}_{es}
   * \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_MUL),
  /*! Floating-point negation.
   *
   * **SMT-LIB:** \c fp.neg
   *
   * **Number of Arguments:** 1
   *
   * **Arguments:** \f$\mathit{FP}_{es} \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_NEG),
  /*! Floating-point remainder.
   *
   * **SMT-LIB:** \c fp.rem
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$\mathit{FP}_{es} \times \mathit{FP}_{es} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_REM),
  /*! Floating-point round to integral.
   *
   * **SMT-LIB:** \c fp.roundToIntegral
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_RTI),
  /*! Floating-point square root.
   *
   * **SMT-LIB:** \c fp.sqrt
   *
   * **Number of Arguments:** 2
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_SQRT),
  /*! Floating-point subtraction.
   *
   * **SMT-LIB:** \c fp.sub
   *
   * **Number of Arguments:** 3
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \times \mathit{FP}_{es}
   * \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term3()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_SUB),
  /*! Floating-point to_fp from IEEE 754 bit-vector.
   *
   * **SMT-LIB:** \c to_fp (indexed)
   *
   * **Number of Arguments:** 1
   *
   * **Number of Indices:** 2 (\f$e\f$, \f$s\f$)
   *
   * **Arguments:** \f$BV_n \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term1_indexed2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_FP_FROM_BV),
  /*! Floating-point to_fp from floating-point.
   *
   * **SMT-LIB:** \c to_fp (indexed)
   *
   * **Number of Arguments:** 2
   *
   * **Number of Indices:** 2 (\f$e\f$, \f$s\f$)
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{e's'} \rightarrow
   * \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2_indexed2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_FP_FROM_FP),
  /*! Floating-point to_fp from signed bit-vector value.
   *
   * **SMT-LIB:** \c to_fp (indexed)
   *
   *
   * **Number of Arguments:** 2
   *
   * **Number of Indices:** 2 (\f$e\f$, \f$s\f$)
   *
   * **Arguments:** \f$RM \times BV_n \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2_indexed2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_FP_FROM_SBV),
  /*! Floating-point to_fp from unsigned bit-vector value.
   *
   * **SMT-LIB:** \c to_fp_unsigned (indexed)
   *
   * **Number of Arguments:** 2
   *
   * **Number of Indices:** 2 (\f$e\f$, \f$s\f$)
   *
   * **Arguments:** \f$RM \times BV_n \rightarrow \mathit{FP}_{es}\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2_indexed2()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_FP_FROM_UBV),
  /*! Floating-point to_sbv.
   *
   * **SMT-LIB:** \c fp.to_sbv (indexed)
   *
   * **Number of Arguments:** 2
   *
   * **Number of Indices:** 1 (\f$n\f$)
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_SBV),
  /*! Floating-point to_ubv.
   *
   * **SMT-LIB:** \c fp.to_ubv (indexed)
   *
   * **Number of Arguments:** 2
   *
   * **Number of Indices:** 1 (\f$n\f$)
   *
   * **Arguments:** \f$RM \times \mathit{FP}_{es} \rightarrow BV_n\f$
   *
   * **Create with:**
   * - **C**
   *   * `bitwuzla_mk_term2_indexed1()`
   *   * `bitwuzla_mk_term()`
   * - **C++**
   *   * `bitwuzla::mk_term()`
   */
  EVALUE(FP_TO_UBV),
#if (!defined(NDEBUG) || defined(BITWUZLA_API_USE_C_ENUMS))
#ifndef DOXYGEN_SKIP
  EVALUE(NUM_KINDS),
#endif
#endif
};

#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(Kind) ENUM(Kind);
#endif
#endif

/* -------------------------------------------------------------------------- */

#undef EVALUE
#undef ENUM

#ifndef BITWUZLA_API_USE_C_ENUMS
}  // namespace bitwuzla
#endif

#endif

#ifndef BITWUZLA_API_USE_C_ENUMS
#ifndef BITWUZLA_API_ENUM_CPP_H_INCLUDED
#define BITWUZLA_API_ENUM_CPP_H_INCLUDED
#endif
#else
#ifndef BITWUZLA_API_ENUM_C_H_INCLUDED
#define BITWUZLA_API_ENUM_C_H_INCLUDED
#endif
#endif
