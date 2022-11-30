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
   *  SMT-LIB: \c and */
  EVALUE(AND),
  /*! Disequality.
   *
   * SMT-LIB: \c distinct */
  EVALUE(DISTINCT),
  /*! Equality.
   *
   * SMT-LIB: \c = */
  EVALUE(EQUAL),
  /*! Boolean if and only if.
   *
   * SMT-LIB: \c = */
  EVALUE(IFF),
  /*! Boolean implies.
   *
   * SMT-LIB: \c => */
  EVALUE(IMPLIES),
  /*! Boolean not.
   *
   * SMT-LIB: \c not */
  EVALUE(NOT),
  /*! Boolean or.
   *
   * SMT-LIB: \c or */
  EVALUE(OR),
  /*! Boolean xor.
   *
   * SMT-LIB: \c xor */
  EVALUE(XOR),

  //// Core
  /*! If-then-else.
   *
   * SMT-LIB: \c ite */
  EVALUE(ITE),

  //// Quantifiers
  /*! Existential quantification.
   *
   * SMT-LIB: \c exists */
  EVALUE(EXISTS),
  /*! Universal quantification.
   *
   * SMT-LIB: \c forall */
  EVALUE(FORALL),

  //// Functions
  /*! Function application. */
  EVALUE(APPLY),
  /*! Lambda. */
  EVALUE(LAMBDA),

  //// Arrays
  /*! Array select.
   *
   *  SMT-LIB: \c select */
  EVALUE(ARRAY_SELECT),
  /*! Array store.
   *
   * SMT-LIB: \c store */
  EVALUE(ARRAY_STORE),

  //// Bit-vectors
  /*! Bit-vector addition.
   *
   *  SMT-LIB: \c bvadd */
  EVALUE(BV_ADD),
  /*! Bit-vector and.
   *
   * SMT-LIB: \c bvand */
  EVALUE(BV_AND),
  /*! Bit-vector arithmetic right shift.
   *
   * SMT-LIB: \c bvashr */
  EVALUE(BV_ASHR),
  /*! Bit-vector comparison.
   *
   * SMT-LIB: \c bvcomp */
  EVALUE(BV_COMP),
  /*! Bit-vector concat.
   *
   * SMT-LIB: \c concat */
  EVALUE(BV_CONCAT),
  /*! Bit-vector decrement.
   *
   * Decrement by one. */
  EVALUE(BV_DEC),
  /*! Bit-vector increment.
   *
   * Increment by one. */
  EVALUE(BV_INC),
  /*! Bit-vector multiplication.
   *
   * SMT-LIB: \c bvmul */
  EVALUE(BV_MUL),
  /*! Bit-vector nand.
   *
   * SMT-LIB: \c bvnand */
  EVALUE(BV_NAND),
  /*! Bit-vector negation (two's complement).
   *
   * SMT-LIB: \c bvneg */
  EVALUE(BV_NEG),
  /*! Bit-vector nor.
   *
   * SMT-LIB: \c bvnor */
  EVALUE(BV_NOR),
  /*! Bit-vector not (one's complement).
   *
   * SMT-LIB: \c bvnot */
  EVALUE(BV_NOT),
  /*! Bit-vector or.
   *
   * SMT-LIB: \c bvor */
  EVALUE(BV_OR),
  /*! Bit-vector and reduction.
   *
EVALUE(* Bit-wise *and* reduction), all bits are *and*'ed together into a
single bit.
   * This corresponds to bit-wise *and* reduction as known from Verilog. */
  EVALUE(BV_REDAND),
  /*! Bit-vector reduce or.
   *
EVALUE(* Bit-wise *or* reduction), all bits are *or*'ed together into a single
bit.
   * This corresponds to bit-wise *or* reduction as known from Verilog. */
  EVALUE(BV_REDOR),
  /*! Bit-vector reduce xor.
   *
EVALUE(* Bit-wise *xor* reduction), all bits are *xor*'ed together into a
single bit.
   * This corresponds to bit-wise *xor* reduction as known from Verilog. */
  EVALUE(BV_REDXOR),
  /*! Bit-vector rotate left (not indexed).
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_left. */
  EVALUE(BV_ROL),
  /*! Bit-vector rotate right.
   *
   * This is a non-indexed variant of SMT-LIB \c rotate_right. */
  EVALUE(BV_ROR),
  /*! Bit-vector signed addition overflow test.
   *
   * Single bit to indicate if signed addition produces an overflow. */
  EVALUE(BV_SADD_OVERFLOW),
  /*! Bit-vector signed division overflow test.
   *
   * Single bit to indicate if signed division produces an overflow. */
  EVALUE(BV_SDIV_OVERFLOW),
  /*! Bit-vector signed division.
   *
   * SMT-LIB: \c bvsdiv */
  EVALUE(BV_SDIV),
  /*! Bit-vector signed greater than or equal.
   *
   * SMT-LIB: \c bvsle */
  EVALUE(BV_SGE),
  /*! Bit-vector signed greater than.
   *
   * SMT-LIB: \c bvslt */
  EVALUE(BV_SGT),
  /*! Bit-vector logical left shift.
   *
   * SMT-LIB: \c bvshl */
  EVALUE(BV_SHL),
  /*! Bit-vector logical right shift.
   *
   * SMT-LIB: \c bvshr */
  EVALUE(BV_SHR),
  /*! Bit-vector signed less than or equal.
   *
   * SMT-LIB: \c bvsle */
  EVALUE(BV_SLE),
  /*! Bit-vector signed less than.
   *
   * SMT-LIB: \c bvslt */
  EVALUE(BV_SLT),
  /*! Bit-vector signed modulo.
   *
   * SMT-LIB: \c bvsmod */
  EVALUE(BV_SMOD),
  /*! Bit-vector signed multiplication overflow test.
   *
   * SMT-LIB: \c bvsmod */
  EVALUE(BV_SMUL_OVERFLOW),
  /*! Bit-vector signed remainder.
   *
   * SMT-LIB: \c bvsrem */
  EVALUE(BV_SREM),
  /*! Bit-vector signed subtraction overflow test.
   *
   * Single bit to indicate if signed subtraction produces an overflow. */
  EVALUE(BV_SSUB_OVERFLOW),
  /*! Bit-vector subtraction.
   *
   * SMT-LIB: \c bvsub */
  EVALUE(BV_SUB),
  /*! Bit-vector unsigned addition overflow test.
   *
   * Single bit to indicate if unsigned addition produces an overflow. */
  EVALUE(BV_UADD_OVERFLOW),
  /*! Bit-vector unsigned division.
   *
   * SMT-LIB: \c bvudiv */
  EVALUE(BV_UDIV),
  /*! Bit-vector unsigned greater than or equal.
   *
   * SMT-LIB: \c bvuge */
  EVALUE(BV_UGE),
  /*! Bit-vector unsigned greater than.
   *
   * SMT-LIB: \c bvugt */
  EVALUE(BV_UGT),
  /*! Bit-vector unsigned less than or equal.
   *
   * SMT-LIB: \c bvule */
  EVALUE(BV_ULE),
  /*! Bit-vector unsigned less than.
   *
   * SMT-LIB: \c bvult */
  EVALUE(BV_ULT),
  /*! Bit-vector unsigned multiplication overflow test.
   *
   * Single bit to indicate if unsigned multiplication produces an overflow.
   */
  EVALUE(BV_UMUL_OVERFLOW),
  /*! Bit-vector unsigned remainder.
   *
   * SMT-LIB: \c bvurem */
  EVALUE(BV_UREM),
  /*! Bit-vector unsigned subtraction overflow test.
   *
   * Single bit to indicate if unsigned subtraction produces an overflow. */
  EVALUE(BV_USUB_OVERFLOW),
  /*! Bit-vector xnor.
   *
   * SMT-LIB: \c bvxnor */
  EVALUE(BV_XNOR),
  /*! Bit-vector xor.
   *
   * SMT-LIB: \c bvxor */
  EVALUE(BV_XOR),
  // indexed
  /*! Bit-vector extract.
   *
   * SMT-LIB: \c extract (indexed) */
  EVALUE(BV_EXTRACT),
  /*! Bit-vector repeat.
   *
   * SMT-LIB: \c repeat (indexed) */
  EVALUE(BV_REPEAT),
  /*! Bit-vector rotate left by integer.
   *
   * SMT-LIB: \c rotate_left (indexed) */
  EVALUE(BV_ROLI),
  /*! Bit-vector rotate right by integer.
   *
   * SMT-LIB: \c rotate_right (indexed) */
  EVALUE(BV_RORI),
  /*! Bit-vector sign extend.
   *
   * SMT-LIB: \c sign_extend (indexed) */
  EVALUE(BV_SIGN_EXTEND),
  /*! Bit-vector zero extend.
   *
   * SMT-LIB: \c zero_extend (indexed) */
  EVALUE(BV_ZERO_EXTEND),
  /*! Floating-point to_fp from IEEE 754 bit-vector.
   *
   * SMT-LIB: \c to_fp (indexed) */

  //// Floating-point arithmetic
  /*! Floating-point absolute value.
   *
   * SMT-LIB: \c fp.abs */
  EVALUE(FP_ABS),
  /*! Floating-point addition.
   *
   * SMT-LIB: \c fp.add */
  EVALUE(FP_ADD),
  /*! Floating-point division.
   *
   * SMT-LIB: \c fp.div */
  EVALUE(FP_DIV),
  /*! Floating-point equality.
   *
   * SMT-LIB: \c fp.eq */
  EVALUE(FP_EQUAL),
  /*! Floating-point fused multiplcation and addition.
   *
   * SMT-LIB: \c fp.fma */
  EVALUE(FP_FMA),
  /*! Floating-point IEEE 754 value.
   *
   * SMT-LIB: \c fp */
  EVALUE(FP_FP),
  /*! Floating-point greater than or equal.
   *
   * SMT-LIB: \c fp.geq */
  EVALUE(FP_GE),
  /*! Floating-point greater than.
   *
   * SMT-LIB: \c fp.gt */
  EVALUE(FP_GT),
  /*! Floating-point is infinity tester.
   *
   * SMT-LIB: \c fp.isInfinite */
  EVALUE(FP_IS_INF),
  /*! Floating-point is Nan tester.
   *
   * SMT-LIB: \c fp.isNaN */
  EVALUE(FP_IS_NAN),
  /*! Floating-point is negative tester.
   *
   * SMT-LIB: \c fp.isNegative */
  EVALUE(FP_IS_NEG),
  /*! Floating-point is normal tester.
   *
   * SMT-LIB: \c fp.isNormal */
  EVALUE(FP_IS_NORMAL),
  /*! Floating-point is positive tester.
   *
   * SMT-LIB: \c fp.isPositive */
  EVALUE(FP_IS_POS),
  /*! Floating-point is subnormal tester.
   *
   * SMT-LIB: \c fp.isSubnormal */
  EVALUE(FP_IS_SUBNORMAL),
  /*! Floating-point is zero tester.
   *
   * SMT-LIB: \c fp.isZero */
  EVALUE(FP_IS_ZERO),
  /*! Floating-point less than or equal.
   *
   * SMT-LIB: \c fp.leq */
  EVALUE(FP_LEQ),
  /*! Floating-point less than.
   *
   * SMT-LIB: \c fp.lt */
  EVALUE(FP_LT),
  /*! Floating-point max.
   *
   * SMT-LIB: \c fp.max */
  EVALUE(FP_MAX),
  /*! Floating-point min.
   *
   * SMT-LIB: \c fp.min */
  EVALUE(FP_MIN),
  /*! Floating-point multiplcation.
   *
   * SMT-LIB: \c fp.mul */
  EVALUE(FP_MUL),
  /*! Floating-point negation.
   *
   * SMT-LIB: \c fp.neg */
  EVALUE(FP_NEG),
  /*! Floating-point remainder.
   *
   * SMT-LIB: \c fp.rem */
  EVALUE(FP_REM),
  /*! Floating-point round to integral.
   *
   * SMT-LIB: \c fp.roundToIntegral */
  EVALUE(FP_RTI),
  /*! Floating-point round to square root.
   *
   * SMT-LIB: \c fp.sqrt */
  EVALUE(FP_SQRT),
  /*! Floating-point round to subtraction.
   *
   * SMT-LIB: \c fp.sqrt */
  EVALUE(FP_SUB),
  // indexed
  EVALUE(FP_TO_FP_FROM_BV),
  /*! Floating-point to_fp from floating-point.
   *
   * SMT-LIB: \c to_fp (indexed) */
  EVALUE(FP_TO_FP_FROM_FP),
  /*! Floating-point to_fp from signed bit-vector value.
   *
   * SMT-LIB: \c to_fp (indexed) */
  EVALUE(FP_TO_FP_FROM_SBV),
  /*! Floating-point to_fp from unsigned bit-vector value.
   *
   * SMT-LIB: \c to_fp_unsigned (indexed) */
  EVALUE(FP_TO_FP_FROM_UBV),
  /*! Floating-point to_sbv.
   *
   * SMT-LIB: \c fp.to_sbv (indexed) */
  EVALUE(FP_TO_SBV),
  /*! Floating-point to_ubv.
   *
   * SMT-LIB: \c fp.to_ubv (indexed) */
  EVALUE(FP_TO_UBV),
#ifndef DOXYGEN_SKIP
  EVALUE(NUM_KINDS),
#endif
};

#ifdef BITWUZLA_API_USE_C_ENUMS
typedef enum ENUM(Kind) ENUM(Kind);
#undef EVALUE
#define EVALUE(name) BITWUZLA_RM_##name
#endif

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
