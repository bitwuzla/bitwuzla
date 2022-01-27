/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAEXP_H_INCLUDED
#define BZLAEXP_H_INCLUDED

#include "bzlabv.h"
#include "bzlanode.h"
#include "bzlasort.h"

/*------------------------------------------------------------------------*/

/* Convenience wrapper function. */
BzlaNode *bzla_exp_create(Bzla *bzla,
                          BzlaNodeKind kind,
                          BzlaNode *e[],
                          uint32_t arity);

/*------------------------------------------------------------------------*/

/* Create a variable of given sort. */
BzlaNode *bzla_exp_var(Bzla *bzla, BzlaSortId sort, const char *symbol);

/* Create a parameter (to a function) of given sort. */
BzlaNode *bzla_exp_param(Bzla *bzla, BzlaSortId sort, const char *symbol);

/* Create an array variable of given sort. */
BzlaNode *bzla_exp_array(Bzla *bzla, BzlaSortId sort, const char *symbol);

BzlaNode *bzla_exp_const_array(Bzla *bzla, BzlaSortId sort, BzlaNode *value);

/* Create an uninterpreted function of given sort. */
BzlaNode *bzla_exp_uf(Bzla *bzla, BzlaSortId sort, const char *symbol);

/*------------------------------------------------------------------------*/

/* Create a bit-vector constant of size 1 respresenting TRUE. */
BzlaNode *bzla_exp_true(Bzla *bzla);

/* Create a bit-vector constant of size 1 respresenting FALSE. */
BzlaNode *bzla_exp_false(Bzla *bzla);

/**
 * Create logical IMPLICATION.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_implies(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create logical EQUIVALENCE
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_iff(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/*------------------------------------------------------------------------*/

/**
 * Create equality.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create inequality.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_ne(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/*------------------------------------------------------------------------*/

/**
 * Create if-then-else .
 * width(e_cond) = 1
 * width(e_if) = width(e_else)
 * width(result) = width(e_if) = width(e_else)
 */
BzlaNode *bzla_exp_cond(Bzla *bzla,
                        BzlaNode *e_cond,
                        BzlaNode *e_if,
                        BzlaNode *e_else);

/*------------------------------------------------------------------------*/

/* Create a bit-vector constant representing the given string of bits. */
BzlaNode *bzla_exp_bv_const(Bzla *bzla, const BzlaBitVector *bits);

/* Create a bit-vector constant representing zero. */
BzlaNode *bzla_exp_bv_zero(Bzla *bzla, BzlaSortId sort);

/* Create a bit-vector constant representing all ones. */
BzlaNode *bzla_exp_bv_ones(Bzla *bzla, BzlaSortId sort);

/* Create a bit-vector constant representing 1. */
BzlaNode *bzla_exp_bv_one(Bzla *bzla, BzlaSortId sort);

/* Create a bit-vector constant representing the minimum signed value. */
BzlaNode *bzla_exp_bv_min_signed(Bzla *bzla, BzlaSortId sort);

/* Create a bit-vector constant representing the maximum signed value. */
BzlaNode *bzla_exp_bv_max_signed(Bzla *bzla, BzlaSortId sort);

/**
 * Create a bit-vector constant representing the given signed integer.
 * The constant is obtained by either truncating bits or by signed extension.
 */
BzlaNode *bzla_exp_bv_int(Bzla *bzla, int32_t i, BzlaSortId sort);

/**
 * Create a bit-vector constant representing the given unsigned integer.
 * The constant is obtained by either truncating bits or by unsigned extension.
 */
BzlaNode *bzla_exp_bv_unsigned(Bzla *bzla, uint32_t u, BzlaSortId sort);

/*------------------------------------------------------------------------*/

/* Create a bit-vector one's complement. */
BzlaNode *bzla_exp_bv_not(Bzla *bzla, BzlaNode *exp);

/* Create a bit-Vector two's complement. */
BzlaNode *bzla_exp_bv_neg(Bzla *bzla, BzlaNode *exp);

/* Create a bit-vector OR reduction. */
BzlaNode *bzla_exp_bv_redor(Bzla *bzla, BzlaNode *exp);

/* Create a bit-vector XOR reduction. */
BzlaNode *bzla_exp_bv_redxor(Bzla *bzla, BzlaNode *exp);

/* Create a bit-vector AND reduction. */
BzlaNode *bzla_exp_bv_redand(Bzla *bzla, BzlaNode *exp);

/* Create a slice of the given bit-vector from index 'upper' to 'lower'. */
BzlaNode *bzla_exp_bv_slice(Bzla *bzla,
                            BzlaNode *exp,
                            uint32_t upper,
                            uint32_t lower);

/* Create an unsigned extension of the given bit-vector by 'width' bits. */
BzlaNode *bzla_exp_bv_uext(Bzla *bzla, BzlaNode *exp, uint32_t width);

/* Create a signed extension of the given bit-vector by 'width' bits. */
BzlaNode *bzla_exp_bv_sext(Bzla *bzla, BzlaNode *exp, uint32_t width);

/**
 * Create logical (bit-vector of size 1) and bit-vector XOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_xor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector XNOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_xnor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector AND.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create n-ary bit-vector AND (represented as a chain of binary ANDs).
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_and_n(Bzla *bzla, BzlaNode *args[], uint32_t argc);

/**
 * Create logical (bit-vector of size 1) and bit-vector NAND.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_nand(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector OR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_or(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create logical (bit-vector of size 1) and bit-vector NOR.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_nor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector addition.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_exp_bv_add_n(Bzla *bzla, BzlaNode *args[], uint32_t argc);

/**
 * Create bit-vector unsigned overflow check for add.
 * Result represents if adding two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_uaddo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed overflow check for add.
 * Result represents if adding two signed operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_saddo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector multiplication.
 * width(e0) = width(e1)
 * width(res) = width(e0)
 */
BzlaNode *bzla_exp_bv_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned overflow check for multiplication.
 * Result represents if multiplying two unsigned operands leads to an overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_umulo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed overflow check for multiplication.
 * Result represents if multiplying two signed operands leads to an
 * overflow.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_smulo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned less than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed less than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned less than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_ulte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed less than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_slte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned greater than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_ugt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed greater than.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_sgt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned greater than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_ugte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed greater than or equal.
 * width(e0) = width(e1)
 * width(res) = 1
 */
BzlaNode *bzla_exp_bv_sgte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector logical shift left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector logical shift right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector arithmetic shift right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_sra(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector rotate left.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_rol(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector rotate right.
 * is_power_of_2(width(e0))
 * width(e1) = log2(width(e0))
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_ror(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector rotate left, with the number of bits to rotate by
 * given as an unsigned integer.
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_roli(Bzla *bzla, BzlaNode *exp, uint32_t nbits);

/**
 * Create bit-vector rotate right, with the number of bits to rotate by
 * given as an unsigned integer.
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_rori(Bzla *bzla, BzlaNode *exp, uint32_t nbits);

/**
 * Create bit-vector subtraction.
 * width(e0) = width(e1)
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned overflow check for subtraction.
 * Result represents if e0 - e1 leads to an overflow if both are unsigned.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BzlaNode *bzla_exp_bv_usubo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed overflow check for subtraction.
 * Result represents if e0 - e1 leads to an overflow if both are signed.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BzlaNode *bzla_exp_bv_ssubo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned division.
 * width(e0) = width(e1)
 * width(result) = width(e0)
 */
BzlaNode *bzla_exp_bv_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed division.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BzlaNode *bzla_exp_bv_sdiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed overflow check for division.
 * Result represents if e0 / e1 leads to an overflow if both are signed.
 * For example INT_MIN / -1.
 * width(e0) = width(e1)
 * width(result) = 1
 */
BzlaNode *bzla_exp_bv_sdivo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector unsigned modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BzlaNode *bzla_exp_bv_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create bit-vector signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BzlaNode *bzla_exp_bv_srem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create bit-vector signed modulo.
 * width(e0) = width(e1)
 * width(result) = width(e0) = width(e1)
 */
BzlaNode *bzla_exp_bv_smod(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create bit-vector concatenation.
 * width(result) = width(e0) + width(e1)
 */
BzlaNode *bzla_exp_bv_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create bit-vector repetition.
 * width(result) = n * width(exp)
 */
BzlaNode *bzla_exp_bv_repeat(Bzla *bzla, BzlaNode *exp, uint32_t n);

/* Create bit-vector increment by one */
BzlaNode *bzla_exp_bv_inc(Bzla *bzla, BzlaNode *exp);

/* Create bit-vector decrement by one */
BzlaNode *bzla_exp_bv_dec(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/* Create rounding mode. */
BzlaNode *bzla_exp_rm_const(Bzla *bzla, BzlaRoundingMode rm);

/**
 * Create floating-point const +zero of given floating-point sort.
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_pos_zero(Bzla *bzla, BzlaSortId sort);

/**
 * Create floating-point const -zero of given floating-point sort.
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_neg_zero(Bzla *bzla, BzlaSortId sort);

/**
 * Create floating-point const +oo of given floating-point sort.
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_pos_inf(Bzla *bzla, BzlaSortId sort);

/**
 * Create floating-point const -oo of given floating-point sort.
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_neg_inf(Bzla *bzla, BzlaSortId sort);

/**
 * Create floating-point const Nan of given floating-point sort.
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_nan(Bzla *bzla, BzlaSortId sort);

/**
 * Create floating-point const.
 * e0: bit-vector constant of size 1 (sign bit)
 * e1: bit-vector constant representing the exponent
 * e2: bit-vector constant representing the significand
 */
BzlaNode *bzla_exp_fp_const(Bzla *bzla,
                            BzlaNode *e0,
                            BzlaNode *e1,
                            BzlaNode *e2);

/**
 * Create floating-point const from decimal real string.
 * sort: floating-point sort
 * rm  : rounding mode
 * real: integer or decimal string
 */
BzlaNode *bzla_exp_fp_const_from_real(Bzla *bzla,
                                      BzlaSortId sort,
                                      BzlaNode *rm,
                                      const char *real);

/**
 * Create floating-point const from decimal numerator and denominator strings
 * representing a rational.
 * sort: floating-point sort
 * rm  : rounding mode
 * num : integer or decimal string representing the numerator of the rational
 * den : integer or decimal string representing the denominator of the rational
 */
BzlaNode *bzla_exp_fp_const_from_rational(Bzla *bzla,
                                          BzlaSortId sort,
                                          BzlaNode *rm,
                                          const char *num,
                                          const char *den);

/** Create floating-point const from BzlaFloatingPoint. */
BzlaNode *bzla_exp_fp_const_fp(Bzla *bzla, const BzlaFloatingPoint *fp);

/**
 * Create floating-point expression.
 * e0: bit-vector expression of size 1 (sign bit)
 * e1: bit-vector expression representing the exponent
 * e2: bit-vector expression representing the significand
 */
BzlaNode *bzla_exp_fp_fp(Bzla *bzla,
                         BzlaNode *e0_sign,
                         BzlaNode *e1_exp,
                         BzlaNode *e2_sig);

/** Create floating-point fp.isNormal. */
BzlaNode *bzla_exp_fp_is_normal(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isSubnormal. */
BzlaNode *bzla_exp_fp_is_subnormal(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isZero. */
BzlaNode *bzla_exp_fp_is_zero(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isInfinite. */
BzlaNode *bzla_exp_fp_is_inf(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isNaN. */
BzlaNode *bzla_exp_fp_is_nan(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isNegative. */
BzlaNode *bzla_exp_fp_is_neg(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.isPositive. */
BzlaNode *bzla_exp_fp_is_pos(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.abs. */
BzlaNode *bzla_exp_fp_abs(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.neg. */
BzlaNode *bzla_exp_fp_neg(Bzla *bzla, BzlaNode *exp);

/* Create floating-point fp.max. */
BzlaNode *bzla_exp_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.min. */
BzlaNode *bzla_exp_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.rem. */
BzlaNode *bzla_exp_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.eq. */
BzlaNode *bzla_exp_fp_fpeq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.leq. */
BzlaNode *bzla_exp_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.lt. */
BzlaNode *bzla_exp_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.geq. */
BzlaNode *bzla_exp_fp_gte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point fp.gt. */
BzlaNode *bzla_exp_fp_gt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point fp.sqrt wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 */
BzlaNode *bzla_exp_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point fp.roundToIntegral wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 */
BzlaNode *bzla_exp_fp_rti(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point fp.add wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point fp.sub wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point fp.mul wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point fp.div wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point fp.fpma (e1 * e2) + e3 wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 * e3: floating-point operand
 */
BzlaNode *bzla_exp_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3);

/**
 * Create signed bit-vector fp.to_sbv from given floating-point wrt to given
 * rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * sort: bit-vector sort
 */
BzlaNode *bzla_exp_fp_to_sbv(Bzla *bzla,
                             BzlaNode *e0,
                             BzlaNode *e1,
                             BzlaSortId sort);

/**
 * Create signed bit-vector fp.to_ubv from given floating-point wrt to given
 * rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * sort: bit-vector sort
 */
BzlaNode *bzla_exp_fp_to_ubv(Bzla *bzla,
                             BzlaNode *e0,
                             BzlaNode *e1,
                             BzlaSortId sort);

/**
 * Create floating-point of given floating-point sort from given bit-vector
 * expression 'exp' (interpreted as in IEEE 754-2008 interchange format).
 * exp:  bit-vector operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_from_bv(Bzla *bzla, BzlaNode *exp, BzlaSortId sort);

/**
 * Create floating-point to-fp from floating-point expression wrt to given
 * rounding mode.
 * e0:   rounding mode
 * e1:   floating-point operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_from_fp(Bzla *bzla,
                                    BzlaNode *e0,
                                    BzlaNode *e1,
                                    BzlaSortId sort);

/**
 * Create floating-point to-fp from signed machine integer (represented as
 * bit-vector, interpreted as signed) wrt to given rounding mode.
 * e0:   rounding mode
 * e1:   bit-vector operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_from_sbv(Bzla *bzla,
                                     BzlaNode *e0,
                                     BzlaNode *e1,
                                     BzlaSortId sort);

/**
 * Create floating-point to-fp from unsigned machine integer (represented as
 * bit-vector, interpreted as unsigned) wrt to given rounding mode.
 * e0:   rounding mode
 * e1:   bit-vector operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_from_ubv(Bzla *bzla,
                                     BzlaNode *e0,
                                     BzlaNode *e1,
                                     BzlaSortId sort);

/*------------------------------------------------------------------------*/

/* Array read on array 'e_array' at position 'e_index'.
 * index_width(e_array) = width(e_index)
 * width(result) = elem_width(e_array)
 */
BzlaNode *bzla_exp_read(Bzla *bzla, BzlaNode *e_array, BzlaNode *e_index);

/* Create array write on array 'e_array' at position 'e_index' with value
 * 'e_value'.
 * index_width(e_array) = width(e_index)
 * elem_width(e_array) = width(e_value)
 */
BzlaNode *bzla_exp_write(Bzla *bzla,
                         BzlaNode *e_array,
                         BzlaNode *e_index,
                         BzlaNode *e_value);

/*------------------------------------------------------------------------*/

/**
 * Create function expression with 'paramc' number of parameters 'params' and
 * a function body 'exp'.
 */
BzlaNode *bzla_exp_fun(Bzla *bzla,
                       BzlaNode *params[],
                       uint32_t paramc,
                       BzlaNode *exp);

/* Create apply expression that applies argument expression 'args' to 'fun'. */
BzlaNode *bzla_exp_apply(Bzla *bzla, BzlaNode *fun, BzlaNode *args);

/* Create apply expression that applies 'argc' number of arguments to 'fun'. */
BzlaNode *bzla_exp_apply_n(Bzla *bzla,
                           BzlaNode *fun,
                           BzlaNode *args[],
                           uint32_t argc);

/* Create argument expression with 'argc' arguments. */
BzlaNode *bzla_exp_args(Bzla *bzla, BzlaNode *args[], uint32_t argc);

/**
 * Create update.
 * Updates function 'fun' with 'value' for arguments 'args' (function write).
 */
BzlaNode *bzla_exp_update(Bzla *bzla,
                          BzlaNode *fun,
                          BzlaNode *args,
                          BzlaNode *value);

/* Create lambda expression that represents an array write. */
BzlaNode *bzla_exp_lambda_write(Bzla *bzla,
                                BzlaNode *e_array,
                                BzlaNode *e_index,
                                BzlaNode *e_value);

/* Create lambda expression with variable 'e_param' bound in 'e_exp'. */
BzlaNode *bzla_exp_lambda(Bzla *bzla, BzlaNode *e_param, BzlaNode *e_exp);

/*------------------------------------------------------------------------*/

/* Create forall expression with variable 'param' and 'body'. */
BzlaNode *bzla_exp_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body);
/* Create forall expression with variables 'params' and 'body'. */
BzlaNode *bzla_exp_forall_n(Bzla *bzla,
                            BzlaNode *params[],
                            uint32_t paramc,
                            BzlaNode *body);

/* Create exists expression with variable 'param' and 'body' */
BzlaNode *bzla_exp_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body);
/* Create exists expression with variables 'params' and 'body' */
BzlaNode *bzla_exp_exists_n(Bzla *bzla,
                            BzlaNode *params[],
                            uint32_t paramc,
                            BzlaNode *body);

#if 0
BzlaNode *bzla_invert_quantifier (Bzla * bzla, BzlaNode * quantifier);
#endif

#endif
