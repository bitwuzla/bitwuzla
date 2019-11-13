/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2017-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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

/* Create round-nearest-ties-to-even rounding mode. */
BzlaNode *bzla_exp_fp_rne(Bzla *bzla);

/* Create round-nearest-ties-to-away rounding mode. */
BzlaNode *bzla_exp_fp_rna(Bzla *bzla);

/* Create round-toward-positive rounding mode. */
BzlaNode *bzla_exp_fp_rtp(Bzla *bzla);

/* Create round-toward-negative rounding mode. */
BzlaNode *bzla_exp_fp_rtn(Bzla *bzla);

/* Create round-toward-zero rounding mode. */
BzlaNode *bzla_exp_fp_rtz(Bzla *bzla);

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

/* Create floating-point is_normal. */
BzlaNode *bzla_exp_fp_is_normal(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_subnormal. */
BzlaNode *bzla_exp_fp_is_subnormal(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_zero. */
BzlaNode *bzla_exp_fp_is_zero(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_inf. */
BzlaNode *bzla_exp_fp_is_inf(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_nan. */
BzlaNode *bzla_exp_fp_is_nan(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_neg. */
BzlaNode *bzla_exp_fp_is_neg(Bzla *bzla, BzlaNode *exp);

/* Create floating-point is_pos. */
BzlaNode *bzla_exp_fp_is_pos(Bzla *bzla, BzlaNode *exp);

/* Create floating-point absolute value. */
BzlaNode *bzla_exp_fp_abs(Bzla *bzla, BzlaNode *exp);

/* Create floating-point negation. */
BzlaNode *bzla_exp_fp_neg(Bzla *bzla, BzlaNode *exp);

/* Create floating-point maximum. */
BzlaNode *bzla_exp_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point minimum. */
BzlaNode *bzla_exp_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point remainder. */
BzlaNode *bzla_exp_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point equality. */
BzlaNode *bzla_exp_fp_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point less or equal. */
BzlaNode *bzla_exp_fp_leq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point less than. */
BzlaNode *bzla_exp_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point greater or equal. */
BzlaNode *bzla_exp_fp_geq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/* Create floating-point greater than. */
BzlaNode *bzla_exp_fp_gt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point square root wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 */
BzlaNode *bzla_exp_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point round-to-integral wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 */
BzlaNode *bzla_exp_fp_round_to_int(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/**
 * Create floating-point addition wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point subtraction wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point multiplication wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point division wrt to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 */
BzlaNode *bzla_exp_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

/**
 * Create floating-point fused multiplication and addition (e1 * e2) + e3 wrt
 * to given rounding mode.
 * e0: rounding mode
 * e1: floating-point operand
 * e2: floating-point operand
 * e3: floating-point operand
 */
BzlaNode *bzla_exp_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3);

/**
 * Create floating-point of given floating-point sort from given bit-vector
 * expression 'exp'.
 * exp:  bit-vector operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp(Bzla *bzla, BzlaNode *exp, BzlaSortId sort);

/**
 * Create floating-point to-fp from bit-vector (interpreted as signed) or
 * floating-point expression wrt to given rounding mode.
 * e0:   rounding mode
 * e1:   bit-vector or floating-point operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_signed(Bzla *bzla,
                                   BzlaNode *e0,
                                   BzlaNode *e1,
                                   BzlaSortId sort);

/**
 * Create floating-point to-fp from bit-vector expression (interpreted as
 * unsigned) wrt to given rounding mode.
 * e0:   rounding mode
 * e1:   bit-vector operand
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_unsigned(Bzla *bzla,
                                     BzlaNode *e0,
                                     BzlaNode *e1,
                                     BzlaSortId sort);

/**
 * Create floating-point to-fp from double wrt to given rounding mode.
 * exp:  rounding mode
 * real: the real operand represented as a strin
 * sort: floating-point sort
 */
BzlaNode *bzla_exp_fp_to_fp_real(Bzla *bzla,
                                 BzlaNode *exp,
                                 const char *real,
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
