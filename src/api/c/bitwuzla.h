/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  This file is part of Bitwuzla.
 *
 *  See COPYING for more information on using this software.
 */

#ifndef BITWUZLA_H_INCLUDED
#define BITWUZLA_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

/* -------------------------------------------------------------------------- */

#if __cplusplus
extern "C" {
#endif

/* -------------------------------------------------------------------------- */

enum BitwuzlaBVBase
{
  BITWUZLA_BV_BASE_BIN,
  BITWUZLA_BV_BASE_DEC,
  BITWUZLA_BV_BASE_HEX,
};
typedef enum BitwuzlaBVBase BitwuzlaBVBase;

enum BitwuzlaOption
{
  BITWUZLA_OPT_PRODUCE_MODELS,
};
typedef enum BitwuzlaOption BitwuzlaOption;

enum BitwuzlaKind
{
  BITWUZLA_KIND_AND,
  BITWUZLA_KIND_ARRAY_SELECT,
  BITWUZLA_KIND_ARRAY_STORE,
  BITWUZLA_KIND_BV_ADD,
  BITWUZLA_KIND_BV_AND,
  BITWUZLA_KIND_BV_ASHR,
  BITWUZLA_KIND_BV_CONCAT,
  BITWUZLA_KIND_BV_DEC,
  BITWUZLA_KIND_BV_INC,
  BITWUZLA_KIND_BV_MUL,
  BITWUZLA_KIND_BV_NAND,
  BITWUZLA_KIND_BV_NEG,
  BITWUZLA_KIND_BV_NOR,
  BITWUZLA_KIND_BV_NOT,
  BITWUZLA_KIND_BV_OR,
  BITWUZLA_KIND_BV_REDAND,
  BITWUZLA_KIND_BV_REDOR,
  BITWUZLA_KIND_BV_REDXOR,
  BITWUZLA_KIND_BV_REPEAT,
  BITWUZLA_KIND_BV_ROL,
  BITWUZLA_KIND_BV_ROR,
  BITWUZLA_KIND_BV_SADD_OVERFLOW,
  BITWUZLA_KIND_BV_SDIV_OVERFLOW,
  BITWUZLA_KIND_BV_SDIV,
  BITWUZLA_KIND_BV_SGEQ,
  BITWUZLA_KIND_BV_SGT,
  BITWUZLA_KIND_BV_SHL,
  BITWUZLA_KIND_BV_SHR,
  BITWUZLA_KIND_BV_SLEQ,
  BITWUZLA_KIND_BV_SLT,
  BITWUZLA_KIND_BV_SMOD,
  BITWUZLA_KIND_BV_SMUL_OVERFLOW,
  BITWUZLA_KIND_BV_SREM,
  BITWUZLA_KIND_BV_SSUB_OVERFLOW,
  BITWUZLA_KIND_BV_SUB,
  BITWUZLA_KIND_BV_UADD_OVERFLOW,
  BITWUZLA_KIND_BV_UDIV,
  BITWUZLA_KIND_BV_UGEQ,
  BITWUZLA_KIND_BV_UGT,
  BITWUZLA_KIND_BV_ULEQ,
  BITWUZLA_KIND_BV_ULT,
  BITWUZLA_KIND_BV_UMUL_OVERFLOW,
  BITWUZLA_KIND_BV_UREM,
  BITWUZLA_KIND_BV_USUB_OVERFLOW,
  BITWUZLA_KIND_BV_XNOR,
  BITWUZLA_KIND_BV_XOR,
  BITWUZLA_KIND_DISTINCT,
  BITWUZLA_KIND_EQUAL,
  BITWUZLA_KIND_EXISTS,
  BITWUZLA_KIND_FORALL,
  BITWUZLA_KIND_FP_ABS,
  BITWUZLA_KIND_FP_ADD,
  BITWUZLA_KIND_FP_DIV,
  BITWUZLA_KIND_FP_EQ,
  BITWUZLA_KIND_FP_FMA,
  BITWUZLA_KIND_FP_FP,
  BITWUZLA_KIND_FP_GEQ,
  BITWUZLA_KIND_FP_GT,
  BITWUZLA_KIND_FP_IS_INF,
  BITWUZLA_KIND_FP_IS_NAN,
  BITWUZLA_KIND_FP_IS_NEG,
  BITWUZLA_KIND_FP_IS_NORMAL,
  BITWUZLA_KIND_FP_IS_POS,
  BITWUZLA_KIND_FP_IS_SUBNORMAL,
  BITWUZLA_KIND_FP_IS_ZERO,
  BITWUZLA_KIND_FP_LEQ,
  BITWUZLA_KIND_FP_LT,
  BITWUZLA_KIND_FP_MAX,
  BITWUZLA_KIND_FP_MIN,
  BITWUZLA_KIND_FP_MUL,
  BITWUZLA_KIND_FP_NEG,
  BITWUZLA_KIND_FP_REM,
  BITWUZLA_KIND_FP_RTI,
  BITWUZLA_KIND_FP_SQRT,
  BITWUZLA_KIND_FP_SUB,
  BITWUZLA_KIND_IFF,
  BITWUZLA_KIND_IMPLIES,
  BITWUZLA_KIND_ITE,
  BITWUZLA_KIND_NOT,
  BITWUZLA_KIND_OR,
  BITWUZLA_KIND_XOR,
  // indexed
  BITWUZLA_KIND_BV_EXTRACT,
  BITWUZLA_KIND_BV_ROLI,
  BITWUZLA_KIND_BV_RORI,
  BITWUZLA_KIND_BV_SIGN_EXTEND,
  BITWUZLA_KIND_BV_ZERO_EXTEND,
  BITWUZLA_KIND_FP_TO_FP_FROM_BV,
  BITWUZLA_KIND_FP_TO_FP_FROM_FP,
  BITWUZLA_KIND_FP_TO_FP_FROM_INT,
  BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
  BITWUZLA_KIND_FP_TO_SBV,
  BITWUZLA_KIND_FP_TO_UBV,
};
typedef enum BitwuzlaKind BitwuzlaKind;

enum BitwuzlaResult
{
  BITWUZLA_SAT     = 10,
  BITWUZLA_UNSAT   = 20,
  BITWUZLA_UNKNOWN = 0,
};
typedef enum BitwuzlaResult BitwuzlaResult;

enum BitwuzlaRoundingMode
{
  BITWUZLA_RM_RNE = 0,
  BITWUZLA_RM_RNA = 1,
  BITWUZLA_RM_RTN = 2,
  BITWUZLA_RM_RTP = 3,
  BITWUZLA_RM_RTZ = 4,
  BITWUZLA_RM_MAX = 5,
};
typedef enum BitwuzlaRoundingMode BitwuzlaRoundingMode;

typedef struct Bitwuzla Bitwuzla;
typedef struct BitwuzlaTerm BitwuzlaTerm;
typedef struct BitwuzlaAnonymous BitwuzlaAnonymous;
typedef BitwuzlaAnonymous *BitwuzlaSort;

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *bitwuzla_new(void);
void bitwuzla_delete(Bitwuzla *bitwuzla);

const char *bitwuzla_copyright(Bitwuzla *bitwuzla);
const char *bitwuzla_version(Bitwuzla *bitwuzla);

void bitwuzla_set_option(Bitwuzla *bitwuzla,
                         BitwuzlaOption option,
                         uint32_t val);
uint32_t bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option);

BitwuzlaSort bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                                    BitwuzlaSort index,
                                    BitwuzlaSort element);
BitwuzlaSort bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla);
BitwuzlaSort bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size);
BitwuzlaSort bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla,
                                 uint32_t exp_size,
                                 uint32_t sig_size);
BitwuzlaSort bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                                  uint32_t arity,
                                  BitwuzlaSort codomain,
                                  BitwuzlaSort domain[]);
BitwuzlaSort bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla);

BitwuzlaTerm *bitwuzla_mk_true(Bitwuzla *bitwuzla);
BitwuzlaTerm *bitwuzla_mk_false(Bitwuzla *bitwuzla);

BitwuzlaTerm *bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla, BitwuzlaSort sort);

BitwuzlaTerm *bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaTerm *bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, BitwuzlaSort sort);

BitwuzlaTerm *bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                                   BitwuzlaSort sort,
                                   const char *value,
                                   BitwuzlaBVBase base);

BitwuzlaTerm *bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                                   BitwuzlaTerm *bv_sign,
                                   BitwuzlaTerm *bv_exponent,
                                   BitwuzlaTerm *bv_significand);

BitwuzlaTerm *bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm);

BitwuzlaTerm *bitwuzla_mk_term(Bitwuzla *bitwuzla,
                               BitwuzlaKind kind,
                               uint32_t argc,
                               BitwuzlaTerm *args[]);

BitwuzlaTerm *bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                                       BitwuzlaKind kind,
                                       uint32_t argc,
                                       BitwuzlaTerm *args[],
                                       uint32_t idxc,
                                       uint32_t idxs[]);

BitwuzlaTerm *bitwuzla_mk_const(Bitwuzla *bitwuzla,
                                BitwuzlaSort sort,
                                const char *symbol);

BitwuzlaTerm *bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                                      BitwuzlaSort sort,
                                      BitwuzlaTerm *value);

BitwuzlaTerm *bitwuzla_mk_var(Bitwuzla *bitwuzla,
                              BitwuzlaSort sort,
                              const char *symbol);

void bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels);
void bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels);

void bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
void bitwuzla_assume(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

BitwuzlaTerm **bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla);
BitwuzlaTerm **bitwuzla_get_unsat_core(Bitwuzla *bitwuzla);

void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla);
void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla);

BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla);

BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

void bitwuzla_print_model(Bitwuzla *bitwuzla, char *format, FILE *file);

void bitwuzla_dump_smt2(Bitwuzla *bitwuzla, FILE *file);

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

uint32_t bitwuzla_sort_bv_get_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_exp_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_sig_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaSort bitwuzla_sort_fun_get_domain(Bitwuzla *bitwuzla,
                                          BitwuzlaSort sort);
BitwuzlaSort bitwuzla_sort_fun_get_codomain(Bitwuzla *bitwuzla,
                                            BitwuzlaSort sort);
uint32_t bitwuzla_sort_fun_get_arity(Bitwuzla *bitwuzla, BitwuzlaSort sort);

bool bitwuzla_sort_is_equal(Bitwuzla *bitwuzla,
                            BitwuzlaSort sort0,
                            BitwuzlaSort sort1);
bool bitwuzla_sort_is_array(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_bv(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_fp(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_fun(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_rm(Bitwuzla *bitwuzla, BitwuzlaSort sort);

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

Bitwuzla *bitwuzla_get_bitwuzla(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_get_sort(BitwuzlaTerm *term);

const char *bitwuzla_get_symbol(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
void bitwuzla_set_symbol(Bitwuzla *bitwuzla,
                         BitwuzlaTerm *term,
                         const char *symbol);

bool bitwuzla_is_array(BitwuzlaTerm *term);
bool bitwuzla_is_const(BitwuzlaTerm *term);
bool bitwuzla_is_fun(BitwuzlaTerm *term);
bool bitwuzla_is_var(BitwuzlaTerm *term);

bool bitwuzla_is_bv_value(BitwuzlaTerm *term);
bool bitwuzla_is_fp_value(BitwuzlaTerm *term);
bool bitwuzla_is_rm_value(BitwuzlaTerm *term);

bool bitwuzla_is_bv(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_rm(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_bv_value_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_one(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_ones(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_min_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_max_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_fp_value_pos_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_neg_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_pos_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_neg_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_nan(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_const_array(BitwuzlaTerm *term);

/* -------------------------------------------------------------------------- */

#if __cplusplus
}
#endif

/* -------------------------------------------------------------------------- */
#endif
