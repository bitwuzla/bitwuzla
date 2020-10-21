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
  BZLA_OPT_PRODUCE_MODELS,
};
typedef enum BitwuzlaOption BitwuzlaOption;

enum BitwuzlaKind
{
  BZLA_KIND_IMPLIES,
  BZLA_KIND_IFF,
  BZLA_KIND_EQUAL,
  BZLA_KIND_DISTINCT,
  BZLA_KIND_BV_NOT,
  BZLA_KIND_BV_NEG,
  BZLA_KIND_BV_REDOR,
  BZLA_KIND_BV_REDXOR,
  BZLA_KIND_BV_REDAND,
  BZLA_KIND_BV_EXTRACT,
  BZLA_KIND_BV_ZERO_EXTEND,
  BZLA_KIND_BV_SIGN_EXTEND,
  BZLA_KIND_BV_XOR,
  BZLA_KIND_BV_XNOR,
  BZLA_KIND_BV_AND,
  BZLA_KIND_BV_NAND,
  BZLA_KIND_BV_OR,
  BZLA_KIND_BV_NOR,
  BZLA_KIND_BV_ADD,
  BZLA_KIND_BV_UADD_OVERFLOW,
  BZLA_KIND_BV_SADD_OVERFLOW,
  BZLA_KIND_BV_MUL,
  BZLA_KIND_BV_UMUL_OVERFLOW,
  BZLA_KIND_BV_SMUL_OVERFLOW,
  BZLA_KIND_BV_ULT,
  BZLA_KIND_BV_SLT,
  BZLA_KIND_BV_ULEQ,
  BZLA_KIND_BV_SLEQ,
  BZLA_KIND_BV_UGT,
  BZLA_KIND_BV_SGT,
  BZLA_KIND_BV_UGEQ,
  BZLA_KIND_BV_SGEQ,
  BZLA_KIND_BV_SHL,
  BZLA_KIND_BV_SHR,
  BZLA_KIND_BV_ASHR,
  BZLA_KIND_BV_ROL,
  BZLA_KIND_BV_ROR,
  BZLA_KIND_BV_SUB,
  BZLA_KIND_BV_USUB_OVERFLOW,
  BZLA_KIND_BV_SSUB_OVERFLOW,
  BZLA_KIND_BV_UDIV,
  BZLA_KIND_BV_SDV,
  BZLA_KIND_BV_SDIV_OVERFLOW,
  BZLA_KIND_BV_UREM,
  BZLA_KIND_BV_SREM,
  BZLA_KIND_BV_SMOD,
  BZLA_KIND_BV_CONCAT,
  BZLA_KIND_BV_REPEAT,
  BZLA_KIND_FP_FP,
  BZLA_KIND_FP_ABS,
  BZLA_KIND_FP_NEG,
  BZLA_KIND_FP_IS_NORMAL,
  BZLA_KIND_FP_IS_SUBNORMAL,
  BZLA_KIND_FP_IS_NAN,
  BZLA_KIND_FP_IS_ZERO,
  BZLA_KIND_FP_IS_INF,
  BZLA_KIND_FP_IS_NEG,
  BZLA_KIND_FP_IS_POS,
  BZLA_KIND_FP_MIN,
  BZLA_KIND_FP_MAX,
  BZLA_KIND_FP_REM,
  BZLA_KIND_FP_EQ,
  BZLA_KIND_FP_LEQ,
  BZLA_KIND_FP_LT,
  BZLA_KIND_FP_GEQ,
  BZLA_KIND_FP_GT,
  BZLA_KIND_FP_SQRT,
  BZLA_KIND_FP_RTI,
  BZLA_KIND_FP_ADD,
  BZLA_KIND_FP_SUB,
  BZLA_KIND_FP_MUL,
  BZLA_KIND_FP_DIV,
  BZLA_KIND_FP_FMA,
  BZLA_KIND_FP_TO_SBV,
  BZLA_KIND_FP_TO_UBV,
  BZLA_KIND_FP_TO_FP_FROM_BV,
  BZLA_KIND_FP_TO_FP_FROM_FP,
  BZLA_KIND_FP_TO_FP_FROM_UINT,
  BZLA_KIND_ARRAY_SELECT,
  BZLA_KIND_ARRAY_STORE,
  BZLA_KIND_ITE,
  BZLA_KIND_BV_INC,
  BZLA_KIND_BV_DEC,
  BZLA_KIND_FORALL,
  BZLA_KIND_EXISTS,
};
typedef enum BitwuzlaKind BitwuzlaKind;

enum BitwuzlaResult
{
  BITWUZLA_SAT,
  BITWUZLA_UNSAT,
  BITWUZLA_UNKNOWN,
};
typedef enum BitwuzlaResult BitwuzlaResult;

enum BitwuzlaRoundingMode
{
  BITWUZLA_RM_RNE,
  BITWUZLA_RM_RNA,
  BITWUZLA_RM_RTN,
  BITWUZLA_RM_RTP,
  BITWUZLA_RM_RTZ,
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
                                  BitwuzlaSort *domain);
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
bool bitwuzla_failed(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

BitwuzlaTerm **bitwuzla_get_failed_assumptions(Bitwuzla *bitwuzla);
BitwuzlaTerm **bitwuzla_get_unsat_core(Bitwuzla *bitwuzla);

void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla);
void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla);

void bitwuzla_simplify(void);

BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

void bitwuzla_print_model(Bitwuzla *bitwuzla, char *format, FILE *file);

void bitwuzla_dump_smt2(Bitwuzla *bitwuzla, FILE *file);

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

BitwuzlaSort bitwuzla_sort_get_domain(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaSort bitwuzla_sort_get_codomain(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_bv_get_width(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fun_get_arity(Bitwuzla *bitwuzla, BitwuzlaSort sort);

bool bitwuzla_sort_is_equal(Bitwuzla *bitwuzla,
                            BitwuzlaSort sort0,
                            BitwuzlaSort s1);
bool bitwuzla_sort_is_array(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_bv(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_fp(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_fun(Bitwuzla *bitwuzla, BitwuzlaSort sort);
bool bitwuzla_sort_is_rm(Bitwuzla *bitwuzla, BitwuzlaSort sort);

uint32_t bitwuzla_sort_bv_get_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_exp_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_sig_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

Bitwuzla *bitwuzla_get_bitwuzla(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
const char *bitwuzla_get_symbol(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
void bitwuzla_set_symbol(Bitwuzla *bitwuzla,
                         BitwuzlaTerm *term,
                         const char *symbol);

BitwuzlaSort bitwuzla_get_sort(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_bv_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_one(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_ones(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_min_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv_value_max_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_fp_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_pos_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_neg_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_pos_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_neg_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp_value_nan(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_rm_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_array(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_bv(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fp(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_fun(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_rm(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

bool bitwuzla_is_const(Bitwuzla *bitwuzla, BitwuzlaTerm *term);
bool bitwuzla_is_var(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

/* -------------------------------------------------------------------------- */

#if __cplusplus
}
#endif

/* -------------------------------------------------------------------------- */
#endif
