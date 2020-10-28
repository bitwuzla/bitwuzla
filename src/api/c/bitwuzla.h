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
  BITWUZLA_OPT_INCREMENTAL,
  BITWUZLA_OPT_PRODUCE_MODELS,
  BITWUZLA_OPT_INPUT_FORMAT,
  BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT,
  BITWUZLA_OPT_OUTPUT_FORMAT,
  BITWUZLA_OPT_ENGINE,
  BITWUZLA_OPT_SAT_ENGINE,
  BITWUZLA_OPT_PRETTY_PRINT,
  BITWUZLA_OPT_EXIT_CODES,
  BITWUZLA_OPT_SEED,
  BITWUZLA_OPT_VERBOSITY,
  BITWUZLA_OPT_LOGLEVEL,
  BITWUZLA_OPT_REWRITE_LEVEL,
  BITWUZLA_OPT_SKELETON_PREPROC,
  BITWUZLA_OPT_ACKERMANN,
  BITWUZLA_OPT_BETA_REDUCE,
  BITWUZLA_OPT_ELIMINATE_ITES,
  BITWUZLA_OPT_ELIMINATE_SLICES,
  BITWUZLA_OPT_VAR_SUBST,
  BITWUZLA_OPT_UCOPT,
  BITWUZLA_OPT_MERGE_LAMBDAS,
  BITWUZLA_OPT_EXTRACT_LAMBDAS,
  BITWUZLA_OPT_NORMALIZE,
  BITWUZLA_OPT_NORMALIZE_ADD,
  BITWUZLA_OPT_FUN_PREPROP,
  BITWUZLA_OPT_FUN_PRESLS,
  BITWUZLA_OPT_FUN_DUAL_PROP,
  BITWUZLA_OPT_FUN_DUAL_PROP_QSORT,
  BITWUZLA_OPT_FUN_JUST,
  BITWUZLA_OPT_FUN_JUST_HEURISTIC,
  BITWUZLA_OPT_FUN_LAZY_SYNTHESIZE,
  BITWUZLA_OPT_FUN_EAGER_LEMMAS,
  BITWUZLA_OPT_FUN_STORE_LAMBDAS,
  BITWUZLA_OPT_PRINT_DIMACS,
  BITWUZLA_OPT_SLS_NFLIPS,
  BITWUZLA_OPT_SLS_STRATEGY,
  BITWUZLA_OPT_SLS_JUST,
  BITWUZLA_OPT_SLS_MOVE_GW,
  BITWUZLA_OPT_SLS_MOVE_RANGE,
  BITWUZLA_OPT_SLS_MOVE_SEGMENT,
  BITWUZLA_OPT_SLS_MOVE_RAND_WALK,
  BITWUZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
  BITWUZLA_OPT_SLS_MOVE_RAND_ALL,
  BITWUZLA_OPT_SLS_MOVE_RAND_RANGE,
  BITWUZLA_OPT_SLS_MOVE_PROP,
  BITWUZLA_OPT_SLS_MOVE_PROP_N_PROP,
  BITWUZLA_OPT_SLS_MOVE_PROP_N_SLS,
  BITWUZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
  BITWUZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
  BITWUZLA_OPT_SLS_USE_RESTARTS,
  BITWUZLA_OPT_SLS_USE_BANDIT,
  BITWUZLA_OPT_PROP_NPROPS,
  BITWUZLA_OPT_PROP_NUPDATES,
  BITWUZLA_OPT_PROP_ENTAILED,
  BITWUZLA_OPT_PROP_CONST_BITS,
  BITWUZLA_OPT_PROP_CONST_DOMAINS,
  BITWUZLA_OPT_PROP_USE_RESTARTS,
  BITWUZLA_OPT_PROP_USE_BANDIT,
  BITWUZLA_OPT_PROP_PATH_SEL,
  BITWUZLA_OPT_PROP_PROB_USE_INV_VALUE,
  BITWUZLA_OPT_PROP_PROB_FLIP_COND,
  BITWUZLA_OPT_PROP_PROB_FLIP_COND_CONST,
  BITWUZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
  BITWUZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
  BITWUZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
  BITWUZLA_OPT_PROP_PROB_CONC_FLIP,
  BITWUZLA_OPT_PROP_PROB_SLICE_FLIP,
  BITWUZLA_OPT_PROP_PROB_EQ_FLIP,
  BITWUZLA_OPT_PROP_PROB_AND_FLIP,
  BITWUZLA_OPT_PROP_PROB_RANDOM_INPUT,
  BITWUZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
  BITWUZLA_OPT_PROP_SKIP_NO_PROGRESS,
  BITWUZLA_OPT_PROP_USE_INV_LT_CONCAT,
  BITWUZLA_OPT_PROP_INFER_INEQ_BOUNDS,
  BITWUZLA_OPT_PROP_SEXT,
  BITWUZLA_OPT_PROP_XOR,
  BITWUZLA_OPT_PROP_SRA,
  BITWUZLA_OPT_AIGPROP_USE_RESTARTS,
  BITWUZLA_OPT_AIGPROP_USE_BANDIT,
  BITWUZLA_OPT_AIGPROP_NPROPS,
  BITWUZLA_OPT_QUANT_SYNTH,
  BITWUZLA_OPT_QUANT_DUAL_SOLVER,
  BITWUZLA_OPT_QUANT_SYNTH_LIMIT,
  BITWUZLA_OPT_QUANT_SYNTH_QI,
  BITWUZLA_OPT_QUANT_DER,
  BITWUZLA_OPT_QUANT_CER,
  BITWUZLA_OPT_QUANT_MINISCOPE,
  /* internal options --------------------------------------------------- */
  BITWUZLA_OPT_SORT_EXP,
  BITWUZLA_OPT_SORT_AIG,
  BITWUZLA_OPT_SORT_AIGVEC,
  BITWUZLA_OPT_SIMPLIFY_CONSTRAINTS,
  BITWUZLA_OPT_CHECK_UNSAT_ASSUMPTIONS,
  BITWUZLA_OPT_CHECK_MODEL,
  BITWUZLA_OPT_CHECK_UNCONSTRAINED,
  BITWUZLA_OPT_LS_SHARE_SAT,
  BITWUZLA_OPT_PARSE_INTERACTIVE,
  BITWUZLA_OPT_SAT_ENGINE_LGL_FORK,
  BITWUZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
  BITWUZLA_OPT_SAT_ENGINE_N_THREADS,
  BITWUZLA_OPT_SLT_ELIM,
  BITWUZLA_OPT_SIMP_NORMAMLIZE_ADDERS,
  BITWUZLA_OPT_DECLSORT_BV_WIDTH,
  BITWUZLA_OPT_QUANT_SYNTH_ITE_COMPLETE,
  BITWUZLA_OPT_QUANT_FIXSYNTH,
  BITWUZLA_OPT_RW_ZERO_LOWER_SLICE,
  BITWUZLA_OPT_NONDESTR_SUBST,
  BITWUZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
  BITWUZLA_OPT_PRODUCE_UNSAT_CORES,
  BITWUZLA_OPT_SMT_COMP_MODE,
  /* this MUST be the last entry! */
  BITWUZLA_OPT_NUM_OPTS,
};
typedef enum BitwuzlaOption BitwuzlaOption;

enum BitwuzlaKind
{
  BITWUZLA_KIND_AND,
  BITWUZLA_KIND_APPLY,
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
  BITWUZLA_KIND_BV_ROL,
  BITWUZLA_KIND_BV_ROR,
  BITWUZLA_KIND_BV_SADD_OVERFLOW,
  BITWUZLA_KIND_BV_SDIV_OVERFLOW,
  BITWUZLA_KIND_BV_SDIV,
  BITWUZLA_KIND_BV_SGE,
  BITWUZLA_KIND_BV_SGT,
  BITWUZLA_KIND_BV_SHL,
  BITWUZLA_KIND_BV_SHR,
  BITWUZLA_KIND_BV_SLE,
  BITWUZLA_KIND_BV_SLT,
  BITWUZLA_KIND_BV_SMOD,
  BITWUZLA_KIND_BV_SMUL_OVERFLOW,
  BITWUZLA_KIND_BV_SREM,
  BITWUZLA_KIND_BV_SSUB_OVERFLOW,
  BITWUZLA_KIND_BV_SUB,
  BITWUZLA_KIND_BV_UADD_OVERFLOW,
  BITWUZLA_KIND_BV_UDIV,
  BITWUZLA_KIND_BV_UGE,
  BITWUZLA_KIND_BV_UGT,
  BITWUZLA_KIND_BV_ULE,
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
  BITWUZLA_KIND_LAMBDA,
  BITWUZLA_KIND_NOT,
  BITWUZLA_KIND_OR,
  BITWUZLA_KIND_XOR,
  // indexed
  BITWUZLA_KIND_BV_EXTRACT,
  BITWUZLA_KIND_BV_REPEAT,
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
typedef uint32_t BitwuzlaSort;

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
                                  BitwuzlaSort domain[],
                                  BitwuzlaSort codomain);
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

BitwuzlaTerm *bitwuzla_mk_bv_value_uint32(Bitwuzla *bitwuzla,
                                          BitwuzlaSort sort,
                                          uint32_t value);

BitwuzlaTerm *bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                                   BitwuzlaTerm *bv_sign,
                                   BitwuzlaTerm *bv_exponent,
                                   BitwuzlaTerm *bv_significand);

BitwuzlaTerm *bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm);

BitwuzlaTerm *bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                                BitwuzlaKind kind,
                                BitwuzlaTerm *arg);

BitwuzlaTerm *bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                                BitwuzlaKind kind,
                                BitwuzlaTerm *arg0,
                                BitwuzlaTerm *arg1);

BitwuzlaTerm *bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                                BitwuzlaKind kind,
                                BitwuzlaTerm *arg0,
                                BitwuzlaTerm *arg1,
                                BitwuzlaTerm *arg2);

BitwuzlaTerm *bitwuzla_mk_term(Bitwuzla *bitwuzla,
                               BitwuzlaKind kind,
                               uint32_t argc,
                               BitwuzlaTerm *args[]);

BitwuzlaTerm *bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
                                         BitwuzlaKind kind,
                                         BitwuzlaTerm *arg,
                                         uint32_t idx);

BitwuzlaTerm *bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                                         BitwuzlaKind kind,
                                         BitwuzlaTerm *arg,
                                         uint32_t idx0,
                                         uint32_t idx1);

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

const BitwuzlaTerm **bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla);
const BitwuzlaTerm **bitwuzla_get_unsat_core(Bitwuzla *bitwuzla);

void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla);
void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla);

BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla);

BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term);

void bitwuzla_print_model(Bitwuzla *bitwuzla, const char *format, FILE *file);

void bitwuzla_dump_formula(Bitwuzla *bitwuzla, const char *format, FILE *file);

BitwuzlaResult bitwuzla_parse(Bitwuzla *bitwuzla,
                              FILE *infile,
                              const char *infile_name,
                              FILE *outfile,
                              char **error_msg,
                              int32_t *parsed_status,
                              bool *parsed_smt2);

BitwuzlaResult bitwuzla_parse_format(Bitwuzla *bitwuzla,
                                     const char *format,
                                     FILE *infile,
                                     const char *infile_name,
                                     FILE *outfile,
                                     char **error_msg,
                                     int32_t *parsed_status);

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

uint32_t bitwuzla_sort_bv_get_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_exp_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
uint32_t bitwuzla_sort_fp_get_sig_size(Bitwuzla *bitwuzla, BitwuzlaSort sort);
BitwuzlaSort bitwuzla_sort_array_get_index(Bitwuzla *bitwuzla,
                                           BitwuzlaSort sort);
BitwuzlaSort bitwuzla_sort_array_get_element(Bitwuzla *bitwuzla,
                                             BitwuzlaSort sort);
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

Bitwuzla *bitwuzla_term_get_bitwuzla(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_term_get_sort(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_term_array_get_index_sort(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_term_array_get_element_sort(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_term_fun_get_domain_sort(BitwuzlaTerm *term);
const BitwuzlaSort *bitwuzla_term_fun_get_domain_sorts(BitwuzlaTerm *term);
BitwuzlaSort bitwuzla_term_fun_get_codomain_sort(BitwuzlaTerm *term);

uint32_t bitwuzla_term_bv_get_size(BitwuzlaTerm *term);
uint32_t bitwuzla_term_fp_get_exp_size(BitwuzlaTerm *term);
uint32_t bitwuzla_term_fp_get_sig_size(BitwuzlaTerm *term);
uint32_t bitwuzla_term_fun_get_arity(BitwuzlaTerm *term);

const char *bitwuzla_term_get_symbol(BitwuzlaTerm *term);
void bitwuzla_term_set_symbol(BitwuzlaTerm *term, const char *symbol);

bool bitwuzla_term_is_array(BitwuzlaTerm *term);
bool bitwuzla_term_is_const(BitwuzlaTerm *term);
bool bitwuzla_term_is_fun(BitwuzlaTerm *term);
bool bitwuzla_term_is_var(BitwuzlaTerm *term);
bool bitwuzla_term_is_bound_var(BitwuzlaTerm *term);

bool bitwuzla_term_is_bv_value(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp_value(BitwuzlaTerm *term);
bool bitwuzla_term_is_rm_value(BitwuzlaTerm *term);

bool bitwuzla_term_is_bv(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp(BitwuzlaTerm *term);
bool bitwuzla_term_is_rm(BitwuzlaTerm *term);

bool bitwuzla_term_is_bv_value_zero(BitwuzlaTerm *term);
bool bitwuzla_term_is_bv_value_one(BitwuzlaTerm *term);
bool bitwuzla_term_is_bv_value_ones(BitwuzlaTerm *term);
bool bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm *term);
bool bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm *term);

bool bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm *term);
bool bitwuzla_term_is_fp_value_nan(BitwuzlaTerm *term);

bool bitwuzla_term_is_const_array(BitwuzlaTerm *term);

/* -------------------------------------------------------------------------- */

#if __cplusplus
}
#endif

/* -------------------------------------------------------------------------- */
#endif
