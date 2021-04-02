/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
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
  BITWUZLA_KIND_BV_COMP,
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
  BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
  BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
  BITWUZLA_KIND_FP_TO_SBV,
  BITWUZLA_KIND_FP_TO_UBV,

  BITWUZLA_NUM_KINDS,
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
typedef struct BitwuzlaSort BitwuzlaSort;

// TODO: add more option enums (check bzlatypes.h)

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

/**
 * Create a new Bitwuzla instance.
 *
 * The returned instance must be deleted via bitwuzla_delete().
 *
 * @return A pointer to the created Bitwuzla instance.
 *
 * @see bitwuzla_delete
 */
Bitwuzla *bitwuzla_new(void);

/**
 * Delete a Bitwuzla instance.
 *
 * The given instance must have been created via bitwuzla_new().
 *
 * @param bitwuzla The Bitwuzla instance to delete.
 *
 * @see bitwuzla_new
 */
void bitwuzla_delete(Bitwuzla *bitwuzla);

/**
 * Reset a Bitwuzla instance.
 *
 * This deletes the given instance and creates a new instance in place.
 * The given instance must have been created via bitwuzla_new().
 *
 * @param bitwuzla The Bitwuzla instance to reset.
 *
 * @see bitwuzla_new
 */
void bitwuzla_reset(Bitwuzla *bitwuzla);

/**
 * Print copyright information.
 *
 * @param bitwuzla The Bitwuzla instance.
 */
const char *bitwuzla_copyright(Bitwuzla *bitwuzla);

/**
 * Print version information.
 *
 * @param bitwuzla The Bitwuzla instance.
 */
const char *bitwuzla_version(Bitwuzla *bitwuzla);

/**
 * If termination callback function has been configured via
 * bitwuzla_set_termination_callback(), call this termination function.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return True if \p bitwuzla has been terminated.
 */
bool bitwuzla_terminate(Bitwuzla *bitwuzla);

/**
 * Configure a termination callback function.
 *
 * The \p state of the callback can be retrieved via
 * bitwuzla_get_termination_callback_state().
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param fun The callback function, returns a value > 0 if \p bitwuzla has
 *            been terminated.
 * @param state The argument to the callback function.
 *
 * @see bitwuzla_terminate
 * @see bitwuzla_get_termination_callback_state
 */
void bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                       int32_t (*fun)(void *),
                                       void *state);

/**
 * Get the state of the termination callback function.
 *
 * The returned object representing the state of the callback corresponds to
 * the \p state configured as argument to the callback function via
 * bitwuzla_get_termination_callback_state().
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return The object passed as argument \p state to the callback function.
 *
 * @see bitwuzla_terminate
 * @see bitwuzla_set_termination_callback
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
 * @param fun The callback function, the argument \p msg explains the reason
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
 * @see BitwuzlaOption
 */
void bitwuzla_set_option(Bitwuzla *bitwuzla,
                         BitwuzlaOption option,
                         uint32_t val);

/**
 * Get the current value of an option.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param option The option.
 *
 * @return The option value.
 *
 * @see BitwuzlaOption
 */
uint32_t bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option);

/**
 * Create an array sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param index The index sort of the array sort.
 * @param element The element sort of the array sort.
 *
 * @return An array sort which maps sort \p index to sort \p element.
 *
 * @see bitwuzla_sort_is_array
 * @see bitwuzla_sort_array_get_index
 * @see bitwuzla_sort_array_get_element
 * @see bitwuzla_term_is_array
 * @see bitwuzla_term_array_get_index_sort
 * @see bitwuzla_term_array_get_element_sort
 */
BitwuzlaSort *bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
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
BitwuzlaSort *bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla);

/**
 * Create a bit-vector sort of given size.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size The size of the bit-vector sort.
 *
 * @return A bit-vector sort of given size.
 *
 * @see bitwuzla_sort_is_bv
 * @see bitwuzla_sort_bv_get_size
 * @see bitwuzla_term_is_bv
 * @see bitwuzla_term_bv_get_size
 */
BitwuzlaSort *bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size);

/**
 * Create a floating-point sort of given exponent and significand size.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param exp_size The size of the exponent.
 * @param sig_size The size of the significand (including sign bit).
 *
 * @return A floating-point sort of given format.
 *
 * @see bitwuzla_sort_is_fp
 * @see bitwuzla_sort_fp_get_exp_size
 * @see bitwuzla_sort_fp_get_sig_size
 * @see bitwuzla_term_is_fp
 * @see bitwuzla_term_fp_get_exp_size
 * @see bitwuzla_term_fp_get_sig_size
 */
BitwuzlaSort *bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla,
                                  uint32_t exp_size,
                                  uint32_t sig_size);

/**
 * Create a function sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param arity The number of arguments to the function.
 * @param domain The domain sorts (the sorts of the arguments). The number of
 *               sorts in this vector must match \p arity.
 * @param codomain The codomain sort (the sort of the return value).
 *
 * @return A function sort of given domain and codomain sorts.
 *
 * @see bitwuzla_sort_is_fun
 * @see bitwuzla_sort_fun_get_arity
 * @see bitwuzla_sort_fun_get_domain
 * @see bitwuzla_sort_fun_get_domain_sorts
 * @see bitwuzla_sort_fun_get_codomain
 * @see bitwuzla_term_is_fun
 * @see bitwuzla_term_fun_get_arity
 * @see bitwuzla_term_fun_get_domain_sort
 * @see bitwuzla_term_fun_get_domain_sorts
 * @see bitwuzla_term_fun_get_codomain_sort
 */
BitwuzlaSort *bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                                   uint32_t arity,
                                   BitwuzlaSort *domain[],
                                   const BitwuzlaSort *codomain);

/**
 * Create a roundingmode sort.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A roundingmode sort.
 *
 * @see bitwuzla_sort_is_rm
 * @see bitwuzla_term_is_rm
 */
BitwuzlaSort *bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla);

/**
 * Create a true value.
 *
 * @note This creates a bit-vector value 1 of size 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A term representing the bit-vector value 1 of size 1.
 */
BitwuzlaTerm *bitwuzla_mk_true(Bitwuzla *bitwuzla);

/**
 * Create a false value.
 *
 * @note This creates a bit-vector value 0 of size 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return A term representing the bit-vector value 0 of size 1.
 */
BitwuzlaTerm *bitwuzla_mk_false(Bitwuzla *bitwuzla);

/**
 * Create a bit-vector value zero.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value 0 of given sort.
 *
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort);

/**
 * Create a bit-vector value one.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value 1 of given sort.
 *
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, const BitwuzlaSort *sort);

/**
 * Create a bit-vector value where all bits are set to 1.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value of given sort
 *         where all bits are set to 1.
 *
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, const BitwuzlaSort *sort);

/**
 * Create a bit-vector minimum signed value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 1 and all remaining bits are set to 0.
 *
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla,
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
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla,
                                        const BitwuzlaSort *sort);

/**
 * Create a floating-point positive zero value (+zero).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point positive zero value of given
 *         floating-point sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla,
                                      const BitwuzlaSort *sort);

/**
 * Create a floating-point negative zero value (-zero).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point negative zero value of given
 *         floating-point sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla,
                                      const BitwuzlaSort *sort);

/**
 * Create a floating-point positive infinity value (+oo).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point positive infinity value of
 *         given floating-point sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla,
                                     const BitwuzlaSort *sort);

/**
 * Create a floating-point negative infinity value (-oo).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 *
 * @return A term representing the floating-point negative infinity value of
 *         given floating-point sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla,
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
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, const BitwuzlaSort *sort);

/**
 * Create a bit-vector value from its string representation.
 *
 * Parameter \p base determines the base of the string representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param value A string representing the value.
 * @param base The base in which the string is given.
 *
 * @return A term representing the bit-vector value of given sort.
 *
 * @see bitwuzla_mk_bv_sort
 * @see BitwuzlaBase
 */
BitwuzlaTerm *bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                                   const BitwuzlaSort *sort,
                                   const char *value,
                                   BitwuzlaBVBase base);

/**
 * Create a bit-vector value from its unsigned integer representation.
 *
 * @note If given value does not fit into a bit-vector of given size (sort),
 *       the value is truncated to fit.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term representing the bit-vector value of given sort.
 *
 * @see bitwuzla_mk_bv_sort
 */
BitwuzlaTerm *bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
                                          const BitwuzlaSort *sort,
                                          uint64_t value);

/**
 * Create a floating-point value from its IEEE 754 standard representation
 * given as three bitvectors representing the sign bit, the exponent and the
 * significand.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param bv_sign The sign bit.
 * @param bv_exponent The exponent bit-vector.
 * @param bv_significand The significand bit-vector.
 *
 * @return A term representing the floating-point value.
 */
BitwuzlaTerm *bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                                   const BitwuzlaTerm *bv_sign,
                                   const BitwuzlaTerm *bv_exponent,
                                   const BitwuzlaTerm *bv_significand);

/**
 * Create a floating-point value from its real representation, given as a
 * decimal string, with respect to given roundingmode.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param rm The roundingmode.
 * @param real The decimal string representing a real value.
 *
 * @return A term representing the floating-point value of given sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_value_from_real(Bitwuzla *bitwuzla,
                                             const BitwuzlaSort *sort,
                                             const BitwuzlaTerm *rm,
                                             const char *real);

/**
 * Create a floating-point value from its rational representation, given as a
 * two decimal strings representing the numerator and denominator, with respect
 * to given roundingmode.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the value.
 * @param rm The roundingmode.
 * @param num The decimal string representing the numerator.
 * @param den The decimal string representing the denominator.
 *
 * @return A term representing the floating-point value of given sort.
 *
 * @see bitwuzla_mk_fp_sort
 */
BitwuzlaTerm *bitwuzla_mk_fp_value_from_rational(Bitwuzla *bitwuzla,
                                                 const BitwuzlaSort *sort,
                                                 const BitwuzlaTerm *rm,
                                                 const char *num,
                                                 const char *den);

/**
 * Create a roundingmode value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param rm The rounding mode value.
 *
 * @return A term representing the roundingmode value.
 *
 * @see BitwuzlaRoundingMode
 */
BitwuzlaTerm *bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm);

/**
 * Create a term of given kind with one argument term.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param kind The operator kind.
 * @param arg The argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term1(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term2(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term3(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term(Bitwuzla *bitwuzla,
                               BitwuzlaKind kind,
                               uint32_t argc,
                               BitwuzlaTerm *args[]);

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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
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
 * @see BitwuzlaKind
 */
BitwuzlaTerm *bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                                       BitwuzlaKind kind,
                                       uint32_t argc,
                                       BitwuzlaTerm *args[],
                                       uint32_t idxc,
                                       uint32_t idxs[]);

/**
 * Create a constant of given sort with given symbol.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the constant.
 * @param symbol The symbol of the constant.
 *
 * @return A term representing the constant.
 *
 * @see bitwuzla_mk_array_sort
 * @see bitwuzla_mk_bool_sort
 * @see bitwuzla_mk_bv_sort
 * @see bitwuzla_mk_fp_sort
 * @see bitwuzla_mk_fun_sort
 * @see bitwuzla_mk_rm_sort
 */
BitwuzlaTerm *bitwuzla_mk_const(Bitwuzla *bitwuzla,
                                const BitwuzlaSort *sort,
                                const char *symbol);

/**
 * Create a one-dimensional constant array of given sort, initialized with
 * given value.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the array.
 * @param value The value to initialize the elements of the array with.
 *
 * @return A term representing a constant array of given sort.
 *
 * @see bitwuzla_mk_array_sort
 */
BitwuzlaTerm *bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                                      const BitwuzlaSort *sort,
                                      const BitwuzlaTerm *value);

/**
 * Create a variable of given sort with given symbol.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param sort The sort of the variable.
 * @param symbol The symbol of the variable.
 *
 * @return A term representing the variable.
 *
 * @see bitwuzla_mk_bool_sort
 * @see bitwuzla_mk_bv_sort
 * @see bitwuzla_mk_fp_sort
 * @see bitwuzla_mk_fun_sort
 * @see bitwuzla_mk_rm_sort
 */
BitwuzlaTerm *bitwuzla_mk_var(Bitwuzla *bitwuzla,
                              const BitwuzlaSort *sort,
                              const char *symbol);

/**
 * Push context levels.
 *
 * Requires that incremental solving has been enabled via bitwuzla_set_opt().
 *
 * @note Assumptions added via this bitwuzla_assume() are not affected by
 *       context level changes and are only valid until the next
 *       bitwuzla_check_sat() call, no matter at which level they were assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to push.
 *
 * @see bitwuzla_set_opt
 */
void bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels);

/**
 * Pop context levels.
 *
 * Requires that incremental solving has been enabled via bitwuzla_set_opt().
 *
 * @note Assumptions added via this bitwuzla_assume() are not affected by
 *       context level changes and are only valid until the next
 *       bitwuzla_check_sat() call, no matter at which level they were assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to pop.
 *
 * @see bitwuzla_set_opt
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
 * Requires that incremental solving has been enabled via bitwuzla_set_opt().
 *
 * @note Assumptions added via this function are not affected by context level
 *       changes and are only valid until the next bitwuzla_check_sat() call,
 *       no matter at which level they were assumed.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The formula to assume.
 *
 * @see bitwuzla_set_opt
 * @see bitwuzla_is_unsat_assumption
 * @see bitwuzla_get_unsat_assumptions
 */
void bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Determine if an assumption is an unsat assumption.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Boolector is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that incremental solving has been enabled via bitwuzla_set_opt().
 *
 * Requires that a prior bitwuzla_check_sat() query returned BITWUZLA_UNSAT.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The assumption to check for.
 *
 * @return True if given assumption is an unsat assumption.
 *
 * @see bitwuzla_set_opt
 * @see bitwuzla_assume
 * @see bitwuzla_check_sat
 */
bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Get the set of unsat assumptions.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Boolector is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that incremental solving has been enabled via bitwuzla_set_opt().
 *
 * Requires that a prior bitwuzla_check_sat() query returned BITWUZLA_UNSAT.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assumptions of size \p size.
 *
 * @see bitwuzla_set_opt
 * @see bitwuzla_assume
 * @see bitwuzla_check_sat
 */
BitwuzlaTerm **bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size);

/**
 * Get the set unsat core (unsat assertions).
 *
 * The unsat core consists of the set of assertions that force an input formula
 * to become unsatisfiable.
 *
 * Requires that a prior bitwuzla_check_sat() query returned BITWUZLA_UNSAT.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assertions of size \p size.
 *
 * @see bitwuzla_assert
 * @see bitwuzla_check_sat
 */
BitwuzlaTerm **bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size);

/**
 * Assert all added assumptions.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @see bitwuzla_assume
 */
void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla);

/**
 * Reset all added assumptions.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @see bitwuzla_assume
 */
void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla);

/**
 * Simplify the current input formula.
 *
 * @note Assumptions are not considered for simplification.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return BITWUZLA_SAT if the input formula was simplified to true,
 *         BITWUZLA_UNSAT if it was simplified to false, and BITWUZLA_UNKNOWN
 *         otherwise.
 *
 * @see bitwuzla_assert
 * @see BitwuzlaResult
 */
BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla);

/**
 * Check satisfiability of current input formula.
 *
 * An input formula consists of assertions added via bitwuzla_assert().  You
 * can guide the search for a solution by making assumptions via
 * bitwuzla_assume().
 *
 * @note Assertions and assumptions are combined via Boolean and.  Multiple
 *       calls to this function require enabling incremental solving via
 *       bitwuzla_set_opt().
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return BITWUZLA_SAT if the input formula is satisfiable and BITWUZLA_UNSAT
 *         if it is unsatisfiable, and BITWUZLA_UNKNOWN when neither
 *         satisfiability nor unsatisfiability was determined. This can happen
 *         when \p bitwuzla was terminated via a termination callback.
 *
 * @see bitwuzla_assert
 * @see bitwuzla_assume
 * @see bitwuzla_set_opt
 * @see BitwuzlaResult
 */
BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

/**
 * Get a term representing the model value of a given term.
 *
 * Requires that a prior bitwuzla_check_sat() query returned BITWUZLA_SAT.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 *
 * @return A term representing the model value of term \p term.
 *
 * @see bitwuzla_check_sat
 */
BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/**
 * Print a model for the current input formula.
 *
 * Requires that a prior bitwuzla_check_sat() query returned BITWUZLA_SAT.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The output format for printing the model. Either "btor" for
 *               the BTOR format, or "smt2" for the SMT-LIB v2 format.
 * @param file The file to print the model to.
 *
 * @see bitwuzla_check_sat
 */
void bitwuzla_print_model(Bitwuzla *bitwuzla, const char *format, FILE *file);

/**
 * Print the current input formula.
 *
 * Requires that incremental solving is not enabled.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The output format for printing the formula. Either "aiger_ascii"
 *               for the AIGER ascii format, "aiger_binary" for the binary
 *               AIGER format, "btor" for the BTOR format, or "smt2" for the
 *               SMT-LIB v2 format.
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
 * @return BITWUZLA_SAT if the input formula was simplified to true,
 *         BITWUZLA_UNSAT if it was simplified to false, and BITWUZLA_UNKNOWN
 *         otherwise.
 *
 * @see bitwuzla_parse_format
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
 * @param format The input format for printing the model. Either "btor" for
 *               the BTOR format, "btor2" for the BTOR2 format, or "smt2" for
 *               the SMT-LIB v2 format.
 * @param infile The input file.
 * @param infile_name The name of the input file.
 * @param outfile The output file.
 * @param error_msg Output parameter, stores an error message in case a parse
 *                  error occurred, else \c NULL.
 * @param parsed_status Output parameter, stores the status of the input in case
 *                      of SMT-LIB v2 input, if given.
 *
 * @return BITWUZLA_SAT if the input formula was simplified to true,
 *         BITWUZLA_UNSAT if it was simplified to false, and BITWUZLA_UNKNOWN
 *         otherwise.
 *
 * @see bitwuzla_parse
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
 * @return The resulting from this substitution.
 */
BitwuzlaTerm *bitwuzla_substitute_term(Bitwuzla *bitwuzla,
                                       const BitwuzlaTerm *term,
                                       size_t map_size,
                                       BitwuzlaTerm *map_keys[],
                                       BitwuzlaTerm *map_values[]);

/**
 * Substitute a set of keys with their corresponding values in the set of given
 * terms.
 *
 * The terms in \p terms are replaced with the terms resulting from this
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
                               BitwuzlaTerm *terms[],
                               size_t map_size,
                               BitwuzlaTerm *map_keys[],
                               BitwuzlaTerm *map_values[]);

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
BitwuzlaSort *bitwuzla_sort_array_get_index(const BitwuzlaSort *sort);

/**
 * Get the element sort of an array sort.
 *
 * Requires that given sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return The element sort of the array sort.
 */
BitwuzlaSort *bitwuzla_sort_array_get_element(const BitwuzlaSort *sort);

/**
 * Get the domain sorts of a function sort, wrapped into a single sort.
 *
 * Requires that given sort is a function sort.
 *
 * @note The returned sort is a tuple sort consisting of the domain sorts of
 *       the given function sort. Tuple sorts are internal only and cannot be
 *       created via the Api.
 *
 * @param sort The sort.
 *
 * @return The domain sorts of the function sort.
 */
BitwuzlaSort *bitwuzla_sort_fun_get_domain(const BitwuzlaSort *sort);

/**
 * Get the domain sorts of a function sort.
 *
 * The domain sorts are returned as a \c NULL terminated array of sorts.  
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return The domain sorts of the function sort as a \c NULL terminated array.
 */
BitwuzlaSort **bitwuzla_sort_fun_get_domain_sorts(const BitwuzlaSort *sort);

/**
 * Get the codomain sort of a function sort.
 *
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return The codomain sort of the function sort.
 */
BitwuzlaSort *bitwuzla_sort_fun_get_codomain(const BitwuzlaSort *sort);

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
 * @return True if \p sort is an array sort.
 */
bool bitwuzla_sort_is_array(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a bit-vector sort.
 *
 * @param sort The sort.
 *
 * @return True if \p sort is a bit-vector sort.
 */
bool bitwuzla_sort_is_bv(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return True if \p sort is a floating-point sort.
 */
bool bitwuzla_sort_is_fp(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return True if \p sort is a function sort.
 */
bool bitwuzla_sort_is_fun(const BitwuzlaSort *sort);

/**
 * Determine if a sort is a roundingmode sort.
 *
 * @param sort The sort.
 *
 * @return True if \p sort is a roundingmode sort.
 */
bool bitwuzla_sort_is_rm(const BitwuzlaSort *sort);

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
 * @param size Output parameter, stores the number of children of \p term.
 *
 * @return The children of \p term as an array of terms.
 */
BitwuzlaTerm **bitwuzla_term_get_children(const BitwuzlaTerm *term,
                                          size_t *size);

/**
 * Get the indices of an indexed term.
 *
 * Requires that given term is an indexed term.
 *
 * @param term The term.
 * @param size Output parameter, stores the number of indices of \p term.
 *
 * @return The children of \p term as an array of terms.
 */
uint32_t *bitwuzla_term_get_indices(const BitwuzlaTerm *term, size_t *size);

/**
 * Determine if a term is an indexed term.
 *
 * @param term The term.
 *
 * @return True if \p term is an indexed term.
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
BitwuzlaSort *bitwuzla_term_get_sort(const BitwuzlaTerm *term);

/**
 * Get the index sort of an array term.
 *
 * Requires that given term is an array or a BITWUZLA_KIND_ARRAY_STORE term.
 *
 * @param term The term.
 *
 * @return The index sort of the array term.
 */
BitwuzlaSort *bitwuzla_term_array_get_index_sort(const BitwuzlaTerm *term);

/**
 * Get the element sort of an array term.
 *
 * Requires that given term is an array or a store term.
 *
 * @param term The term.
 *
 * @return The element sort of the array term.
 */
BitwuzlaSort *bitwuzla_term_array_get_element_sort(const BitwuzlaTerm *term);

/**
 * Get the domain sorts of a function term, wrapped into a single sort.
 *
 * Requires that given term is an uninterpreted function, a lambda term, a
 * store term, an ite term over function terms.
 *
 * @note The returned sort is a tuple sort consisting of the domain sorts of
 *       the given function sort. Tuple sorts are internal only and cannot be
 *       created via the Api.
 *
 * @param term The term.
 *
 * @return The domain sorts of the function term.
 */
BitwuzlaSort *bitwuzla_term_fun_get_domain_sort(const BitwuzlaTerm *term);

/**
 * Get the domain sorts of a function term.
 *
 * The domain sorts are returned as a \c NULL terminated array of sorts.  
 * Requires that given term is an uninterpreted function, a lambda term, a
 * store term, an ite term over function terms.
 *
 * @param term The term.
 *
 * @return The domain sorts of the function term as a \c NULL terminated array.
 */
BitwuzlaSort **bitwuzla_term_fun_get_domain_sorts(const BitwuzlaTerm *term);

/**
 * Get the codomain sort of a function term.
 *
 * Requires that given term is an uninterpreted function, a lambda term, a
 * store term, an ite term over function terms.
 *
 * @param term The term.
 *
 * @return The codomain sort of the function term.
 */
BitwuzlaSort *bitwuzla_term_fun_get_codomain_sort(const BitwuzlaTerm *term);

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
 * Get the aritye of a function term.
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
 * @return The symbol of \p term. \c NULL if no symbol is defined.
 */
const char *bitwuzla_term_get_symbol(const BitwuzlaTerm *term);

/**
 * Set the symbol of a term.
 *
 * @param term The term.
 * @param symbol The symbol.
 */
void bitwuzla_term_set_symbol(BitwuzlaTerm *term, const char *symbol);

/**
 * Determine if the sorts of two terms are equal.
 *
 * @param term0 The first term.
 * @param term1 The second term.
 *
 * @return True if the sorts of \p term0 and \p term1 are equal.
 */
bool bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
                                 const BitwuzlaTerm *term1);

/**
 * Determine if a term is an array term.
 *
 * @param term The term.
 *
 * @return True if \p term is an array term.
 */
bool bitwuzla_term_is_array(const BitwuzlaTerm *term);

/**
 * Determine if a term is a constant.
 *
 * @param term The term.
 *
 * @return True if \p term is a constant.
 */
bool bitwuzla_term_is_const(const BitwuzlaTerm *term);

/**
 * Determine if a term is a function.
 *
 * @param term The term.
 *
 * @return True if \p term is a function.
 */
bool bitwuzla_term_is_fun(const BitwuzlaTerm *term);

/**
 * Determine if a term is a variable.
 *
 * @param term The term.
 *
 * @return True if \p term is a variable.
 */
bool bitwuzla_term_is_var(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bound variable.
 *
 * @param term The term.
 *
 * @return True if \p term is a variable and bound.
 */
bool bitwuzla_term_is_bound_var(const BitwuzlaTerm *term);

/**
 * Determine if a term is a value.
 *
 * @param term The term.
 *
 * @return True if \p term is a value.
 */
bool bitwuzla_term_is_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector value.
 */
bool bitwuzla_term_is_bv_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point value.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point value.
 */
bool bitwuzla_term_is_fp_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a roundingmode value.
 *
 * @param term The term.
 *
 * @return True if \p term is a roundingmode value.
 */
bool bitwuzla_term_is_rm_value(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector term.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector term.
 */
bool bitwuzla_term_is_bv(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point term.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point term.
 */
bool bitwuzla_term_is_fp(const BitwuzlaTerm *term);

/**
 * Determine if a term is a roundingmode term.
 *
 * @param term The term.
 *
 * @return True if \p term is a roundingmode term.
 */
bool bitwuzla_term_is_rm(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value representing zero.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector zero value.
 */
bool bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value representing one.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector one value.
 */
bool bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector value with all bits set to one.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector value with all bits set to one.
 */
bool bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector minimum signed value.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector value with the most significant bit
 *         set to 1 and all other bits set to 0.
 */
bool bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term);

/**
 * Determine if a term is a bit-vector maximum signed value.
 *
 * @param term The term.
 *
 * @return True if \p term is a bit-vector value with the most significant bit
 *         set to 0 and all other bits set to 1.
 */
bool bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point positive zero (+zero) value.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point +zero value.
 */
bool bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point value negative zero (-zero).
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point value negative zero.
 */
bool bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point positive infinity (+oo) value.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point +oo value.
 */
bool bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point negative infinity (-oo) value.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point -oo value.
 */
bool bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term);

/**
 * Determine if a term is a floating-point NaN value.
 *
 * @param term The term.
 *
 * @return True if \p term is a floating-point NaN value.
 */
bool bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term);

/**
 * Determine if a term is a constant array.
 *
 * @param term The term.
 *
 * @return True if \p term is a constant array.
 */
bool bitwuzla_term_is_const_array(const BitwuzlaTerm *term);

/**
 * Print term .
 *
 * @param term The term.
 * @param format The output format for printing the term. Either "btor" for the
 *               BTOR format, or "smt2" for the SMT-LIB v2 format.
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
