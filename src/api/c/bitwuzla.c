/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bitwuzla.h"

#include "bzlaconfig.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaparse.h"
#include "bzlaprintmodel.h"
#include "bzlasubst.h"
#include "dumper/bzladumpaig.h"
#include "dumper/bzladumpbtor.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlaabort.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */

BZLA_DECLARE_STACK(BitwuzlaTermConstPtr, const BitwuzlaTerm *);
BZLA_DECLARE_STACK(BitwuzlaTermConstPtrPtr, const BitwuzlaTerm **);
BZLA_DECLARE_STACK(BitwuzlaConstSortPtr, const BitwuzlaSort *);
BZLA_DECLARE_STACK(BzlaConstCharPtr, const char *);

/* -------------------------------------------------------------------------- */

struct Bitwuzla
{
  /* Non-simplified assumptions as assumed via bitwuzla_assume. */
  BitwuzlaTermConstPtrStack d_assumptions;
  /* Unsat assumptions of current bitwuzla_get_unsat_assumptions query. */
  BitwuzlaTermConstPtrStack d_unsat_assumptions;
  /* Unsat core of the current bitwuzla_get_unsat_core query. */
  BitwuzlaTermConstPtrStack d_unsat_core;
  /* Children stack for bitwuzla_term_get_children. */
  BitwuzlaTermConstPtrStack d_term_children;
  /* Indices populated by bitwuzla_term_get_indices. */
  uint32_t d_term_indices[2];
  /* Domain sorts of current bitwuzla_term_fun_get_domain_sorts query. */
  BitwuzlaConstSortPtrStack d_fun_domain_sorts;
  /* Domain sorts of current bitwuzla_sort_fun_get_domain_sorts query. */
  BitwuzlaConstSortPtrStack d_sort_fun_domain_sorts;
  /* String populated by bitwuzla_get_bv_value. */
  char *d_bv_value;
  /* Strings populated by bitwuzla_get_fp_value. */
  char *d_fp_significand;
  char *d_fp_exponent;
  /* Strings populated by bitwuzla_get_array_value. */
  BitwuzlaTermConstPtrStack d_array_indices;
  BitwuzlaTermConstPtrStack d_array_values;
  /* Strings populated by bitwuzla_get_fun_value. */
  BitwuzlaTermConstPtrStack d_fun_args;
  BitwuzlaTermConstPtrPtrStack d_fun_args_ptr;
  BitwuzlaTermConstPtrStack d_fun_values;
  BzlaConstCharPtrStack d_option_info_values;
  /* Map internal sort id to external sort wrapper. */
  BzlaIntHashTable *d_sort_map;
  /* Internal solver. */
  Bzla *d_bzla;
  /* API memory manager. */
  BzlaMemMgr *d_mm;
};

struct BitwuzlaSort
{
  /* Internal sort. */
  BzlaSortId d_bzla_sort;
  /* Associated solver. */
  Bitwuzla *d_bzla;
};

static BzlaOption bzla_options[BITWUZLA_OPT_NUM_OPTS] = {
    [BITWUZLA_OPT_AIGPROP_NPROPS]          = BZLA_OPT_AIGPROP_NPROPS,
    [BITWUZLA_OPT_AIGPROP_USE_BANDIT]      = BZLA_OPT_AIGPROP_USE_BANDIT,
    [BITWUZLA_OPT_AIGPROP_USE_RESTARTS]    = BZLA_OPT_AIGPROP_USE_RESTARTS,
    [BITWUZLA_OPT_CHECK_MODEL]             = BZLA_OPT_CHECK_MODEL,
    [BITWUZLA_OPT_CHECK_UNCONSTRAINED]     = BZLA_OPT_CHECK_UNCONSTRAINED,
    [BITWUZLA_OPT_CHECK_UNSAT_ASSUMPTIONS] = BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS,
    [BITWUZLA_OPT_DECLSORT_BV_WIDTH]       = BZLA_OPT_DECLSORT_BV_WIDTH,
    [BITWUZLA_OPT_ENGINE]                  = BZLA_OPT_ENGINE,
    [BITWUZLA_OPT_EXIT_CODES]              = BZLA_OPT_EXIT_CODES,
    [BITWUZLA_OPT_FUN_DUAL_PROP]           = BZLA_OPT_FUN_DUAL_PROP,
    [BITWUZLA_OPT_FUN_DUAL_PROP_QSORT]     = BZLA_OPT_FUN_DUAL_PROP_QSORT,
    [BITWUZLA_OPT_FUN_EAGER_LEMMAS]        = BZLA_OPT_FUN_EAGER_LEMMAS,
    [BITWUZLA_OPT_FUN_JUST]                = BZLA_OPT_FUN_JUST,
    [BITWUZLA_OPT_FUN_JUST_HEURISTIC]      = BZLA_OPT_FUN_JUST_HEURISTIC,
    [BITWUZLA_OPT_FUN_LAZY_SYNTHESIZE]     = BZLA_OPT_FUN_LAZY_SYNTHESIZE,
    [BITWUZLA_OPT_FUN_PREPROP]             = BZLA_OPT_FUN_PREPROP,
    [BITWUZLA_OPT_FUN_PRESLS]              = BZLA_OPT_FUN_PRESLS,
    [BITWUZLA_OPT_FUN_STORE_LAMBDAS]       = BZLA_OPT_FUN_STORE_LAMBDAS,
    [BITWUZLA_OPT_INCREMENTAL]             = BZLA_OPT_INCREMENTAL,
    [BITWUZLA_OPT_INPUT_FORMAT]            = BZLA_OPT_INPUT_FORMAT,
    [BITWUZLA_OPT_LOGLEVEL]                = BZLA_OPT_LOGLEVEL,
    [BITWUZLA_OPT_LS_SHARE_SAT]            = BZLA_OPT_LS_SHARE_SAT,
    [BITWUZLA_OPT_OUTPUT_FORMAT]           = BZLA_OPT_OUTPUT_FORMAT,
    [BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT]    = BZLA_OPT_OUTPUT_NUMBER_FORMAT,
    [BITWUZLA_OPT_PARSE_INTERACTIVE]       = BZLA_OPT_PARSE_INTERACTIVE,
    [BITWUZLA_OPT_PP_ACKERMANN]            = BZLA_OPT_PP_ACKERMANN,
    [BITWUZLA_OPT_PP_BETA_REDUCE]          = BZLA_OPT_PP_BETA_REDUCE,
    [BITWUZLA_OPT_PP_ELIMINATE_EXTRACTS]   = BZLA_OPT_PP_ELIMINATE_EXTRACTS,
    [BITWUZLA_OPT_PP_ELIMINATE_ITES]       = BZLA_OPT_PP_ELIMINATE_ITES,
    [BITWUZLA_OPT_PP_EXTRACT_LAMBDAS]      = BZLA_OPT_PP_EXTRACT_LAMBDAS,
    [BITWUZLA_OPT_PP_MERGE_LAMBDAS]        = BZLA_OPT_PP_MERGE_LAMBDAS,
    [BITWUZLA_OPT_PP_NONDESTR_SUBST]       = BZLA_OPT_PP_NONDESTR_SUBST,
    [BITWUZLA_OPT_PP_NORMALIZE_ADD]        = BZLA_OPT_PP_NORMALIZE_ADD,
    [BITWUZLA_OPT_PP_SKELETON_PREPROC]     = BZLA_OPT_PP_SKELETON_PREPROC,
    [BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION] =
        BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION,
    [BITWUZLA_OPT_PP_VAR_SUBST]        = BZLA_OPT_PP_VAR_SUBST,
    [BITWUZLA_OPT_PRETTY_PRINT]        = BZLA_OPT_PRETTY_PRINT,
    [BITWUZLA_OPT_PRINT_DIMACS]        = BZLA_OPT_PRINT_DIMACS,
    [BITWUZLA_OPT_PRODUCE_MODELS]      = BZLA_OPT_PRODUCE_MODELS,
    [BITWUZLA_OPT_PRODUCE_UNSAT_CORES] = BZLA_OPT_PRODUCE_UNSAT_CORES,
    [BITWUZLA_OPT_PROP_ASHR]           = BZLA_OPT_PROP_ASHR,
    [BITWUZLA_OPT_PROP_CONST_BITS]     = BZLA_OPT_PROP_CONST_BITS,
    [BITWUZLA_OPT_PROP_CONST_DOMAINS]  = BZLA_OPT_PROP_CONST_DOMAINS,
    [BITWUZLA_OPT_PROP_ENTAILED]       = BZLA_OPT_PROP_ENTAILED,
    [BITWUZLA_OPT_PROP_FLIP_COND_CONST_DELTA] =
        BZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
    [BITWUZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL] =
        BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
    [BITWUZLA_OPT_PROP_INFER_INEQ_BOUNDS]   = BZLA_OPT_PROP_INFER_INEQ_BOUNDS,
    [BITWUZLA_OPT_PROP_NO_MOVE_ON_CONFLICT] = BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
    [BITWUZLA_OPT_PROP_NPROPS]              = BZLA_OPT_PROP_NPROPS,
    [BITWUZLA_OPT_PROP_NUPDATES]            = BZLA_OPT_PROP_NUPDATES,
    [BITWUZLA_OPT_PROP_PATH_SEL]            = BZLA_OPT_PROP_PATH_SEL,
    [BITWUZLA_OPT_PROP_PROB_AND_FLIP]       = BZLA_OPT_PROP_PROB_AND_FLIP,
    [BITWUZLA_OPT_PROP_PROB_EQ_FLIP]        = BZLA_OPT_PROP_PROB_EQ_FLIP,
    [BITWUZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE] =
        BZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
    [BITWUZLA_OPT_PROP_PROB_FLIP_COND] = BZLA_OPT_PROP_PROB_FLIP_COND,
    [BITWUZLA_OPT_PROP_PROB_FLIP_COND_CONST] =
        BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
    [BITWUZLA_OPT_PROP_PROB_RANDOM_INPUT]  = BZLA_OPT_PROP_PROB_RANDOM_INPUT,
    [BITWUZLA_OPT_PROP_PROB_SLICE_FLIP]    = BZLA_OPT_PROP_PROB_SLICE_FLIP,
    [BITWUZLA_OPT_PROP_PROB_SLICE_KEEP_DC] = BZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
    [BITWUZLA_OPT_PROP_PROB_USE_INV_VALUE] = BZLA_OPT_PROP_PROB_USE_INV_VALUE,
    [BITWUZLA_OPT_PROP_SEXT]               = BZLA_OPT_PROP_SEXT,
    [BITWUZLA_OPT_PROP_SKIP_NO_PROGRESS]   = BZLA_OPT_PROP_SKIP_NO_PROGRESS,
    [BITWUZLA_OPT_PROP_USE_BANDIT]         = BZLA_OPT_PROP_USE_BANDIT,
    [BITWUZLA_OPT_PROP_USE_INV_LT_CONCAT]  = BZLA_OPT_PROP_USE_INV_LT_CONCAT,
    [BITWUZLA_OPT_PROP_USE_RESTARTS]       = BZLA_OPT_PROP_USE_RESTARTS,
    [BITWUZLA_OPT_PROP_XOR]                = BZLA_OPT_PROP_XOR,
    [BITWUZLA_OPT_QUANT_SYNTH_SK]          = BZLA_OPT_QUANT_SYNTH_SK,
    [BITWUZLA_OPT_QUANT_SYNTH_QI]          = BZLA_OPT_QUANT_SYNTH_QI,
    [BITWUZLA_OPT_QUANT_SKOLEM_UF]         = BZLA_OPT_QUANT_SKOLEM_UF,
    [BITWUZLA_OPT_RW_EXTRACT_ARITH]        = BZLA_OPT_RW_EXTRACT_ARITH,
    [BITWUZLA_OPT_RW_LEVEL]                = BZLA_OPT_RW_LEVEL,
    [BITWUZLA_OPT_RW_NORMALIZE]            = BZLA_OPT_RW_NORMALIZE,
    [BITWUZLA_OPT_RW_NORMALIZE_ADD]        = BZLA_OPT_RW_NORMALIZE_ADD,
    [BITWUZLA_OPT_RW_SIMPLIFY_CONSTRAINTS] = BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS,
    [BITWUZLA_OPT_RW_SLT]                  = BZLA_OPT_RW_SLT,
    [BITWUZLA_OPT_RW_SORT_AIGVEC]          = BZLA_OPT_RW_SORT_AIGVEC,
    [BITWUZLA_OPT_RW_SORT_AIG]             = BZLA_OPT_RW_SORT_AIG,
    [BITWUZLA_OPT_RW_SORT_EXP]             = BZLA_OPT_RW_SORT_EXP,
    [BITWUZLA_OPT_SAT_ENGINE]              = BZLA_OPT_SAT_ENGINE,
    [BITWUZLA_OPT_SAT_ENGINE_CADICAL_FREEZE] =
        BZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
    [BITWUZLA_OPT_SAT_ENGINE_LGL_FORK]     = BZLA_OPT_SAT_ENGINE_LGL_FORK,
    [BITWUZLA_OPT_SAT_ENGINE_N_THREADS]    = BZLA_OPT_SAT_ENGINE_N_THREADS,
    [BITWUZLA_OPT_SEED]                    = BZLA_OPT_SEED,
    [BITWUZLA_OPT_SLS_JUST]                = BZLA_OPT_SLS_JUST,
    [BITWUZLA_OPT_SLS_MOVE_GW]             = BZLA_OPT_SLS_MOVE_GW,
    [BITWUZLA_OPT_SLS_MOVE_INC_MOVE_TEST]  = BZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
    [BITWUZLA_OPT_SLS_MOVE_PROP]           = BZLA_OPT_SLS_MOVE_PROP,
    [BITWUZLA_OPT_SLS_MOVE_PROP_FORCE_RW]  = BZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
    [BITWUZLA_OPT_SLS_MOVE_PROP_NPROPS]    = BZLA_OPT_SLS_MOVE_PROP_NPROPS,
    [BITWUZLA_OPT_SLS_MOVE_PROP_NSLSS]     = BZLA_OPT_SLS_MOVE_PROP_NSLSS,
    [BITWUZLA_OPT_SLS_MOVE_RAND_ALL]       = BZLA_OPT_SLS_MOVE_RAND_ALL,
    [BITWUZLA_OPT_SLS_MOVE_RAND_RANGE]     = BZLA_OPT_SLS_MOVE_RAND_RANGE,
    [BITWUZLA_OPT_SLS_MOVE_RAND_WALK]      = BZLA_OPT_SLS_MOVE_RAND_WALK,
    [BITWUZLA_OPT_SLS_MOVE_RANGE]          = BZLA_OPT_SLS_MOVE_RANGE,
    [BITWUZLA_OPT_SLS_MOVE_SEGMENT]        = BZLA_OPT_SLS_MOVE_SEGMENT,
    [BITWUZLA_OPT_SLS_NFLIPS]              = BZLA_OPT_SLS_NFLIPS,
    [BITWUZLA_OPT_SLS_PROB_MOVE_RAND_WALK] = BZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
    [BITWUZLA_OPT_SLS_STRATEGY]            = BZLA_OPT_SLS_STRATEGY,
    [BITWUZLA_OPT_SLS_USE_BANDIT]          = BZLA_OPT_SLS_USE_BANDIT,
    [BITWUZLA_OPT_SLS_USE_RESTARTS]        = BZLA_OPT_SLS_USE_RESTARTS,
    [BITWUZLA_OPT_SMT_COMP_MODE]           = BZLA_OPT_SMT_COMP_MODE,
    [BITWUZLA_OPT_VERBOSITY]               = BZLA_OPT_VERBOSITY,
};

static BitwuzlaOption bitwuzla_options[BZLA_OPT_NUM_OPTS] = {
    [BZLA_OPT_AIGPROP_NPROPS]          = BITWUZLA_OPT_AIGPROP_NPROPS,
    [BZLA_OPT_AIGPROP_USE_BANDIT]      = BITWUZLA_OPT_AIGPROP_USE_BANDIT,
    [BZLA_OPT_AIGPROP_USE_RESTARTS]    = BITWUZLA_OPT_AIGPROP_USE_RESTARTS,
    [BZLA_OPT_CHECK_MODEL]             = BITWUZLA_OPT_CHECK_MODEL,
    [BZLA_OPT_CHECK_UNCONSTRAINED]     = BITWUZLA_OPT_CHECK_UNCONSTRAINED,
    [BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS] = BITWUZLA_OPT_CHECK_UNSAT_ASSUMPTIONS,
    [BZLA_OPT_DECLSORT_BV_WIDTH]       = BITWUZLA_OPT_DECLSORT_BV_WIDTH,
    [BZLA_OPT_ENGINE]                  = BITWUZLA_OPT_ENGINE,
    [BZLA_OPT_EXIT_CODES]              = BITWUZLA_OPT_EXIT_CODES,
    [BZLA_OPT_FUN_DUAL_PROP]           = BITWUZLA_OPT_FUN_DUAL_PROP,
    [BZLA_OPT_FUN_DUAL_PROP_QSORT]     = BITWUZLA_OPT_FUN_DUAL_PROP_QSORT,
    [BZLA_OPT_FUN_EAGER_LEMMAS]        = BITWUZLA_OPT_FUN_EAGER_LEMMAS,
    [BZLA_OPT_FUN_JUST]                = BITWUZLA_OPT_FUN_JUST,
    [BZLA_OPT_FUN_JUST_HEURISTIC]      = BITWUZLA_OPT_FUN_JUST_HEURISTIC,
    [BZLA_OPT_FUN_LAZY_SYNTHESIZE]     = BITWUZLA_OPT_FUN_LAZY_SYNTHESIZE,
    [BZLA_OPT_FUN_PREPROP]             = BITWUZLA_OPT_FUN_PREPROP,
    [BZLA_OPT_FUN_PRESLS]              = BITWUZLA_OPT_FUN_PRESLS,
    [BZLA_OPT_FUN_STORE_LAMBDAS]       = BITWUZLA_OPT_FUN_STORE_LAMBDAS,
    [BZLA_OPT_INCREMENTAL]             = BITWUZLA_OPT_INCREMENTAL,
    [BZLA_OPT_INPUT_FORMAT]            = BITWUZLA_OPT_INPUT_FORMAT,
    [BZLA_OPT_LOGLEVEL]                = BITWUZLA_OPT_LOGLEVEL,
    [BZLA_OPT_LS_SHARE_SAT]            = BITWUZLA_OPT_LS_SHARE_SAT,
    [BZLA_OPT_OUTPUT_FORMAT]           = BITWUZLA_OPT_OUTPUT_FORMAT,
    [BZLA_OPT_OUTPUT_NUMBER_FORMAT]    = BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT,
    [BZLA_OPT_PARSE_INTERACTIVE]       = BITWUZLA_OPT_PARSE_INTERACTIVE,
    [BZLA_OPT_PP_ACKERMANN]            = BITWUZLA_OPT_PP_ACKERMANN,
    [BZLA_OPT_PP_BETA_REDUCE]          = BITWUZLA_OPT_PP_BETA_REDUCE,
    [BZLA_OPT_PP_ELIMINATE_EXTRACTS]   = BITWUZLA_OPT_PP_ELIMINATE_EXTRACTS,
    [BZLA_OPT_PP_ELIMINATE_ITES]       = BITWUZLA_OPT_PP_ELIMINATE_ITES,
    [BZLA_OPT_PP_EXTRACT_LAMBDAS]      = BITWUZLA_OPT_PP_EXTRACT_LAMBDAS,
    [BZLA_OPT_PP_MERGE_LAMBDAS]        = BITWUZLA_OPT_PP_MERGE_LAMBDAS,
    [BZLA_OPT_PP_NONDESTR_SUBST]       = BITWUZLA_OPT_PP_NONDESTR_SUBST,
    [BZLA_OPT_PP_NORMALIZE_ADD]        = BITWUZLA_OPT_PP_NORMALIZE_ADD,
    [BZLA_OPT_PP_SKELETON_PREPROC]     = BITWUZLA_OPT_PP_SKELETON_PREPROC,
    [BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION] =
        BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION,
    [BZLA_OPT_PP_VAR_SUBST]        = BITWUZLA_OPT_PP_VAR_SUBST,
    [BZLA_OPT_PRETTY_PRINT]        = BITWUZLA_OPT_PRETTY_PRINT,
    [BZLA_OPT_PRINT_DIMACS]        = BITWUZLA_OPT_PRINT_DIMACS,
    [BZLA_OPT_PRODUCE_MODELS]      = BITWUZLA_OPT_PRODUCE_MODELS,
    [BZLA_OPT_PRODUCE_UNSAT_CORES] = BITWUZLA_OPT_PRODUCE_UNSAT_CORES,
    [BZLA_OPT_PROP_CONST_BITS]     = BITWUZLA_OPT_PROP_CONST_BITS,
    [BZLA_OPT_PROP_CONST_DOMAINS]  = BITWUZLA_OPT_PROP_CONST_DOMAINS,
    [BZLA_OPT_PROP_ENTAILED]       = BITWUZLA_OPT_PROP_ENTAILED,
    [BZLA_OPT_PROP_FLIP_COND_CONST_DELTA] =
        BITWUZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
    [BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL] =
        BITWUZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
    [BZLA_OPT_PROP_INFER_INEQ_BOUNDS]   = BITWUZLA_OPT_PROP_INFER_INEQ_BOUNDS,
    [BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT] = BITWUZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
    [BZLA_OPT_PROP_NPROPS]              = BITWUZLA_OPT_PROP_NPROPS,
    [BZLA_OPT_PROP_NUPDATES]            = BITWUZLA_OPT_PROP_NUPDATES,
    [BZLA_OPT_PROP_PATH_SEL]            = BITWUZLA_OPT_PROP_PATH_SEL,
    [BZLA_OPT_PROP_PROB_AND_FLIP]       = BITWUZLA_OPT_PROP_PROB_AND_FLIP,
    [BZLA_OPT_PROP_PROB_EQ_FLIP]        = BITWUZLA_OPT_PROP_PROB_EQ_FLIP,
    [BZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE] =
        BITWUZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
    [BZLA_OPT_PROP_PROB_FLIP_COND] = BITWUZLA_OPT_PROP_PROB_FLIP_COND,
    [BZLA_OPT_PROP_PROB_FLIP_COND_CONST] =
        BITWUZLA_OPT_PROP_PROB_FLIP_COND_CONST,
    [BZLA_OPT_PROP_PROB_RANDOM_INPUT]  = BITWUZLA_OPT_PROP_PROB_RANDOM_INPUT,
    [BZLA_OPT_PROP_PROB_SLICE_FLIP]    = BITWUZLA_OPT_PROP_PROB_SLICE_FLIP,
    [BZLA_OPT_PROP_PROB_SLICE_KEEP_DC] = BITWUZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
    [BZLA_OPT_PROP_PROB_USE_INV_VALUE] = BITWUZLA_OPT_PROP_PROB_USE_INV_VALUE,
    [BZLA_OPT_PROP_SEXT]               = BITWUZLA_OPT_PROP_SEXT,
    [BZLA_OPT_PROP_SKIP_NO_PROGRESS]   = BITWUZLA_OPT_PROP_SKIP_NO_PROGRESS,
    [BZLA_OPT_PROP_ASHR]               = BITWUZLA_OPT_PROP_ASHR,
    [BZLA_OPT_PROP_USE_BANDIT]         = BITWUZLA_OPT_PROP_USE_BANDIT,
    [BZLA_OPT_PROP_USE_INV_LT_CONCAT]  = BITWUZLA_OPT_PROP_USE_INV_LT_CONCAT,
    [BZLA_OPT_PROP_USE_RESTARTS]       = BITWUZLA_OPT_PROP_USE_RESTARTS,
    [BZLA_OPT_PROP_XOR]                = BITWUZLA_OPT_PROP_XOR,
    [BZLA_OPT_QUANT_SYNTH_SK]          = BITWUZLA_OPT_QUANT_SYNTH_SK,
    [BZLA_OPT_QUANT_SYNTH_QI]          = BITWUZLA_OPT_QUANT_SYNTH_QI,
    [BZLA_OPT_QUANT_SKOLEM_UF]         = BITWUZLA_OPT_QUANT_SKOLEM_UF,
    [BZLA_OPT_RW_EXTRACT_ARITH]        = BITWUZLA_OPT_RW_EXTRACT_ARITH,
    [BZLA_OPT_RW_LEVEL]                = BITWUZLA_OPT_RW_LEVEL,
    [BZLA_OPT_RW_NORMALIZE]            = BITWUZLA_OPT_RW_NORMALIZE,
    [BZLA_OPT_RW_NORMALIZE_ADD]        = BITWUZLA_OPT_RW_NORMALIZE_ADD,
    [BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS] = BITWUZLA_OPT_RW_SIMPLIFY_CONSTRAINTS,
    [BZLA_OPT_RW_SLT]                  = BITWUZLA_OPT_RW_SLT,
    [BZLA_OPT_RW_SORT_AIGVEC]          = BITWUZLA_OPT_RW_SORT_AIGVEC,
    [BZLA_OPT_RW_SORT_AIG]             = BITWUZLA_OPT_RW_SORT_AIG,
    [BZLA_OPT_RW_SORT_EXP]             = BITWUZLA_OPT_RW_SORT_EXP,
    [BZLA_OPT_SAT_ENGINE]              = BITWUZLA_OPT_SAT_ENGINE,
    [BZLA_OPT_SAT_ENGINE_CADICAL_FREEZE] =
        BITWUZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
    [BZLA_OPT_SAT_ENGINE_LGL_FORK]     = BITWUZLA_OPT_SAT_ENGINE_LGL_FORK,
    [BZLA_OPT_SAT_ENGINE_N_THREADS]    = BITWUZLA_OPT_SAT_ENGINE_N_THREADS,
    [BZLA_OPT_SEED]                    = BITWUZLA_OPT_SEED,
    [BZLA_OPT_SLS_JUST]                = BITWUZLA_OPT_SLS_JUST,
    [BZLA_OPT_SLS_MOVE_GW]             = BITWUZLA_OPT_SLS_MOVE_GW,
    [BZLA_OPT_SLS_MOVE_INC_MOVE_TEST]  = BITWUZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
    [BZLA_OPT_SLS_MOVE_PROP]           = BITWUZLA_OPT_SLS_MOVE_PROP,
    [BZLA_OPT_SLS_MOVE_PROP_FORCE_RW]  = BITWUZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
    [BZLA_OPT_SLS_MOVE_PROP_NPROPS]    = BITWUZLA_OPT_SLS_MOVE_PROP_NPROPS,
    [BZLA_OPT_SLS_MOVE_PROP_NSLSS]     = BITWUZLA_OPT_SLS_MOVE_PROP_NSLSS,
    [BZLA_OPT_SLS_MOVE_RAND_ALL]       = BITWUZLA_OPT_SLS_MOVE_RAND_ALL,
    [BZLA_OPT_SLS_MOVE_RAND_RANGE]     = BITWUZLA_OPT_SLS_MOVE_RAND_RANGE,
    [BZLA_OPT_SLS_MOVE_RAND_WALK]      = BITWUZLA_OPT_SLS_MOVE_RAND_WALK,
    [BZLA_OPT_SLS_MOVE_RANGE]          = BITWUZLA_OPT_SLS_MOVE_RANGE,
    [BZLA_OPT_SLS_MOVE_SEGMENT]        = BITWUZLA_OPT_SLS_MOVE_SEGMENT,
    [BZLA_OPT_SLS_NFLIPS]              = BITWUZLA_OPT_SLS_NFLIPS,
    [BZLA_OPT_SLS_PROB_MOVE_RAND_WALK] = BITWUZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
    [BZLA_OPT_SLS_STRATEGY]            = BITWUZLA_OPT_SLS_STRATEGY,
    [BZLA_OPT_SLS_USE_BANDIT]          = BITWUZLA_OPT_SLS_USE_BANDIT,
    [BZLA_OPT_SLS_USE_RESTARTS]        = BITWUZLA_OPT_SLS_USE_RESTARTS,
    [BZLA_OPT_SMT_COMP_MODE]           = BITWUZLA_OPT_SMT_COMP_MODE,
    [BZLA_OPT_VERBOSITY]               = BITWUZLA_OPT_VERBOSITY,
};

static const char *bzla_kind_to_str[BITWUZLA_NUM_KINDS] = {
    "BITWUZLA_KIND_CONST",
    "BITWUZLA_KIND_CONST_ARRAY",
    "BITWUZLA_KIND_VAL",
    "BITWUZLA_KIND_VAR",
    "BITWUZLA_KIND_AND",
    "BITWUZLA_KIND_APPLY",
    "BITWUZLA_KIND_ARRAY_SELECT",
    "BITWUZLA_KIND_ARRAY_STORE",
    "BITWUZLA_KIND_BV_ADD",
    "BITWUZLA_KIND_BV_AND",
    "BITWUZLA_KIND_BV_ASHR",
    "BITWUZLA_KIND_BV_COMP",
    "BITWUZLA_KIND_BV_CONCAT",
    "BITWUZLA_KIND_BV_DEC",
    "BITWUZLA_KIND_BV_INC",
    "BITWUZLA_KIND_BV_MUL",
    "BITWUZLA_KIND_BV_NAND",
    "BITWUZLA_KIND_BV_NEG",
    "BITWUZLA_KIND_BV_NOR",
    "BITWUZLA_KIND_BV_NOT",
    "BITWUZLA_KIND_BV_OR",
    "BITWUZLA_KIND_BV_REDAND",
    "BITWUZLA_KIND_BV_REDOR",
    "BITWUZLA_KIND_BV_REDXOR",
    "BITWUZLA_KIND_BV_ROL",
    "BITWUZLA_KIND_BV_ROR",
    "BITWUZLA_KIND_BV_SADD_OVERFLOW",
    "BITWUZLA_KIND_BV_SDIV_OVERFLOW",
    "BITWUZLA_KIND_BV_SDIV",
    "BITWUZLA_KIND_BV_SGE",
    "BITWUZLA_KIND_BV_SGT",
    "BITWUZLA_KIND_BV_SHL",
    "BITWUZLA_KIND_BV_SHR",
    "BITWUZLA_KIND_BV_SLE",
    "BITWUZLA_KIND_BV_SLT",
    "BITWUZLA_KIND_BV_SMOD",
    "BITWUZLA_KIND_BV_SMUL_OVERFLOW",
    "BITWUZLA_KIND_BV_SREM",
    "BITWUZLA_KIND_BV_SSUB_OVERFLOW",
    "BITWUZLA_KIND_BV_SUB",
    "BITWUZLA_KIND_BV_UADD_OVERFLOW",
    "BITWUZLA_KIND_BV_UDIV",
    "BITWUZLA_KIND_BV_UGE",
    "BITWUZLA_KIND_BV_UGT",
    "BITWUZLA_KIND_BV_ULE",
    "BITWUZLA_KIND_BV_ULT",
    "BITWUZLA_KIND_BV_UMUL_OVERFLOW",
    "BITWUZLA_KIND_BV_UREM",
    "BITWUZLA_KIND_BV_USUB_OVERFLOW",
    "BITWUZLA_KIND_BV_XNOR",
    "BITWUZLA_KIND_BV_XOR",
    "BITWUZLA_KIND_DISTINCT",
    "BITWUZLA_KIND_EQUAL",
    "BITWUZLA_KIND_EXISTS",
    "BITWUZLA_KIND_FORALL",
    "BITWUZLA_KIND_FP_ABS",
    "BITWUZLA_KIND_FP_ADD",
    "BITWUZLA_KIND_FP_DIV",
    "BITWUZLA_KIND_FP_EQ",
    "BITWUZLA_KIND_FP_FMA",
    "BITWUZLA_KIND_FP_FP",
    "BITWUZLA_KIND_FP_GEQ",
    "BITWUZLA_KIND_FP_GT",
    "BITWUZLA_KIND_FP_IS_INF",
    "BITWUZLA_KIND_FP_IS_NAN",
    "BITWUZLA_KIND_FP_IS_NEG",
    "BITWUZLA_KIND_FP_IS_NORMAL",
    "BITWUZLA_KIND_FP_IS_POS",
    "BITWUZLA_KIND_FP_IS_SUBNORMAL",
    "BITWUZLA_KIND_FP_IS_ZERO",
    "BITWUZLA_KIND_FP_LEQ",
    "BITWUZLA_KIND_FP_LT",
    "BITWUZLA_KIND_FP_MAX",
    "BITWUZLA_KIND_FP_MIN",
    "BITWUZLA_KIND_FP_MUL",
    "BITWUZLA_KIND_FP_NEG",
    "BITWUZLA_KIND_FP_REM",
    "BITWUZLA_KIND_FP_RTI",
    "BITWUZLA_KIND_FP_SQRT",
    "BITWUZLA_KIND_FP_SUB",
    "BITWUZLA_KIND_IFF",
    "BITWUZLA_KIND_IMPLIES",
    "BITWUZLA_KIND_ITE",
    "BITWUZLA_KIND_LAMBDA",
    "BITWUZLA_KIND_NOT",
    "BITWUZLA_KIND_OR",
    "BITWUZLA_KIND_XOR",
    "BITWUZLA_KIND_BV_EXTRACT",
    "BITWUZLA_KIND_BV_REPEAT",
    "BITWUZLA_KIND_BV_ROLI",
    "BITWUZLA_KIND_BV_RORI",
    "BITWUZLA_KIND_BV_SIGN_EXTEND",
    "BITWUZLA_KIND_BV_ZERO_EXTEND",
    "BITWUZLA_KIND_FP_TO_FP_FROM_BV",
    "BITWUZLA_KIND_FP_TO_FP_FROM_FP",
    "BITWUZLA_KIND_FP_TO_FP_FROM_SBV",
    "BITWUZLA_KIND_FP_TO_FP_FROM_UBV",
    "BITWUZLA_KIND_FP_TO_SBV",
    "BITWUZLA_KIND_FP_TO_UBV",
};

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA(bitwuzla) (bitwuzla->d_bzla)
#define BZLA_EXPORT_BITWUZLA(bzla) ((Bitwuzla *) (bzla)->bitwuzla)

#define BZLA_IMPORT_BITWUZLA_TERM(term) (((BzlaNode *) (term)))
#define BZLA_IMPORT_BITWUZLA_TERMS(terms) (((BzlaNode **) (terms)))
#define BZLA_EXPORT_BITWUZLA_TERM(node) (((const BitwuzlaTerm *) (node)))
#define BZLA_EXPORT_BITWUZLA_TERMS(terms) (((const BitwuzlaTerm **) (terms)))

#define BZLA_IMPORT_BITWUZLA_SORT(sort) ((sort)->d_bzla_sort)
#define BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, sort) wrap_sort(bitwuzla, sort)

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options[option])
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (bitwuzla_options[option])

#define BZLA_IMPORT_BITWUZLA_RM(rm)                                \
  (rm == BITWUZLA_RM_RNA                                           \
       ? BZLA_RM_RNA                                               \
       : (rm == BITWUZLA_RM_RNE                                    \
              ? BZLA_RM_RNE                                        \
              : (rm == BITWUZLA_RM_RTN                             \
                     ? BZLA_RM_RTN                                 \
                     : (rm == BITWUZLA_RM_RTP                      \
                            ? BZLA_RM_RTP                          \
                            : (rm == BITWUZLA_RM_RTZ ? BZLA_RM_RTZ \
                                                     : BZLA_RM_MAX)))))

#define BZLA_EXPORT_BITWUZLA_RM(rm)                                \
  (rm == BZLA_RM_RNA                                               \
       ? BITWUZLA_RM_RNA                                           \
       : (rm == BZLA_RM_RNE                                        \
              ? BITWUZLA_RM_RNE                                    \
              : (rm == BZLA_RM_RTN                                 \
                     ? BITWUZLA_RM_RTN                             \
                     : (rm == BZLA_RM_RTP                          \
                            ? BITWUZLA_RM_RTP                      \
                            : (rm == BZLA_RM_RTZ ? BITWUZLA_RM_RTZ \
                                                 : BITWUZLA_RM_MAX)))))

/* -------------------------------------------------------------------------- */

#define BZLA_CHECK_OPT_INCREMENTAL(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL), \
             "incremental usage not enabled");

#define BZLA_CHECK_OPT_PRODUCE_MODELS(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS), \
             "model production not enabled");

#define BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_UNSAT_CORES), \
             "unsat core production not enabled");

#define BZLA_CHECK_UNSAT(bzla, what)                     \
  BZLA_ABORT(bzla->last_sat_result != BZLA_RESULT_UNSAT, \
             "cannot %s if input formula is not unsat",  \
             what);

#define BZLA_CHECK_SAT(bzla, what)                                          \
  BZLA_ABORT(                                                               \
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments, \
      "cannot %s if input formula is not sat",                              \
      what);

/* -------------------------------------------------------------------------- */

#define BZLA_CHECK_ARG_NOT_NULL(arg) \
  BZLA_ABORT((arg) == NULL, "argument '%s' must not be NULL", #arg)

#define BZLA_CHECK_ARG_NOT_NULL_AT_IDX(arg, idx)           \
  BZLA_ABORT((arg) == NULL,                                \
             "argument '%s' must not be NULL at index %u", \
             #arg,                                         \
             (idx))

#define BZLA_CHECK_ARG_NOT_ZERO(arg) \
  BZLA_ABORT(arg == 0, "argument '%s' must be > 0", #arg)

#define BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(arg) \
  BZLA_ABORT(arg == NULL || *arg == '\0', "expected non-empty string")

#define BZLA_CHECK_ARG_CNT(kind, nary, expected, argc)                         \
  BZLA_ABORT(                                                                  \
      (nary && (argc) < expected) || (!nary && (argc) != (expected)),          \
      "invalid number of arguments for kind '%s', expected '%u' and got '%u'", \
      bzla_kind_to_str[kind],                                                  \
      expected,                                                                \
      argc)

#define BZLA_CHECK_IDX_CNT(kind, expected, argc)                             \
  BZLA_ABORT(                                                                \
      (argc) != (expected),                                                  \
      "invalid number of indices for kind '%s', expected '%u' and got '%u'", \
      bzla_kind_to_str[kind],                                                \
      expected,                                                              \
      argc)

#define BZLA_CHECK_ARGS_SORT(bzla, arg, nextarg, idx, sort_check)    \
  do                                                                 \
  {                                                                  \
    BzlaSortId sorti = bzla_node_get_sort_id(arg);                   \
    BZLA_ABORT(!sort_check(bzla, sorti),                             \
               "node with unexpected sort at index %u",              \
               idx);                                                 \
    if (nextarg)                                                     \
    {                                                                \
      BZLA_ABORT(sorti != bzla_node_get_sort_id(nextarg),            \
                 "terms with mismatching sort at indices %u and %u", \
                 idx,                                                \
                 (idx) + 1);                                         \
    }                                                                \
  } while (0)

#define BZLA_CHECK_MK_TERM_ARGS(                                   \
    kind, nary, args, expected, argc, start, sort_check, match)    \
  do                                                               \
  {                                                                \
    BZLA_CHECK_ARG_CNT(kind, nary, expected, argc);                \
    for (int64_t i = 0, j = 1; i < argc; i++, j++)                 \
    {                                                              \
      BZLA_CHECK_ARG_NOT_NULL_AT_IDX(args[i], i);                  \
      assert(bzla_node_get_ext_refs(args[i]));                     \
      BZLA_CHECK_TERM_BZLA(bzla, args[i]);                         \
      if (i < (start)) continue;                                   \
      BZLA_CHECK_ARGS_SORT(bzla,                                   \
                           args[i],                                \
                           j < (argc) && (match) ? args[j] : NULL, \
                           i,                                      \
                           sort_check);                            \
    }                                                              \
  } while (0)

#define BZLA_CHECK_MK_TERM_ARGS_IDXED(                                         \
    kind, args, expected, argc, idxc_expected, idxc, start, sort_check, match) \
  do                                                                           \
  {                                                                            \
    BZLA_CHECK_MK_TERM_ARGS(                                                   \
        kind, false, args, expected, argc, start, sort_check, match);          \
    BZLA_CHECK_IDX_CNT(kind, idxc_expected, idxc);                             \
  } while (0)

#define BZLA_CHECK_OPTION(bzla, opt) \
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option")

#define BZLA_CHECK_OPTION_VALUE(bzla, opt, value)                              \
  BZLA_ABORT(                                                                  \
      value<bzla_opt_get_min(bzla, opt) || value> bzla_opt_get_max(bzla, opt), \
      "invalid value '%u' for option '%s'",                                    \
      value,                                                                   \
      bzla_opt_get_lng(bzla, opt))

#define BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort)                           \
  do                                                                       \
  {                                                                        \
    BZLA_ABORT(!sort || (sort)->d_bzla != (bitwuzla),                      \
               "sort '%s' is not associated with given solver instance",   \
               #sort);                                                     \
    assert(bzla_sort_is_valid((sort)->d_bzla->d_bzla, sort->d_bzla_sort)); \
  } while (0)

#define BZLA_CHECK_SORT_BITWUZLA_AT_IDX(bitwuzla, sort, idx)                \
  do                                                                        \
  {                                                                         \
    BZLA_ABORT(                                                             \
        !sort || (sort)->d_bzla != (bitwuzla),                              \
        "sort %s is not associated with given solver instance at index %u", \
        #sort,                                                              \
        (idx));                                                             \
    assert(bzla_sort_is_valid((sort)->d_bzla->d_bzla, sort->d_bzla_sort));  \
  } while (0)

#define BZLA_CHECK_SORT_IS_ARRAY(bzla, sort)                        \
  BZLA_ABORT(!bzla_sort_is_fun(bzla, sort)                          \
                 || bzla_sort_tuple_get_arity(                      \
                        bzla, bzla_sort_fun_get_domain(bzla, sort)) \
                        != 1,                                       \
             "expected array sort");

#define BZLA_CHECK_SORT_IS_BV(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_bv(bzla, sort), "expected bit-vector sort")

#define BZLA_CHECK_SORT_IS_FP(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_fp(bzla, sort), "expected floating-point sort")

#define BZLA_CHECK_SORT_IS_FP_AT_IDX(bzla, sort, idx)    \
  BZLA_ABORT(!bzla_sort_is_fp(bzla, sort),               \
             "expected floating-point sort at index %u", \
             (idx))

#define BZLA_CHECK_SORT_IS_FUN(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_fun(bzla, sort), "expected function sort")

#define BZLA_CHECK_SORT_NOT_IS_FUN(bzla, sort)                            \
  do                                                                      \
  {                                                                       \
    BZLA_ABORT(bzla_sort_is_array(bzla, sort), "unexpected array sort");  \
    BZLA_ABORT(bzla_sort_is_fun(bzla, sort), "unexpected function sort"); \
  } while (0)

#define BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, sort, idx) \
  do                                                       \
  {                                                        \
    BZLA_ABORT(bzla_sort_is_array(bzla, sort),             \
               "unexpected function sort at index %u",     \
               (idx));                                     \
    BZLA_ABORT(bzla_sort_is_fun(bzla, sort),               \
               "unexpected function sort at index %u",     \
               (idx));                                     \
  } while (0)

#define BZLA_CHECK_TERM_BZLA(bzla, term)                               \
  BZLA_ABORT(bzla_node_get_bzla(term) != bzla,                         \
             "term '%s' is not associated with given solver instance", \
             #term);

#define BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, term, idx)   \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term),              \
             "expected rounding-mode term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_BOOL(bzla, term)                         \
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_get_sort_id(term)), \
             "expected boolean term")

#define BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, term, idx)             \
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_get_sort_id(term)), \
             "expected boolean term at index %u",                   \
             (idx))

#define BZLA_CHECK_TERM_IS_BV(bzla, term) \
  BZLA_ABORT(!bzla_node_is_bv(bzla, term), "expected bit-vector term")

#define BZLA_CHECK_TERM_IS_BV_AT_IDX(bzla, term, idx) \
  BZLA_ABORT(!bzla_node_is_bv(bzla, term),            \
             "expected bit-vector term at index %u",  \
             (idx))

#define BZLA_CHECK_TERM_IS_BV_LAMBDA_AT_IDX(bzla, term, idx)                \
  BZLA_ABORT(                                                               \
      !bzla_node_is_bv(bzla, term)                                          \
          && (!bzla_node_is_fun(term)                                       \
              || !bzla_sort_is_bv(bzla,                                     \
                                  bzla_sort_fun_get_codomain(               \
                                      bzla, bzla_node_get_sort_id(term)))), \
      "expected bit-vector term or bit-vector function term at index %u",   \
      (idx))

#define BZLA_CHECK_TERM_IS_FP(bzla, term) \
  BZLA_ABORT(!bzla_node_is_fp(bzla, term), "expected floating-point term")

#define BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, term, idx)    \
  BZLA_ABORT(!bzla_node_is_fp(bzla, term),               \
             "expected floating-point term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_RM(bzla, term) \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term), "expected rounding-mode term")

#define BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, term, idx)   \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term),              \
             "expected rounding-mode term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_ARRAY(term)                                        \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected array term")

#define BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(term, idx)                            \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected array term at index %u",                                      \
      (idx))

#define BZLA_CHECK_TERM_IS_BV_VAL(term)                              \
  BZLA_ABORT(!bzla_node_is_bv_const(                                 \
                 bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected bit-vector value")

#define BZLA_CHECK_TERM_IS_VAR(term)                                     \
  BZLA_ABORT(bzla_node_is_inverted(term)                                 \
                 || !bzla_node_is_param(                                 \
                     bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected variable term")

#define BZLA_CHECK_TERM_IS_VAR_AT_IDX(term, idx)                         \
  BZLA_ABORT(bzla_node_is_inverted(term)                                 \
                 || !bzla_node_is_param(                                 \
                     bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected variable term at index %u",                       \
             (idx))

#define BZLA_CHECK_TERM_IS_FUN(term)                                        \
  BZLA_ABORT(                                                               \
      !bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "unexpected function term at index")

#define BZLA_CHECK_TERM_IS_FUN_AT_IDX(term, idx)                            \
  BZLA_ABORT(                                                               \
      !bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected function term at index %u",                                 \
      (idx))

#define BZLA_CHECK_TERM_NOT_IS_FUN(term)                                       \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
        "unexpected array term");                                              \
    BZLA_ABORT(                                                                \
        bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)),   \
        "unexpected function term");                                           \
  } while (0)

#define BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(term, idx)                           \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
        "unexpected array term at index %u",                                   \
        (idx));                                                                \
    BZLA_ABORT(                                                                \
        bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)),   \
        "unexpected function term at index %u",                                \
        (idx));                                                                \
  } while (0)

#define BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(term)                           \
  BZLA_ABORT(                                                                \
      bzla_node_real_addr(bzla_simplify_exp(bzla_node_get_bzla(term), term)) \
          ->parameterized,                                                   \
      "term must not be parameterized");

#define BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(term, idx)                           \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_lambda(bzla_simplify_exp(bzla_node_get_bzla(term), term)) \
          && bzla_node_is_fun(                                                \
              bzla_simplify_exp(bzla_node_get_bzla(term), term)),             \
      "unexpected function term at index %u",                                 \
      (idx))

#define BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(term, idx) \
  BZLA_ABORT(bzla_node_param_is_bound(term),               \
             "expected unbound variable term at index %u", \
             (idx))

/* -------------------------------------------------------------------------- */

/** Increment external reference counter. */
static void
inc_ext_refs_sort(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  assert(id);
  BzlaSort *sort = bzla_sort_get_by_id(bzla, id);
  BZLA_ABORT(sort->ext_refs == INT32_MAX, "sort reference counter overflow");
  sort->ext_refs += 1;
  bzla->external_refs += 1;
}

/** Dummy helper for sort argument check for mk_term. */
static bool
sort_any(Bzla *bzla, BzlaSortId node)
{
  (void) bzla;
  (void) node;
  return true;
}

/** Return true given variable terms are distinct. */
static bool
vars_distinct(Bzla *bzla, BzlaNode *vars[], uint32_t paramc)
{
  bool res                = true;
  BzlaIntHashTable *cache = bzla_hashint_table_new(bzla->mm);
  for (uint32_t i = 0; i < paramc; i++)
  {
    if (bzla_hashint_table_contains(cache, bzla_node_get_id(vars[i])))
    {
      res = false;
      break;
    }
    bzla_hashint_table_add(cache, bzla_node_get_id(vars[i]));
  }
  bzla_hashint_table_delete(cache);
  return res;
}

static BzlaNode *
mk_term_left_assoc(Bzla *bzla,
                   BzlaNode *args[],
                   uint32_t argc,
                   BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp;

  res = fun(bzla, args[0], args[1]);
  for (uint32_t i = 2; i < argc; i++)
  {
    tmp = fun(bzla, res, args[i]);
    bzla_node_release(bzla, res);
    res = tmp;
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_right_assoc(Bzla *bzla,
                    BzlaNode *args[],
                    uint32_t argc,
                    BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp;
  res = bzla_node_copy(bzla, args[argc - 1]);
  for (uint32_t i = 1; i < argc; ++i)
  {
    tmp = fun(bzla, args[argc - i - 1], res);
    bzla_node_release(bzla, res);
    res = tmp;
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_pairwise(Bzla *bzla,
                 BzlaNode *args[],
                 uint32_t argc,
                 BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0; i < argc - 1; i++)
  {
    for (uint32_t j = i + 1; j < argc; j++)
    {
      tmp = fun(bzla, args[i], args[j]);
      if (res)
      {
        old = res;
        res = bzla_exp_bv_and(bzla, old, tmp);
        bzla_node_release(bzla, old);
        bzla_node_release(bzla, tmp);
      }
      else
      {
        res = tmp;
      }
    }
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_chained(Bzla *bzla,
                BzlaNode *args[],
                uint32_t argc,
                BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0, j = 1; j < argc; i++, j++)
  {
    tmp = fun(bzla, args[i], args[j]);
    if (res)
    {
      old = res;
      res = bzla_exp_bv_and(bzla, old, tmp);
      bzla_node_release(bzla, old);
      bzla_node_release(bzla, tmp);
    }
    else
    {
      res = tmp;
    }
  }
  assert(res);
  return res;
}

static const BitwuzlaSort *
wrap_sort(Bitwuzla *bitwuzla, BzlaSortId bzla_sort)
{
  assert(bitwuzla);
  assert(bzla_sort);

  BitwuzlaSort *res;
  if (bzla_hashint_map_contains(bitwuzla->d_sort_map, bzla_sort))
  {
    res = bzla_hashint_map_get(bitwuzla->d_sort_map, bzla_sort)->as_ptr;
  }
  else
  {
    BZLA_NEW(bitwuzla->d_mm, res);
    res->d_bzla_sort = bzla_sort;
    res->d_bzla      = bitwuzla;
    bzla_hashint_map_add(bitwuzla->d_sort_map,
                         bzla_sort_copy(bitwuzla->d_bzla, bzla_sort))
        ->as_ptr = res;
  }
  return res;
}

static void
reset_assumptions(Bitwuzla *bitwuzla)
{
  assert(bitwuzla);
  assert(bitwuzla->d_bzla);
  if (bitwuzla->d_bzla->valid_assignments)
  {
    BZLA_RESET_STACK(bitwuzla->d_assumptions);
  }
}

/* -------------------------------------------------------------------------- */

#define BZLA_RETURN_BITWUZLA_SORT(bitwuzla, sort)    \
  do                                                 \
  {                                                  \
    assert(res);                                     \
    inc_ext_refs_sort(bzla, res);                    \
    return BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, res); \
  } while (0)

#define BZLA_RETURN_BITWUZLA_TERM(term)       \
  do                                          \
  {                                           \
    assert(res);                              \
    bzla_node_inc_ext_ref_counter(bzla, res); \
    return BZLA_EXPORT_BITWUZLA_TERM(res);    \
  } while (0)

/* -------------------------------------------------------------------------- */
/* BitwuzlaKind                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_kind_to_string(BitwuzlaKind kind)
{
  BZLA_ABORT(kind >= BITWUZLA_NUM_KINDS, "invalid term kind");
  return bzla_kind_to_str[kind];
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_rm_to_string(BitwuzlaRoundingMode rm)
{
  switch (rm)
  {
    case BITWUZLA_RM_RNA: return "RNA"; break;
    case BITWUZLA_RM_RNE: return "RNE"; break;
    case BITWUZLA_RM_RTN: return "RTN"; break;
    case BITWUZLA_RM_RTP: return "RTP"; break;
    default:
      BZLA_ABORT(rm != BITWUZLA_RM_RTZ, "invalid rounding mode");
      return "RTZ";
  }
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_result_to_string(BitwuzlaResult result)
{
  switch (result)
  {
    case BITWUZLA_SAT: return "sat"; break;
    case BITWUZLA_UNSAT: return "unsat"; break;
    default:
      BZLA_ABORT(result != BITWUZLA_UNKNOWN, "invalid result kind");
      return "unknown";
  }
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

static void
init(Bitwuzla *bitwuzla, BzlaMemMgr *mm)
{
  bitwuzla->d_mm             = mm;
  bitwuzla->d_bzla           = bzla_new();
  bitwuzla->d_bzla->bitwuzla = bitwuzla;
  bitwuzla->d_sort_map       = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, bitwuzla->d_assumptions);
  BZLA_INIT_STACK(mm, bitwuzla->d_unsat_assumptions);
  BZLA_INIT_STACK(mm, bitwuzla->d_unsat_core);
  BZLA_INIT_STACK(mm, bitwuzla->d_term_children);
  BZLA_INIT_STACK(mm, bitwuzla->d_fun_domain_sorts);
  BZLA_INIT_STACK(mm, bitwuzla->d_sort_fun_domain_sorts);
  BZLA_INIT_STACK(mm, bitwuzla->d_array_indices);
  BZLA_INIT_STACK(mm, bitwuzla->d_array_values);
  BZLA_INIT_STACK(mm, bitwuzla->d_fun_args);
  BZLA_INIT_STACK(mm, bitwuzla->d_fun_args_ptr);
  BZLA_INIT_STACK(mm, bitwuzla->d_fun_values);
  BZLA_INIT_STACK(mm, bitwuzla->d_option_info_values);
  bzla_opt_set(bitwuzla->d_bzla, BZLA_OPT_AUTO_CLEANUP, 1);
}

Bitwuzla *
bitwuzla_new(void)
{
  Bitwuzla *res;
  BzlaMemMgr *mm = bzla_mem_mgr_new();
  BZLA_CNEW(mm, res);
  init(res, mm);
  return res;
}

static void
reset(Bitwuzla *bitwuzla)
{
  BzlaIntHashTableIterator it;
  bzla_iter_hashint_init(&it, bitwuzla->d_sort_map);
  while (bzla_iter_hashint_has_next(&it))
  {
    bzla_sort_release(bitwuzla->d_bzla, it.t->keys[it.cur_pos]);
    BitwuzlaSort *sort = bzla_iter_hashint_next_data(&it)->as_ptr;
    BZLA_DELETE(bitwuzla->d_mm, sort);
  }
  bzla_hashint_map_delete(bitwuzla->d_sort_map);
  BZLA_RELEASE_STACK(bitwuzla->d_assumptions);
  BZLA_RELEASE_STACK(bitwuzla->d_unsat_assumptions);
  BZLA_RELEASE_STACK(bitwuzla->d_unsat_core);
  BZLA_RELEASE_STACK(bitwuzla->d_term_children);
  BZLA_RELEASE_STACK(bitwuzla->d_fun_domain_sorts);
  BZLA_RELEASE_STACK(bitwuzla->d_sort_fun_domain_sorts);
  BZLA_RELEASE_STACK(bitwuzla->d_array_indices);
  BZLA_RELEASE_STACK(bitwuzla->d_array_values);
  BZLA_RELEASE_STACK(bitwuzla->d_fun_args);
  BZLA_RELEASE_STACK(bitwuzla->d_fun_args_ptr);
  BZLA_RELEASE_STACK(bitwuzla->d_fun_values);
  BZLA_RELEASE_STACK(bitwuzla->d_option_info_values);
  if (bitwuzla->d_bv_value)
  {
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_bv_value);
    bitwuzla->d_bv_value = 0;
  }
  if (bitwuzla->d_fp_significand)
  {
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_fp_significand);
    bitwuzla->d_fp_significand = 0;
  }
  if (bitwuzla->d_fp_exponent)
  {
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_fp_exponent);
    bitwuzla->d_fp_exponent = 0;
  }
  bzla_delete(bitwuzla->d_bzla);
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  reset(bitwuzla);
  BzlaMemMgr *mm = bitwuzla->d_mm;
  BZLA_DELETE(mm, bitwuzla);
  bzla_mem_mgr_delete(mm);
}

void
bitwuzla_reset(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  reset(bitwuzla);
  init(bitwuzla, bitwuzla->d_mm);
}

const char *
bitwuzla_copyright(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return BZLA_LICENSE
      "\n\n"
      "This version of Bitwuzla is linked against the following\n"
      "third party libraries. For copyright information of each\n"
      "library see the corresponding url.\n"
      "\n"
      "  Btor2Tools - tools for the BTOR2 format\n"
      "  https://https://github.com/Boolector/btor2tools\n"
      "\n"
      "  GMP - GNU Multiple Precision Arithmetic Library\n"
      "  https://gmplib.org \n"
#ifdef BZLA_USE_LINGELING
      "\n"
      "  Lingeling\n"
      "  https://github.com/arminbiere/lingeling\n"
#endif
#ifdef BZLA_USE_PICOSAT
      "\n"
      "  PicoSAT\n"
      "  http://fmv.jku.at/picosat\n"
#endif
#ifdef BZLA_USE_MINISAT
      "\n"
      "  MiniSAT\n"
      "  https://github.com/niklasso/minisat\n"
#endif
#ifdef BZLA_USE_CADICAL
      "\n"
      "  CaDiCaL\n"
      "  https://github.com/arminbiere/cadical\n"
#endif
#ifdef BZLA_USE_CMS
      "\n"
      "  CryptoMiniSat\n"
      "  https://github.com/msoos/cryptominisat\n"
#endif
#ifdef BZLA_USE_SYMFPU
      "\n"
      "  SymFPU\n"
      "  https://github.com/martin-cs/symfpu \n"
#endif
      "";
}

const char *
bitwuzla_version(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_version(BZLA_IMPORT_BITWUZLA(bitwuzla));
}

const char *
bitwuzla_git_id(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_git_id(BZLA_IMPORT_BITWUZLA(bitwuzla));
}

bool
bitwuzla_terminate(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_terminate(BZLA_IMPORT_BITWUZLA(bitwuzla)) != 0;
}

void
bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                  int32_t (*fun)(void *),
                                  void *state)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  bzla_set_term(BZLA_IMPORT_BITWUZLA(bitwuzla), fun, state);
}

void *
bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_get_term_state(BZLA_IMPORT_BITWUZLA(bitwuzla));
}

void
bitwuzla_set_abort_callback(void (*fun)(const char *msg))
{
  bzla_set_abort_callback(fun);
}

void
bitwuzla_set_option(Bitwuzla *bitwuzla, BitwuzlaOption option, uint32_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_CHECK_OPTION_VALUE(bzla, opt, value);

  if (option == BITWUZLA_OPT_INCREMENTAL)
  {
    BZLA_ABORT(bzla->bzla_sat_bzla_called > 0,
               "enabling/disabling incremental usage after having called "
               "'bitwuzla_check_sat' is not allowed");
  }

  if (value)
  {
    if (option == BITWUZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)),
                 "incremental solving cannot be enabled "
                 "if unconstrained optimization is enabled");
    }
    else if (option == BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)
    {
      BZLA_ABORT(
          bzla_opt_get(
              bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_PRODUCE_MODELS)),
          "unconstrained optimization cannot be enabled "
          "if model generation is enabled");
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_INCREMENTAL)),
          "unconstrained optimization cannot be enabled "
          "in incremental mode");
    }
    else if (option == BITWUZLA_OPT_FUN_DUAL_PROP)
    {
      BZLA_ABORT(bzla_opt_get(
                     bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_JUST)),
                 "enabling multiple optimization techniques is not allowed");
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_NONDESTR_SUBST)),
                 "non-destructive substitution is not supported with dual "
                 "propagation");
    }
    else if (option == BITWUZLA_OPT_FUN_JUST)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_DUAL_PROP)),
          "enabling multiple optimization techniques is not allowed");
    }
    else if (option == BITWUZLA_OPT_PP_NONDESTR_SUBST)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_DUAL_PROP)),
          "non-destructive substitution is not supported with dual "
          "propagation");
    }
    else if (option == BITWUZLA_OPT_PRODUCE_MODELS)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)),
                 "model generation cannot be enabled "
                 "if unconstrained optimization is enabled");
    }
  }
  else
  {
    if (option == BITWUZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PRODUCE_UNSAT_CORES)),
                 "incremental solving cannot be disabled "
                 "when unsat cores are enabled");
    }
  }

  uint32_t val = bzla_opt_get(bzla, opt);

  if (opt == BZLA_OPT_SAT_ENGINE)
  {
    if (false
#ifndef BZLA_USE_LINGELING
        || value == BZLA_SAT_ENGINE_LINGELING
#endif
#ifndef BZLA_USE_CADICAL
        || value == BZLA_SAT_ENGINE_CADICAL
#endif
#ifndef BZLA_USE_MINISAT
        || value == BZLA_SAT_ENGINE_MINISAT
#endif
#ifndef BZLA_USE_PICOSAT
        || value == BZLA_SAT_ENGINE_PICOSAT
#endif
#ifndef BZLA_USE_CMS
        || value == BZLA_SAT_ENGINE_CMS
#endif
    )
    {
      BZLA_WARN(true,
                "SAT solver %s not compiled in, using %s",
                g_bzla_se_name[value],
                g_bzla_se_name[val]);
      value = val;
    }
  }
#ifndef BZLA_USE_LINGELING
  if (opt == BZLA_OPT_SAT_ENGINE_LGL_FORK)
  {
    value = val;
    BZLA_WARN (true,
              "SAT solver Lingeling not compiled in, will not set option "
              "to clone/fork Lingeling");
  }
#endif
  if (opt == BZLA_OPT_RW_LEVEL)
  {
    BZLA_ABORT(
        BZLA_COUNT_STACK (bzla->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }
  bzla_opt_set(bzla, opt, value);
}

void
bitwuzla_set_option_str(Bitwuzla *bitwuzla,
                        BitwuzlaOption option,
                        const char *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_ABORT(
      !bzla_opt_is_enum_option(bzla, opt),
      "option expects an integer value, use bitwuzla_set_option instead.");
  BZLA_ABORT(!bzla_opt_is_enum_option_value(bzla, opt, value),
             "invalid option value '%s'",
             value);

  bzla_opt_set(bzla, opt, bzla_opt_get_enum_value(bzla, opt, value));
}

uint32_t
bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  return bzla_opt_get(bzla, opt);
}

const char*
bitwuzla_get_option_str(Bitwuzla *bitwuzla,
                        BitwuzlaOption option)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_ABORT(!bzla_opt_is_enum_option(bzla, opt),
             "option is configured with an integer value, use "
             "bitwuzla_get_option instead.");
  return bzla_opt_get_str_value(bzla, opt);
}

void
bitwuzla_get_option_info(Bitwuzla *bitwuzla,
                         BitwuzlaOption option,
                         BitwuzlaOptionInfo *info)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(info);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);

  BZLA_CLR(info);
  info->opt        = option;
  info->shrt       = bzla_opt_get_shrt(bzla, opt);
  info->lng        = bzla_opt_get_lng(bzla, opt);
  info->desc       = bzla_opt_get_desc(bzla, opt);
  info->is_numeric = !bzla_opt_is_enum_option(bzla, opt);

  if (info->is_numeric)
  {
    info->numeric.cur_val = bzla_opt_get(bzla, opt);
    info->numeric.def_val = bzla_opt_get_dflt(bzla, opt);
    info->numeric.min_val = bzla_opt_get_min(bzla, opt);
    info->numeric.max_val = bzla_opt_get_max(bzla, opt);
  }
  else
  {
    BZLA_RESET_STACK(bitwuzla->d_option_info_values);
    info->string.cur_val = bzla_opt_get_str_value(bzla, opt);

    int32_t def_val = bzla_opt_get_dflt(bzla, opt);
    BzlaPtrHashTableIterator it;
    BzlaOptHelp *oh;
    bzla_iter_hashptr_init(&it, bzla->options[opt].options);
    while (bzla_iter_hashptr_has_next(&it))
    {
      oh = it.bucket->data.as_ptr;
      BZLA_PUSH_STACK(bitwuzla->d_option_info_values,
                      bzla_iter_hashptr_next(&it));
      if (oh->val == def_val)
      {
        info->string.def_val = BZLA_TOP_STACK(bitwuzla->d_option_info_values);
      }
    }
    info->string.num_values = BZLA_COUNT_STACK(bitwuzla->d_option_info_values);
    info->string.values     = bitwuzla->d_option_info_values.start;
  }
}

const BitwuzlaSort *
bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                       const BitwuzlaSort *index,
                       const BitwuzlaSort *element)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(index);
  BZLA_CHECK_ARG_NOT_NULL(element);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, index);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, element);

  Bzla *bzla       = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId isort = BZLA_IMPORT_BITWUZLA_SORT(index);
  BzlaSortId esort = BZLA_IMPORT_BITWUZLA_SORT(element);

  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, isort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, esort);

  BzlaSortId res = bzla_sort_array(bzla, isort, esort);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaSort *
bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bool(bzla);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaSort *
bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bv(bzla, size);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaSort *
bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla, uint32_t exp_size, uint32_t sig_size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(exp_size);
  BZLA_CHECK_ARG_NOT_ZERO(sig_size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_fp(bzla, exp_size, sig_size);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaSort *
bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                     uint32_t arity,
                     const BitwuzlaSort *domain[],
                     const BitwuzlaSort *codomain)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(arity);
  BZLA_CHECK_ARG_NOT_NULL(domain);
  BZLA_CHECK_ARG_NOT_NULL(codomain);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, codomain);

  Bzla *bzla      = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId cdom = BZLA_IMPORT_BITWUZLA_SORT(codomain);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, cdom);

  BzlaSortId dom[arity];
  for (uint32_t i = 0; i < arity; i++)
  {
    dom[i] = BZLA_IMPORT_BITWUZLA_SORT(domain[i]);
    BZLA_CHECK_SORT_BITWUZLA_AT_IDX(bitwuzla, domain[i], i);
    BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, dom[i], i);
  }
  BzlaSortId tupsort = bzla_sort_tuple(bzla, dom, arity);

  BzlaSortId res = bzla_sort_fun(bzla, tupsort, cdom);
  bzla_sort_release(bzla, tupsort);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaSort *
bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_rm(bzla);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

const BitwuzlaTerm *
bitwuzla_mk_true(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_true(bzla);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_false(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_false(bzla);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_one(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_ones(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_min_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_max_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_nan(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                     const BitwuzlaSort *sort,
                     const char *value,
                     BitwuzlaBVBase base)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(value);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  uint32_t size = bzla_sort_bv_get_width(bzla, bzla_sort);
  BzlaBitVector *bv;
  switch (base)
  {
    case BITWUZLA_BV_BASE_BIN: {
      for (const char *p = value; *p; p++)
      {
        BZLA_ABORT(*p != '1' && *p != '0', "invalid binary string '%s'", value);
      }
      BZLA_ABORT(size < strlen(value),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv               = bzla_bv_char_to_bv(bzla->mm, value);
      uint32_t bv_size = bzla_bv_get_width(bv);

      if (bv_size < size)
      {
        BzlaBitVector *ext = bzla_bv_uext(bzla->mm, bv, size - bv_size);
        bzla_bv_free(bzla->mm, bv);
        bv = ext;
      }
      break;
    }

    case BITWUZLA_BV_BASE_DEC: {
      const char *p = value;
      if (*p && p[0] == '-')
      {
        ++p;
      }
      BZLA_ABORT(!*p, "invalid decimal string '%s'", value);
      for (; *p; p++)
      {
        /* 48-57: 0-9 */
        BZLA_ABORT(*p < '0' || *p > '9', "invalid decimal string '%s'", value);
      }
      BZLA_ABORT(!bzla_util_check_dec_to_bv(bzla->mm, value, size),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_constd(bzla->mm, value, size);
      break;
    }

    default:
      BZLA_ABORT(base != BITWUZLA_BV_BASE_HEX,
                 "invalid base for numerical string '%s'",
                 value);
      for (const char *p = value; *p; p++)
      {
        /* 48-57: 0-9, 65-70: A-F, 97-102: a-f */
        BZLA_ABORT((*p < 48 || *p > 57) && (*p < 65 || *p > 70)
                       && (*p < 97 || *p > 102),
                   "invalid hex string '%s'",
                   value);
      }
      BZLA_ABORT(!bzla_util_check_hex_to_bv(bzla->mm, value, size),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_consth(bzla->mm, value, size);
      break;
  }
  BzlaNode *res = bzla_exp_bv_const(bzla, bv);
  assert(bzla_node_get_sort_id(res) == bzla_sort);
  bzla_bv_free(bzla->mm, bv);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
                            const BitwuzlaSort *sort,
                            uint64_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  BzlaBitVector *bv = bzla_bv_uint64_to_bv(
      bzla->mm, value, bzla_sort_bv_get_width(bzla, bzla_sort));
  BzlaNode *res = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                     const BitwuzlaTerm *bv_sign,
                     const BitwuzlaTerm *bv_exponent,
                     const BitwuzlaTerm *bv_significand)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(bv_sign);
  BZLA_CHECK_ARG_NOT_NULL(bv_exponent);
  BZLA_CHECK_ARG_NOT_NULL(bv_significand);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *sign = BZLA_IMPORT_BITWUZLA_TERM(bv_sign);
  BzlaNode *exp  = BZLA_IMPORT_BITWUZLA_TERM(bv_exponent);
  BzlaNode *sig  = BZLA_IMPORT_BITWUZLA_TERM(bv_significand);
  assert(bzla_node_get_ext_refs(sign));
  assert(bzla_node_get_ext_refs(exp));
  assert(bzla_node_get_ext_refs(sig));
  BZLA_CHECK_TERM_BZLA(bzla, sign);
  BZLA_CHECK_TERM_BZLA(bzla, exp);
  BZLA_CHECK_TERM_BZLA(bzla, sig);
  BZLA_CHECK_TERM_IS_BV(bzla, sign);
  BZLA_CHECK_TERM_IS_BV(bzla, exp);
  BZLA_CHECK_TERM_IS_BV(bzla, sig);
  BZLA_CHECK_TERM_IS_BV_VAL(sign);
  BZLA_CHECK_TERM_IS_BV_VAL(exp);
  BZLA_CHECK_TERM_IS_BV_VAL(sig);
  BZLA_ABORT(
      bzla_node_bv_get_width(bzla, sign) != 1,
      "invalid bit-vector size for argument 'bv_sign', expected size one");

  BzlaNode *res = bzla_exp_fp_const(bzla, sign, exp, sig);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value_from_real(Bitwuzla *bitwuzla,
                               const BitwuzlaSort *sort,
                               const BitwuzlaTerm *rm,
                               const char *real)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(rm);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(real);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);
  BZLA_ABORT(!bzla_util_is_valid_real(real),
             "invalid value '%s', expected real number",
             real);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *bzla_rm = BZLA_IMPORT_BITWUZLA_TERM(rm);
  assert(bzla_node_get_ext_refs(bzla_rm));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_rm);
  BZLA_CHECK_TERM_IS_RM(bzla, bzla_rm);

  BzlaNode *res = bzla_exp_fp_const_from_real(bzla, bzla_sort, bzla_rm, real);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value_from_rational(Bitwuzla *bitwuzla,
                                   const BitwuzlaSort *sort,
                                   const BitwuzlaTerm *rm,
                                   const char *num,
                                   const char *den)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(rm);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(num);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(den);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);
  BZLA_ABORT(!bzla_util_is_valid_real(num),
             "invalid value '%s' for numerator, expected real number");
  BZLA_ABORT(!bzla_util_is_valid_real(den),
             "invalid value '%s' for denominator, expected real number");

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *bzla_rm = BZLA_IMPORT_BITWUZLA_TERM(rm);
  assert(bzla_node_get_ext_refs(bzla_rm));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_rm);
  BZLA_CHECK_TERM_IS_RM(bzla, bzla_rm);

  BzlaNode *res =
      bzla_exp_fp_const_from_rational(bzla, bzla_sort, bzla_rm, num, den);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(rm >= BITWUZLA_RM_MAX, "invalid rounding mode");

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_rm_const(bzla, BZLA_IMPORT_BITWUZLA_RM(rm));
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg)
{
  const BitwuzlaTerm *args[] = {arg};
  return bitwuzla_mk_term(bitwuzla, kind, 1, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  return bitwuzla_mk_term(bitwuzla, kind, 2, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1,
                  const BitwuzlaTerm *arg2)
{
  const BitwuzlaTerm *args[] = {arg0, arg1, arg2};
  return bitwuzla_mk_term(bitwuzla, kind, 3, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term(Bitwuzla *bitwuzla,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 const BitwuzlaTerm *args[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode **bzla_args = BZLA_IMPORT_BITWUZLA_TERMS(args);

  BzlaNode *res = NULL;
  switch (kind)
  {
    case BITWUZLA_KIND_EQUAL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, sort_any, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_eq);
      break;

    case BITWUZLA_KIND_DISTINCT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, sort_any, true);
      res = mk_term_pairwise(bzla, bzla_args, argc, bzla_exp_ne);
      break;

    case BITWUZLA_KIND_IMPLIES:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_right_assoc(bzla, bzla_args, argc, bzla_exp_implies);
      break;

    case BITWUZLA_KIND_IFF:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = bzla_exp_iff(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_NOT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bool, true);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_AND:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_and);
      break;

    case BITWUZLA_KIND_OR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_or);
      break;

    case BITWUZLA_KIND_XOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_xor);
      break;

    case BITWUZLA_KIND_BV_COMP:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_eq(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_NOT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDXOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redxor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDAND:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redand(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_XOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_xor);
      break;

    case BITWUZLA_KIND_BV_XNOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_xnor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_AND:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_and);
      break;

    case BITWUZLA_KIND_BV_NAND:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_nand(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_OR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_or);
      break;

    case BITWUZLA_KIND_BV_NOR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_nor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ADD:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_add);
      break;

    case BITWUZLA_KIND_BV_UADD_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_uaddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SADD_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_saddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_MUL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_mul);
      break;

    case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_umulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_smulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ult(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_slt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ulte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_slte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ugt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sgt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ugte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sgte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sll(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_srl(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ASHR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sra(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SUB:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sub(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_usubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ssubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UDIV:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_udiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sdiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sdivo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UREM:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_urem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SREM:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_srem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMOD:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_smod(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_rol(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROR:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ror(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_INC:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_inc(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_DEC:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_dec(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_CONCAT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_bv, false);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_concat);
      break;

    case BITWUZLA_KIND_FP_FP:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 0, bzla_sort_is_bv, false);
      BZLA_ABORT(
          bzla_node_bv_get_width(bzla, bzla_args[0]) != 1,
          "invalid bit-vector size for argument at index 0, expected size 1");
      res = bzla_exp_fp_fp(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_ABS:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_abs(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NORMAL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_normal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_SUBNORMAL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_subnormal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NAN:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_nan(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_ZERO:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_zero(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_INF:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_inf(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_POS:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_pos(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_MIN:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_min(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_MAX:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_max(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_REM:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_rem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_EQ:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_fpeq);
      break;

    case BITWUZLA_KIND_FP_LEQ:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_lte);
      break;

    case BITWUZLA_KIND_FP_LT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_lt);
      break;

    case BITWUZLA_KIND_FP_GEQ:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_gte);
      break;

    case BITWUZLA_KIND_FP_GT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_gt);
      break;

    case BITWUZLA_KIND_FP_SQRT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_sqrt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_RTI:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_rti(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_ADD:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_add(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_SUB:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_sub(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_MUL:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_mul(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_DIV:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_div(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_FMA:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 4, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_fma(
          bzla, bzla_args[0], bzla_args[1], bzla_args[2], bzla_args[3]);
      break;

    case BITWUZLA_KIND_ARRAY_SELECT:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 2, argc, 0, sort_any, false);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      BZLA_ABORT(
          bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[1]),
          "sort of index term does not match index sort of array");
      res = bzla_exp_read(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_ARRAY_STORE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 0, sort_any, false);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[2], 2);
      BZLA_ABORT(
          bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[1]),
          "sort of index term does not match index sort of array");
      BZLA_ABORT(
          bzla_sort_array_get_element(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[2]),
          "sort of element term does not match element sort of array");
      res = bzla_exp_write(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_ITE:
      BZLA_CHECK_MK_TERM_ARGS(
          kind, false, bzla_args, 3, argc, 1, sort_any, true);
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_cond(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_APPLY: {
      BZLA_ABORT(argc < 2,
                 "invalid number of arguments for kind '%s', expected at least "
                 "2, got %u",
                 bzla_kind_to_str[kind],
                 argc);
      BzlaNodePtrStack apply_args;
      BZLA_INIT_STACK(bzla->mm, apply_args);
      uint32_t apply_argc = argc - 1;
      for (uint32_t i = 1; i <= apply_argc; i++)
      {
        BZLA_CHECK_ARG_NOT_NULL_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(apply_args, bzla_args[i]);
      }
      BzlaNode *fun = bzla_args[0];
      BZLA_CHECK_TERM_IS_FUN_AT_IDX(fun, apply_argc);
      BZLA_ABORT(
          bzla_node_fun_get_arity(bzla, fun) != argc - 1,
          "number of given arguments to function must match arity of function");
      BzlaNode *apply_args_node =
          bzla_exp_args(bzla, apply_args.start, apply_argc);
      BZLA_ABORT(
          bzla_node_get_sort_id(apply_args_node)
              != bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun)),
          "sorts of arguments to apply don't match domain sorts of "
          "given function");
      res = bzla_exp_apply(bzla, fun, apply_args_node);
      BZLA_RELEASE_STACK(apply_args);
      bzla_node_release(bzla, apply_args_node);
    }
    break;

    case BITWUZLA_KIND_LAMBDA: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'lambda', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(bzla_args[paramc], paramc);
      BZLA_CHECK_TERM_IS_BV_LAMBDA_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_fun(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_FORALL: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'forall', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_forall_n(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_EXISTS: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'exists', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_exists_n(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    default:
      BZLA_ABORT(true, "unexpected operator kind '%s'", bzla_kind_to_str[kind]);
  }
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg};
  const uint32_t idxs[]      = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 1, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg};
  const uint32_t idxs[]      = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 2, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  const uint32_t idxs[]      = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 1, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  const uint32_t idxs[]      = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 2, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                         BitwuzlaKind kind,
                         uint32_t argc,
                         const BitwuzlaTerm *args[],
                         uint32_t idxc,
                         const uint32_t idxs[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode **bzla_args = BZLA_IMPORT_BITWUZLA_TERMS(args);
  for (uint32_t i = 0; i < argc; i++)
  {
    assert(bzla_node_get_ext_refs(bzla_args[i]));
    BZLA_CHECK_TERM_BZLA(bzla, bzla_args[i]);
  }

  BzlaNode *res = NULL;
  switch (kind)
  {
    case BITWUZLA_KIND_BV_EXTRACT:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 2, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(idxs[0] > bzla_node_bv_get_width(bzla, bzla_args[0]),
                 "upper index must be < bit-vector size of given term");
      BZLA_ABORT(idxs[0] < idxs[1], "upper index must be >= lower index");
      res = bzla_exp_bv_slice(bzla, bzla_args[0], idxs[0], idxs[1]);
      break;

    case BITWUZLA_KIND_BV_ZERO_EXTEND:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      res = bzla_exp_bv_uext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_SIGN_EXTEND:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      res = bzla_exp_bv_sext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_ROLI:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_roli(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_RORI:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_rori(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_REPEAT:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(((uint32_t)(UINT32_MAX / idxs[0]))
                     < bzla_node_bv_get_width(bzla, bzla_args[0]),
                 "resulting bit-vector size of 'repeat' exceeds maximum "
                 "bit-vector size of %u",
                 UINT32_MAX);
      res = bzla_exp_bv_repeat(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_FP_TO_SBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_sbv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_UBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_ubv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_BV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 1, argc, 2, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(
          idxs[0] + idxs[1] != bzla_node_bv_get_width(bzla, bzla_args[0]),
          "size of bit-vector does not match given floating-point format");
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res             = bzla_exp_fp_to_fp_from_bv(bzla, bzla_args[0], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_FP: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 2, argc, 2, idxc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_fp(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_SBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 2, argc, 2, idxc, 1, bzla_sort_is_bv, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_sbv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_UBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          kind, bzla_args, 2, argc, 2, idxc, 1, bzla_sort_is_bv, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_ubv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;
    default:
      BZLA_ABORT(true, "unexpected operator kind '%s'", bzla_kind_to_str[kind]);
  }
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_const(Bitwuzla *bitwuzla,
                  const BitwuzlaSort *sort,
                  const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);

  BzlaNode *res;
  if (bzla_sort_is_array(bzla, bzla_sort))
  {
    res = bzla_exp_array(bzla, bzla_sort, symbol);
  }
  else if (bzla_sort_is_fun(bzla, bzla_sort))
  {
    res = bzla_exp_uf(bzla, bzla_sort, symbol);
  }
  else
  {
    res = bzla_exp_var(bzla, bzla_sort, symbol);
  }
  (void) bzla_hashptr_table_add(bzla->inputs, bzla_node_copy(bzla, res));
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                        const BitwuzlaSort *sort,
                        const BitwuzlaTerm *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(value);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  BzlaNode *bzla_val = BZLA_IMPORT_BITWUZLA_TERM(value);
  assert(bzla_node_get_ext_refs(bzla_val));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_val);
  BZLA_CHECK_TERM_NOT_IS_FUN(bzla_val);
  BZLA_ABORT(bzla_node_get_sort_id(bzla_val)
                 != bzla_sort_array_get_element(bzla, bzla_sort),
             "sort of 'value' does not match array element sort");
  BzlaNode *res = bzla_exp_const_array(bzla, bzla_sort, bzla_val);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const BitwuzlaTerm *
bitwuzla_mk_var(Bitwuzla *bitwuzla,
                const BitwuzlaSort *sort,
                const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_param(bzla, bzla_sort, symbol);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

void
bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  if (nlevels)
  {
    for (uint32_t i = 0; i < nlevels; i++)
    {
      BZLA_PUSH_STACK(bzla->assertions_trail,
                      BZLA_COUNT_STACK(bzla->assertions));
    }
    bzla->num_push_pop++;
  }
}

void
bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_ABORT(
      nlevels > BZLA_COUNT_STACK(bzla->assertions_trail),
      "number of levels to pop (%u) greater than number of pushed levels (%u)",
      nlevels,
      BZLA_COUNT_STACK(bzla->assertions_trail));

  if (nlevels)
  {
    uint32_t pos = 0;
    for (uint32_t i = 0; i < nlevels; i++)
    {
      pos = BZLA_POP_STACK(bzla->assertions_trail);
    }
    while (BZLA_COUNT_STACK(bzla->assertions) > pos)
    {
      BzlaNode *cur = BZLA_POP_STACK(bzla->assertions);
      bzla_hashint_table_remove(bzla->assertions_cache, bzla_node_get_id(cur));
      bzla_node_release(bzla, cur);
    }
    bzla->num_push_pop++;
  }
}

void
bitwuzla_assert(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  reset_assumptions(bitwuzla);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  /* Note: All assertions at a context level > 0 are internally handled as
   *       assumptions. */
  if (BZLA_COUNT_STACK(bzla->assertions_trail) > 0
      || bzla_opt_get(bzla, BZLA_OPT_PRODUCE_UNSAT_CORES))
  {
    int32_t id = bzla_node_get_id(bzla_term);
    if (!bzla_hashint_table_contains(bzla->assertions_cache, id))
    {
      BZLA_PUSH_STACK(bzla->assertions, bzla_node_copy(bzla, bzla_term));
      bzla_hashint_table_add(bzla->assertions_cache, id);
    }
  }
  else
  {
    bzla_assert_exp(bzla, bzla_term);
  }
}

void
bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  reset_assumptions(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  bzla_assume_exp(bzla, bzla_term);
  BZLA_PUSH_STACK(bitwuzla->d_assumptions, term);
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_UNSAT(bzla, "check for unsat assumptions");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_ABORT(!bzla_is_assumption_exp(bzla, bzla_term),
             "'exp' must be an assumption");
  return bzla_failed_exp(bzla, bzla_term);
}

const BitwuzlaTerm **
bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(size);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_UNSAT(bzla, "get unsat assumptions");

  BZLA_RESET_STACK(bitwuzla->d_unsat_assumptions);

  for (size_t i = 0; i < BZLA_COUNT_STACK(bitwuzla->d_assumptions); i++)
  {
    BzlaNode *bzla_assumption =
        BZLA_IMPORT_BITWUZLA_TERM(BZLA_PEEK_STACK(bitwuzla->d_assumptions, i));
    if (bzla_failed_exp(bzla, bzla_assumption))
    {
      BZLA_PUSH_STACK(bitwuzla->d_unsat_assumptions,
                      BZLA_EXPORT_BITWUZLA_TERM(bzla_assumption));
    }
  }
  *size = BZLA_COUNT_STACK(bitwuzla->d_unsat_assumptions);
  return bitwuzla->d_unsat_assumptions.start;
}

const BitwuzlaTerm **
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(size);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla);
  BZLA_CHECK_UNSAT(bzla, "get unsat core");

  BZLA_RESET_STACK(bitwuzla->d_unsat_core);

  for (uint32_t i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
  {
    BzlaNode *cur = BZLA_PEEK_STACK(bzla->assertions, i);
    if (cur == NULL) continue;

    if (bzla_failed_exp(bzla, cur))
    {
      BZLA_PUSH_STACK(bitwuzla->d_unsat_core,
                      BZLA_EXPORT_BITWUZLA_TERM(bzla_node_copy(bzla, cur)));
      bzla_node_inc_ext_ref_counter(bzla, cur);
    }
  }
  *size = BZLA_COUNT_STACK(bitwuzla->d_unsat_core);
  return bitwuzla->d_unsat_core.start;
}

void
bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  bzla_fixate_assumptions(bzla);
}

void
bitwuzla_reset_assumptions(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  bzla_reset_assumptions(bzla);
}

BitwuzlaResult
bitwuzla_simplify(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  reset_assumptions(bitwuzla);

  Bzla *bzla                = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSolverResult bzla_res = bzla_simplify(bzla);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaResult
bitwuzla_check_sat(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  reset_assumptions(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  if (bzla->bzla_sat_bzla_called > 0)
  {
    BZLA_CHECK_OPT_INCREMENTAL(bzla);
  }
  BZLA_ABORT(
      bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL) && bzla->quantifiers->count,
      "incremental solving is currently not supported with quantifiers");

  BzlaSolverResult bzla_res = bzla_check_sat(bzla, -1, -1);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

const BitwuzlaTerm *
bitwuzla_get_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BzlaNode *res = bzla_model_get_value(bzla, bzla_term);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

const char *
bitwuzla_get_bv_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_ABORT(!bzla_node_is_bv(bzla, bzla_term),
             "given term is not a bit-vector term");

  if (bitwuzla->d_bv_value)
  {
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_bv_value);
  }
  const BzlaBitVector *bv = bzla_model_get_bv(bzla, bzla_term);
  bitwuzla->d_bv_value    = bzla_bv_to_char(bitwuzla->d_mm, bv);
  return bitwuzla->d_bv_value;
}

void
bitwuzla_get_fp_value(Bitwuzla *bitwuzla,
                      const BitwuzlaTerm *term,
                      const char **sign,
                      const char **exponent,
                      const char **significand)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(sign);
  BZLA_CHECK_ARG_NOT_NULL(exponent);
  BZLA_CHECK_ARG_NOT_NULL(significand);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_ABORT(!bzla_node_is_fp(bzla, bzla_term),
             "given term is not a floating-point term");

  const BzlaBitVector *bv = bzla_model_get_bv(bzla, bzla_term);
  BzlaBitVector *bv_sign, *bv_exp, *bv_sig;
  bzla_fp_ieee_bv_as_bvs(
      bzla, bv, bzla_node_get_sort_id(bzla_term), &bv_sign, &bv_exp, &bv_sig);

  if (bitwuzla->d_fp_exponent)
  {
    assert(bitwuzla->d_fp_significand);
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_fp_exponent);
    bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_fp_significand);
  }
  bitwuzla->d_fp_exponent    = bzla_bv_to_char(bitwuzla->d_mm, bv_exp);
  bitwuzla->d_fp_significand = bzla_bv_to_char(bitwuzla->d_mm, bv_sig);

  *sign        = bzla_bv_is_one(bv_sign) ? "1" : "0";
  *exponent    = bitwuzla->d_fp_exponent;
  *significand = bitwuzla->d_fp_significand;

  bzla_bv_free(bzla->mm, bv_sign);
  bzla_bv_free(bzla->mm, bv_exp);
  bzla_bv_free(bzla->mm, bv_sig);
}

const char *
bitwuzla_get_rm_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_ABORT(!bzla_node_is_rm(bzla, bzla_term),
             "given term is not a rounding mode term");

  BzlaRoundingMode rm = bzla_rm_from_bv(bzla_model_get_bv(bzla, bzla_term));
  if (rm == BZLA_RM_RNA) return "RNA";
  if (rm == BZLA_RM_RNE) return "RNE";
  if (rm == BZLA_RM_RTN) return "RTN";
  if (rm == BZLA_RM_RTP) return "RTP";
  assert(rm == BZLA_RM_RTZ);
  return "RTZ";
}

void
bitwuzla_get_array_value(Bitwuzla *bitwuzla,
                         const BitwuzlaTerm *term,
                         const BitwuzlaTerm ***indices,
                         const BitwuzlaTerm ***values,
                         size_t *size,
                         const BitwuzlaTerm **default_value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(indices);
  BZLA_CHECK_ARG_NOT_NULL(values);
  BZLA_CHECK_ARG_NOT_NULL(size);
  BZLA_CHECK_ARG_NOT_NULL(default_value);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_ABORT(!bzla_node_is_array(bzla_term), "given term is not an array term");

  BzlaNodePtrStack _indices, _values;
  BzlaNode *_default_value = 0, *index, *value;

  BZLA_INIT_STACK(bitwuzla->d_mm, _indices);
  BZLA_INIT_STACK(bitwuzla->d_mm, _values);
  bzla_model_get_array_model(
      bzla, bzla_term, &_indices, &_values, &_default_value);
  assert(BZLA_COUNT_STACK(_indices) == BZLA_COUNT_STACK(_values));

  *indices       = 0;
  *values        = 0;
  *size          = 0;
  *default_value = 0;

  if (BZLA_EMPTY_STACK(_indices) && !_default_value)
  {
    BZLA_RELEASE_STACK(_indices);
    BZLA_RELEASE_STACK(_values);
    return;
  }

  BZLA_RESET_STACK(bitwuzla->d_array_indices);
  BZLA_RESET_STACK(bitwuzla->d_array_values);

  for (size_t i = 0; i < BZLA_COUNT_STACK(_indices); ++i)
  {
    index = BZLA_PEEK_STACK(_indices, i);
    value = BZLA_PEEK_STACK(_values, i);
    BZLA_PUSH_STACK(bitwuzla->d_array_indices,
                    BZLA_EXPORT_BITWUZLA_TERM(index));
    bzla_node_inc_ext_ref_counter(bzla, index);
    BZLA_PUSH_STACK(bitwuzla->d_array_values, BZLA_EXPORT_BITWUZLA_TERM(value));
    bzla_node_inc_ext_ref_counter(bzla, value);
  }

  *size = BZLA_COUNT_STACK(_values);

  if (*size)
  {
    *indices = bitwuzla->d_array_indices.start;
    *values  = bitwuzla->d_array_values.start;
  }

  if (_default_value)
  {
    *default_value = BZLA_EXPORT_BITWUZLA_TERM(_default_value);
    bzla_node_inc_ext_ref_counter(bzla, _default_value);
  }
  BZLA_RELEASE_STACK(_indices);
  BZLA_RELEASE_STACK(_values);
}

void
bitwuzla_get_fun_value(Bitwuzla *bitwuzla,
                       const BitwuzlaTerm *term,
                       const BitwuzlaTerm ****args,
                       size_t *arity,
                       const BitwuzlaTerm ***values,
                       size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(args);
  BZLA_CHECK_ARG_NOT_NULL(arity);
  BZLA_CHECK_ARG_NOT_NULL(values);
  BZLA_CHECK_ARG_NOT_NULL(size);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_ABORT(!bzla_sort_is_fun(bzla, bzla_node_get_sort_id(bzla_term)),
             "given term is not a function term");

  uint32_t _arity = bzla_node_fun_get_arity(bzla, bzla_term);
  BzlaNodePtrStack _args, _values;

  BZLA_INIT_STACK(bitwuzla->d_mm, _args);
  BZLA_INIT_STACK(bitwuzla->d_mm, _values);
  bzla_model_get_fun_model(bzla, bzla_term, &_args, &_values);
  assert(BZLA_COUNT_STACK(_values) * _arity == BZLA_COUNT_STACK(_args));

  *args   = 0;
  *arity  = 0;
  *values = 0;
  *size   = 0;

  if (BZLA_EMPTY_STACK(_args))
  {
    BZLA_RELEASE_STACK(_args);
    BZLA_RELEASE_STACK(_values);
    return;
  }

  BZLA_RESET_STACK(bitwuzla->d_fun_args_ptr);
  BZLA_RESET_STACK(bitwuzla->d_fun_args);
  BZLA_RESET_STACK(bitwuzla->d_fun_values);

  BzlaNode *arg, *value;
  for (size_t i = 0; i < BZLA_COUNT_STACK(_args); ++i)
  {
    arg = BZLA_PEEK_STACK(_args, i);
    BZLA_PUSH_STACK(bitwuzla->d_fun_args, BZLA_EXPORT_BITWUZLA_TERM(arg));
    bzla_node_inc_ext_ref_counter(bzla, arg);
  }

  for (size_t i = 0; i < BZLA_COUNT_STACK(_values); ++i)
  {
    BZLA_PUSH_STACK(bitwuzla->d_fun_args_ptr,
                    bitwuzla->d_fun_args.start + i * _arity);
    value = BZLA_PEEK_STACK(_values, i);
    BZLA_PUSH_STACK(bitwuzla->d_fun_values, BZLA_EXPORT_BITWUZLA_TERM(value));
    bzla_node_inc_ext_ref_counter(bzla, value);
  }

  assert(BZLA_COUNT_STACK(bitwuzla->d_fun_args_ptr)
         == BZLA_COUNT_STACK(bitwuzla->d_fun_values));

  *arity  = _arity;
  *args   = bitwuzla->d_fun_args_ptr.start;
  *values = bitwuzla->d_fun_values.start;
  *size   = BZLA_COUNT_STACK(_values);
  BZLA_RELEASE_STACK(_args);
  BZLA_RELEASE_STACK(_values);
}

void
bitwuzla_print_model(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);
  BZLA_ABORT(strcmp(format, "btor") && strcmp(format, "smt2"),
             "invalid model output format: %s",
             format);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "print model");
  bzla_print_model(bzla, format, file);
}

void
bitwuzla_dump_formula(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "dumping in incremental mode is currently not supported");
  if (strcmp(format, "smt2") == 0)
  {
    bzla_dumpsmt_dump(bzla, file);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_dumpbtor_dump(bzla, file, 1);
  }
  else if (strcmp(format, "aiger_ascii") == 0)
  {
    bzla_dumpaig_dump(bzla, false, file, true);
  }
  else if (strcmp(format, "aiger_binary") == 0)
  {
    bzla_dumpaig_dump(bzla, true, file, true);
  }
  else
  {
    BZLA_ABORT(true,
               "unknown format '%s', expected one of 'smt2', 'bzla', "
               "'aiger_ascii' or 'aiger_binary'",
               format);
  }
}

BitwuzlaResult
bitwuzla_parse(Bitwuzla *bitwuzla,
               FILE *infile,
               const char *infile_name,
               FILE *outfile,
               char **error_msg,
               BitwuzlaResult *parsed_status,
               bool *parsed_smt2)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);
  BZLA_CHECK_ARG_NOT_NULL(parsed_smt2);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing after having created expressions is not allowed");
  int32_t bzla_res = bzla_parse(bitwuzla,
                                infile,
                                infile_name,
                                outfile,
                                error_msg,
                                parsed_status,
                                parsed_smt2);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaResult
bitwuzla_parse_format(Bitwuzla *bitwuzla,
                      const char *format,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      BitwuzlaResult *parsed_status)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing after having created expressions is not allowed");
  int32_t bzla_res = 0;
  if (strcmp(format, "smt2") == 0)
  {
    bzla_res = bzla_parse_smt2(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_res = bzla_parse_btor(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor2") == 0)
  {
    bzla_res = bzla_parse_btor2(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else
  {
    BZLA_ABORT(true,
               "unknown format '%s', expected one of 'smt2', 'bzla' or 'btor2'",
               format);
  }
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

const BitwuzlaTerm *
bitwuzla_substitute_term(Bitwuzla *bitwuzla,
                         const BitwuzlaTerm *term,
                         size_t map_size,
                         const BitwuzlaTerm *map_keys[],
                         const BitwuzlaTerm *map_values[])
{
  const BitwuzlaTerm *terms[1] = {term};
  bitwuzla_substitute_terms(bitwuzla, 1, terms, map_size, map_keys, map_values);
  return terms[0];
}

void
bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
                          size_t terms_size,
                          const BitwuzlaTerm *terms[],
                          size_t map_size,
                          const BitwuzlaTerm *map_keys[],
                          const BitwuzlaTerm *map_values[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(terms_size == 0, "no terms to substitute");
  BZLA_ABORT(map_size == 0, "empty substitution map");

  BzlaNode *k, *v;
  Bzla *bzla                 = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode **bzla_map_keys   = BZLA_IMPORT_BITWUZLA_TERMS(map_keys);
  BzlaNode **bzla_map_values = BZLA_IMPORT_BITWUZLA_TERMS(map_values);

  BzlaNodePtrStack keys, values;
  BZLA_INIT_STACK(bzla->mm, keys);
  BZLA_INIT_STACK(bzla->mm, values);
  for (size_t i = 0; i < map_size; ++i)
  {
    k = bzla_map_keys[i];
    v = bzla_map_values[i];
    BZLA_ABORT(bzla_node_is_inverted(k)
                   || (!bzla_node_is_param(k) && !bzla_node_is_var(k)
                       && !bzla_node_is_uf(k)),
               "expected variable or constant as key at index %u",
               i);
    BZLA_PUSH_STACK(keys, k);
    BZLA_PUSH_STACK(values, bzla_simplify_exp(bzla, v));
  }

  BzlaNodePtrStack bzla_terms;
  BZLA_INIT_STACK(bzla->mm, bzla_terms);
  for (size_t i = 0; i < terms_size; ++i)
  {
    BZLA_PUSH_STACK(
        bzla_terms,
        bzla_simplify_exp(bzla, BZLA_IMPORT_BITWUZLA_TERM(terms[i])));
  }

  bzla_substitute_terms(
      bzla, terms_size, bzla_terms.start, map_size, keys.start, values.start);
  BZLA_RELEASE_STACK(keys);
  BZLA_RELEASE_STACK(values);

  /* Replace terms[i] with substitutions. */
  for (size_t i = 0; i < terms_size; ++i)
  {
    k        = BZLA_PEEK_STACK(bzla_terms, i);
    terms[i] = BZLA_EXPORT_BITWUZLA_TERM(k);
    bzla_node_inc_ext_ref_counter(bzla, k);
  }
  BZLA_RELEASE_STACK(bzla_terms);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_sort_hash(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_bzla_sort;
}

uint32_t
bitwuzla_sort_bv_get_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  return bzla_sort_bv_get_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_exp_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_exp_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_sig_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_sig_width(bzla, bzla_sort);
}

const BitwuzlaSort *
bitwuzla_sort_array_get_index(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(sort->d_bzla,
                                   bzla_sort_array_get_index(bzla, bzla_sort));
}

const BitwuzlaSort *
bitwuzla_sort_array_get_element(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      sort->d_bzla, bzla_sort_array_get_element(bzla, bzla_sort));
}

const BitwuzlaSort **
bitwuzla_sort_fun_get_domain_sorts(const BitwuzlaSort *sort, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(size);

  Bitwuzla *bitwuzla   = sort->d_bzla;
  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  uint32_t arity = bzla_sort_fun_get_arity(bzla, bzla_sort);
  BZLA_RESET_STACK(bitwuzla->d_sort_fun_domain_sorts);
  BzlaTupleSort *tuple_sort =
      &bzla_sort_get_by_id(bzla, bzla_sort_fun_get_domain(bzla, bzla_sort))
           ->tuple;
  assert(arity == tuple_sort->num_elements);
  for (uint32_t i = 0; i < arity; i++)
  {
    BzlaSortId id = tuple_sort->elements[i]->id;
    BZLA_PUSH_STACK(bitwuzla->d_sort_fun_domain_sorts,
                    BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, id));
    bzla_sort_copy(bzla, id);
    inc_ext_refs_sort(bzla, id);
  }
  *size = BZLA_COUNT_STACK(bitwuzla->d_sort_fun_domain_sorts);
  return bitwuzla->d_sort_fun_domain_sorts.start;
}

const BitwuzlaSort *
bitwuzla_sort_fun_get_codomain(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(sort->d_bzla,
                                   bzla_sort_fun_get_codomain(bzla, bzla_sort));
}

uint32_t
bitwuzla_sort_fun_get_arity(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  return bzla_sort_fun_get_arity(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_equal(const BitwuzlaSort *sort0, const BitwuzlaSort *sort1)
{
  BZLA_CHECK_ARG_NOT_NULL(sort0);
  BZLA_CHECK_ARG_NOT_NULL(sort1);
  BZLA_ABORT(sort0->d_bzla != sort1->d_bzla,
             "given sorts are not associated with the same solver instance");

  BzlaSortId bzla_sort0 = BZLA_IMPORT_BITWUZLA_SORT(sort0);
  BzlaSortId bzla_sort1 = BZLA_IMPORT_BITWUZLA_SORT(sort1);
#ifndef NDEBUG
  Bzla *bzla = BZLA_IMPORT_BITWUZLA(sort0->d_bzla);
  assert(bzla_sort_is_valid(bzla, bzla_sort0));
  assert(bzla_sort_is_valid(bzla, bzla_sort1));
#endif

  return bzla_sort0 == bzla_sort1;
}

bool
bitwuzla_sort_is_array(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_array(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_bv(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_bv(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fp(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_fp(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fun(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_fun(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_rm(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_rm(bzla, bzla_sort);
}

void
bitwuzla_sort_dump(const BitwuzlaSort *sort, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  if (strcmp(format, "smt2") == 0)
  {
    bzla_dumpsmt_dump_sort(bzla_sort_get_by_id(bzla, bzla_sort), file);
  }
  else if (strcmp(format, "btor") == 0)
  {
    // Sorts are dumped when dumping terms.
  }
  else
  {
    BZLA_ABORT(
        true, "unknown format '%s', expected one of 'smt2' or 'bzla'", format);
  }
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_term_hash(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_get_id(bzla_term);
}

BitwuzlaKind
bitwuzla_term_get_kind(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  Bzla *bzla          = bzla_node_get_bzla(bzla_term);
  bzla_term           = bzla_simplify_exp(bzla, bzla_term);

  BitwuzlaKind kind;
  BzlaNodeKind k = bzla_node_get_kind(bzla_term);

  if (bzla_node_is_inverted(bzla_term) && !bzla_node_is_bv_const(bzla_term))
  {
    return BITWUZLA_KIND_BV_NOT;
  }

  switch (k)
  {
    case BZLA_BV_SLICE_NODE: kind = BITWUZLA_KIND_BV_EXTRACT; break;
    case BZLA_FP_ABS_NODE: kind = BITWUZLA_KIND_FP_ABS; break;
    case BZLA_FP_IS_INF_NODE: kind = BITWUZLA_KIND_FP_IS_INF; break;
    case BZLA_FP_IS_NAN_NODE: kind = BITWUZLA_KIND_FP_IS_NAN; break;
    case BZLA_FP_IS_NEG_NODE: kind = BITWUZLA_KIND_FP_IS_NEG; break;
    case BZLA_FP_IS_NORM_NODE: kind = BITWUZLA_KIND_FP_IS_NORMAL; break;
    case BZLA_FP_IS_POS_NODE: kind = BITWUZLA_KIND_FP_IS_POS; break;
    case BZLA_FP_IS_SUBNORM_NODE: kind = BITWUZLA_KIND_FP_IS_SUBNORMAL; break;
    case BZLA_FP_IS_ZERO_NODE: kind = BITWUZLA_KIND_FP_IS_ZERO; break;
    case BZLA_FP_NEG_NODE: kind = BITWUZLA_KIND_FP_NEG; break;
    case BZLA_FP_TO_FP_BV_NODE: kind = BITWUZLA_KIND_FP_TO_FP_FROM_BV; break;

    case BZLA_BV_AND_NODE: kind = BITWUZLA_KIND_BV_AND; break;

    case BZLA_BV_EQ_NODE:
    case BZLA_FP_EQ_NODE:
    case BZLA_RM_EQ_NODE:
    case BZLA_FUN_EQ_NODE: kind = BITWUZLA_KIND_EQUAL; break;

    case BZLA_BV_ADD_NODE: kind = BITWUZLA_KIND_BV_ADD; break;
    case BZLA_BV_MUL_NODE: kind = BITWUZLA_KIND_BV_MUL; break;
    case BZLA_BV_ULT_NODE: kind = BITWUZLA_KIND_BV_ULT; break;
    case BZLA_BV_SLL_NODE: kind = BITWUZLA_KIND_BV_SHL; break;
    case BZLA_BV_SLT_NODE: kind = BITWUZLA_KIND_BV_SLT; break;
    case BZLA_BV_SRL_NODE: kind = BITWUZLA_KIND_BV_SHR; break;
    case BZLA_BV_UDIV_NODE: kind = BITWUZLA_KIND_BV_UDIV; break;
    case BZLA_BV_UREM_NODE: kind = BITWUZLA_KIND_BV_UREM; break;
    case BZLA_BV_CONCAT_NODE: kind = BITWUZLA_KIND_BV_CONCAT; break;
    case BZLA_FP_LTE_NODE: kind = BITWUZLA_KIND_FP_LEQ; break;
    case BZLA_FP_LT_NODE: kind = BITWUZLA_KIND_FP_LT; break;
    case BZLA_FP_MIN_NODE: kind = BITWUZLA_KIND_FP_MIN; break;
    case BZLA_FP_MAX_NODE: kind = BITWUZLA_KIND_FP_MAX; break;
    case BZLA_FP_SQRT_NODE: kind = BITWUZLA_KIND_FP_SQRT; break;
    case BZLA_FP_REM_NODE: kind = BITWUZLA_KIND_FP_REM; break;
    case BZLA_FP_RTI_NODE: kind = BITWUZLA_KIND_FP_RTI; break;
    case BZLA_FP_TO_SBV_NODE: kind = BITWUZLA_KIND_FP_TO_SBV; break;
    case BZLA_FP_TO_UBV_NODE: kind = BITWUZLA_KIND_FP_TO_UBV; break;
    case BZLA_FP_TO_FP_FP_NODE: kind = BITWUZLA_KIND_FP_TO_FP_FROM_FP; break;
    case BZLA_FP_TO_FP_SBV_NODE: kind = BITWUZLA_KIND_FP_TO_FP_FROM_SBV; break;
    case BZLA_FP_TO_FP_UBV_NODE: kind = BITWUZLA_KIND_FP_TO_FP_FROM_UBV; break;

    case BZLA_APPLY_NODE:
      if (bzla_node_is_array(bzla_term->e[0]))
      {
        kind = BITWUZLA_KIND_ARRAY_SELECT;
      }
      else
      {
        kind = BITWUZLA_KIND_APPLY;
      }
      break;

    case BZLA_FORALL_NODE: kind = BITWUZLA_KIND_FORALL; break;
    case BZLA_EXISTS_NODE: kind = BITWUZLA_KIND_EXISTS; break;
    case BZLA_LAMBDA_NODE:
      if (bzla_node_is_const_array(bzla_term))
      {
        kind = BITWUZLA_KIND_CONST_ARRAY;
      }
      else
      {
        kind = BITWUZLA_KIND_LAMBDA;
      }
      break;

    case BZLA_COND_NODE: kind = BITWUZLA_KIND_ITE; break;
    case BZLA_FP_ADD_NODE: kind = BITWUZLA_KIND_FP_ADD; break;
    case BZLA_FP_MUL_NODE: kind = BITWUZLA_KIND_FP_MUL; break;
    case BZLA_FP_DIV_NODE: kind = BITWUZLA_KIND_FP_DIV; break;
    case BZLA_UPDATE_NODE: kind = BITWUZLA_KIND_ARRAY_STORE; break;

    default:
      if (bzla_node_is_var(bzla_term) || bzla_node_is_uf(bzla_term))
      {
        kind = BITWUZLA_KIND_CONST;
        break;
      }
      if (bzla_node_is_bv_const(bzla_term) || bzla_node_is_fp_const(bzla_term)
          || bzla_node_is_rm_const(bzla_term))
      {
        kind = BITWUZLA_KIND_VAL;
        break;
      }
      if (bzla_node_is_param(bzla_term))
      {
        kind = BITWUZLA_KIND_VAR;
        break;
      }
      BZLA_ABORT(k != BZLA_FP_FMA_NODE,
                 "unhandled internal kind: %s",
                 g_bzla_op2str[k]);
      kind = BITWUZLA_KIND_FP_FMA;
  }

  return kind;
}

const BitwuzlaTerm **
bitwuzla_term_get_children(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *n;
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  Bzla *bzla          = bzla_node_get_bzla(bzla_term);
  bzla_term           = bzla_simplify_exp(bzla, bzla_term);
  Bitwuzla *bitwuzla  = BZLA_EXPORT_BITWUZLA(bzla);

  BZLA_RESET_STACK(bitwuzla->d_term_children);

  if (bzla_node_is_inverted(bzla_term))
  {
    /* Inverted BV values are still handled as values. */
    if (!bzla_node_is_bv_const(bzla_term))
    {
      n = bzla_node_copy(bzla, bzla_node_real_addr(bzla_term));
      BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
      bzla_node_inc_ext_ref_counter(bzla, n);
    }
  }
  else if (bzla_node_is_apply(bzla_term) || bzla_node_is_update(bzla_term))
  {
    n = bzla_node_copy(bzla, bzla_term->e[0]);
    BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
    bzla_node_inc_ext_ref_counter(bzla, n);

    /* collect all arguments */
    BzlaArgsIterator it;
    bzla_iter_args_init(&it, bzla_term->e[1]);
    while (bzla_iter_args_has_next(&it))
    {
      n = bzla_node_copy(bzla, bzla_iter_args_next(&it));
      BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
      bzla_node_inc_ext_ref_counter(bzla, n);
    }

    if (bzla_node_is_update(bzla_term))
    {
      n = bzla_node_copy(bzla, bzla_term->e[2]);
      BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
      bzla_node_inc_ext_ref_counter(bzla, n);
    }
  }
  else if (bzla_node_is_const_array(bzla_term))
  {
    n = bzla_node_copy(bzla, bzla_node_binder_get_body(bzla_term));
    BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
    bzla_node_inc_ext_ref_counter(bzla, n);
  }
  else if (bzla_node_is_binder(bzla_term))
  {
    /* collect all variables */
    BzlaNode *binder;
    BzlaNodeIterator it;
    bzla_iter_binder_init(&it, bzla_term);
    while (bzla_iter_binder_has_next(&it))
    {
      binder = bzla_iter_binder_next(&it);
      n      = bzla_node_copy(bzla, binder->e[0]);
      BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
      bzla_node_inc_ext_ref_counter(bzla, n);
    }
    n = bzla_node_copy(bzla, bzla_node_binder_get_body(bzla_term));
    BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
    bzla_node_inc_ext_ref_counter(bzla, n);
  }
  else
  {
    for (size_t i = 0; i < bzla_term->arity; ++i)
    {
      n = bzla_node_copy(bzla, bzla_term->e[i]);
      BZLA_PUSH_STACK(bitwuzla->d_term_children, BZLA_EXPORT_BITWUZLA_TERM(n));
      bzla_node_inc_ext_ref_counter(bzla, n);
    }
  }

  *size = BZLA_COUNT_STACK(bitwuzla->d_term_children);
  if (*size == 0)
  {
    return NULL;
  }
  return bitwuzla->d_term_children.start;
}

uint32_t *
bitwuzla_term_get_indices(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = bzla_node_real_addr(BZLA_IMPORT_BITWUZLA_TERM(term));
  Bzla *bzla          = bzla_node_get_bzla(bzla_term);
  Bitwuzla *bitwuzla  = BZLA_EXPORT_BITWUZLA(bzla);
  BZLA_ABORT(!bzla_node_is_indexed(bzla_term),
             "cannot get indices of non-indexed term");

  BzlaSortId sort = bzla_node_get_sort_id(bzla_term);
  switch (bzla_node_get_kind(bzla_term))
  {
    case BZLA_FP_TO_FP_FP_NODE:
    case BZLA_FP_TO_FP_BV_NODE:
    case BZLA_FP_TO_FP_SBV_NODE:
    case BZLA_FP_TO_FP_UBV_NODE:
      bitwuzla->d_term_indices[0] = bzla_sort_fp_get_exp_width(bzla, sort);
      bitwuzla->d_term_indices[1] = bzla_sort_fp_get_sig_width(bzla, sort);
      *size                       = 2;
      break;

    case BZLA_FP_TO_SBV_NODE:
    case BZLA_FP_TO_UBV_NODE:
      bitwuzla->d_term_indices[0] = bzla_sort_bv_get_width(bzla, sort);
      *size                       = 1;
      break;

    default:
      BZLA_ABORT(bzla_node_get_kind(bzla_term) != BZLA_BV_SLICE_NODE,
                 "unhandled internal kind.");
      bitwuzla->d_term_indices[0] = bzla_node_bv_slice_get_upper(bzla_term);
      bitwuzla->d_term_indices[1] = bzla_node_bv_slice_get_lower(bzla_term);
      *size                       = 2;
  }

  return bitwuzla->d_term_indices;
}

bool
bitwuzla_term_is_indexed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  return bzla_node_is_regular(bzla_term) && bzla_node_is_indexed(bzla_term);
}

Bitwuzla *
bitwuzla_term_get_bitwuzla(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *res = bzla_node_get_bzla(bzla_term);
  return BZLA_EXPORT_BITWUZLA(res);
}

const BitwuzlaSort *
bitwuzla_term_get_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  const BitwuzlaSort *sort;
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);

  BzlaSortId bzla_sort = bzla_node_get_sort_id(bzla_term);
  if (bzla_node_is_array(bzla_term))
  {
    BzlaSortId array_sort =
        bzla_sort_array(bzla,
                        bzla_sort_array_get_index(bzla, bzla_sort),
                        bzla_sort_array_get_element(bzla, bzla_sort));

    sort = BZLA_EXPORT_BITWUZLA_SORT(
        BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)), array_sort);

    bzla_sort_release(bzla, array_sort);
  }
  else
  {
    sort = BZLA_EXPORT_BITWUZLA_SORT(
        BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)), bzla_sort);
  }

  return sort;
}

const BitwuzlaSort *
bitwuzla_term_array_get_index_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_array_get_index(bzla_node_get_bzla(bzla_term),
                                bzla_node_get_sort_id(bzla_term)));
}

const BitwuzlaSort *
bitwuzla_term_array_get_element_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_array_get_element(bzla_node_get_bzla(bzla_term),
                                  bzla_node_get_sort_id(bzla_term)));
}

const BitwuzlaSort **
bitwuzla_term_fun_get_domain_sorts(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(size);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  Bzla *bzla         = bzla_node_get_bzla(bzla_term);
  Bitwuzla *bitwuzla = BZLA_EXPORT_BITWUZLA(bzla);
  uint32_t arity     = bzla_node_fun_get_arity(bzla, bzla_term);
  BZLA_RESET_STACK(bitwuzla->d_fun_domain_sorts);
  BzlaTupleSort *tuple_sort =
      &bzla_sort_get_by_id(
           bzla,
           bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(bzla_term)))
           ->tuple;
  assert(arity == tuple_sort->num_elements);
  for (uint32_t i = 0; i < arity; i++)
  {
    BzlaSortId id = tuple_sort->elements[i]->id;
    BZLA_PUSH_STACK(bitwuzla->d_fun_domain_sorts,
                    BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, id));
    bzla_sort_copy(bzla, id);
    inc_ext_refs_sort(bzla, id);
  }
  *size = BZLA_COUNT_STACK(bitwuzla->d_fun_domain_sorts);
  return bitwuzla->d_fun_domain_sorts.start;
}

const BitwuzlaSort *
bitwuzla_term_fun_get_codomain_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_fun_get_codomain(bzla_node_get_bzla(bzla_term),
                                 bzla_node_get_sort_id(bzla_term)));
}

uint32_t
bitwuzla_term_bv_get_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_BV(bzla, bzla_term);
  return bzla_node_bv_get_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_exp_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_exp_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_sig_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_sig_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fun_get_arity(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  return bzla_node_fun_get_arity(bzla, bzla_term);
}

const char *
bitwuzla_term_get_symbol(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_get_symbol(bzla, bzla_term);
}

void
bitwuzla_term_set_symbol(const BitwuzlaTerm *term, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(symbol);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);

  bzla_node_set_symbol(bzla, bzla_term, symbol);
}

bool
bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
                            const BitwuzlaTerm *term1)
{
  BZLA_CHECK_ARG_NOT_NULL(term0);
  BZLA_CHECK_ARG_NOT_NULL(term1);

  BzlaNode *bzla_term0 = BZLA_IMPORT_BITWUZLA_TERM(term0);
  BzlaNode *bzla_term1 = BZLA_IMPORT_BITWUZLA_TERM(term1);
  BZLA_ABORT(bzla_node_get_bzla(bzla_term0) != bzla_node_get_bzla(bzla_term1),
             "given terms are not associated with the same solver instance");
  assert(bzla_node_get_ext_refs(bzla_term0));
  assert(bzla_node_get_ext_refs(bzla_term0));
  return bzla_node_get_sort_id(bzla_term0) == bzla_node_get_sort_id(bzla_term1);
}

bool
bitwuzla_term_is_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_const(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  bzla_term = bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term);
  return !bzla_node_is_inverted(bzla_term)
         && (bzla_node_is_var(bzla_term) || bzla_node_is_uf(bzla_term));
}

bool
bitwuzla_term_is_fun(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  bzla_term = bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term);
  return bzla_node_is_fun(bzla_term) && !bzla_node_is_array(bzla_term);
}

bool
bitwuzla_term_is_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  bzla_term = bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term);
  return !bzla_node_is_inverted(bzla_term) && bzla_node_is_param(bzla_term);
}

bool
bitwuzla_term_is_bound_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_VAR(bzla_term);
  return bzla_node_param_is_bound(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  bzla_term = bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term);

  return bzla_node_is_bv_const(bzla_term) || bzla_node_is_fp_const(bzla_term)
         || bzla_node_is_rm_const(bzla_term);
}

bool
bitwuzla_term_is_bv_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_fp_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_rm_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bv(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_bv(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_fp(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_fp(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_rm(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_rm(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_zero(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_one(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_ones(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_min_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_max_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_nan(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_rm_value_rna(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const_rna(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_rm_value_rne(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const_rne(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_rm_value_rtn(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const_rtn(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_rm_value_rtp(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const_rtp(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_rm_value_rtz(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const_rtz(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_const_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_const_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

void
bitwuzla_term_dump(const BitwuzlaTerm *term, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  Bzla *bzla          = bzla_node_get_bzla(bzla_term);
  if (strcmp(format, "smt2") == 0)
  {
    bzla_dumpsmt_dump_node(bzla, file, bzla_simplify_exp(bzla, bzla_term), 0);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_dumpbtor_dump_node(bzla, file, bzla_simplify_exp(bzla, bzla_term));
  }
  else
  {
    BZLA_ABORT(
        true, "unknown format '%s', expected one of 'smt2' or 'bzla'", format);
  }
}

/* main only ---------------------------------------------------------------- */

Bzla *
bitwuzla_get_bzla(Bitwuzla *bitwuzla)
{
  return bitwuzla->d_bzla;
}

/* parser only -------------------------------------------------------------- */

BzlaMsg *
bitwuzla_get_bzla_msg(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  return bzla->msg;
}

/* smt2 parser only --------------------------------------------------------- */

void
bitwuzla_term_var_mark_bool(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);

  BzlaPtrHashBucket *b = bzla_hashptr_table_get(bzla->inputs, bzla_term);
  assert(b);
  b->data.flag = true;
}

void
bitwuzla_term_print_value_smt2(const BitwuzlaTerm *term,
                               char *symbol,
                               FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "print model value");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");
  bzla_print_value_smt2(bzla, bzla_term, symbol, file);
}

BitwuzlaOption
bitwuzla_get_option_from_string(Bitwuzla *bitwuzla, const char *str)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(str);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);

  if (!bzla_hashptr_table_get(bzla->str2opt, str))
  {
    return BITWUZLA_OPT_NUM_OPTS;
  }
  return BZLA_EXPORT_BITWUZLA_OPTION(
      bzla_hashptr_table_get(bzla->str2opt, str)->data.as_int);
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_set_bzla_id(Bitwuzla *bitwuzla, const BitwuzlaTerm *term, int32_t id)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BZLA_ABORT(
      !bzla_node_is_bv_var(bzla_term) && !bzla_node_is_uf_array(bzla_term),
      "expected bit-vector/array variable or UF");
  bzla_node_set_bzla_id(bzla, bzla_term, id);
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_add_output(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BZLA_PUSH_STACK(bzla->outputs, bzla_node_copy(bzla, bzla_term));
}
