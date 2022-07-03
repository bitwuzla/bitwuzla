/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAOPTS_H_INCLUDED
#define BZLAOPTS_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "bzlatypes.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

// clang-format off
enum BzlaOption
{
  /* General options */
  BZLA_OPT_AUTO_CLEANUP,
  BZLA_OPT_ENGINE,
  BZLA_OPT_EXIT_CODES,
  BZLA_OPT_INCREMENTAL,
  BZLA_OPT_INPUT_FORMAT,
  BZLA_OPT_LOGLEVEL,
  BZLA_OPT_OUTPUT_FORMAT,
  BZLA_OPT_OUTPUT_NUMBER_FORMAT,
  BZLA_OPT_PRETTY_PRINT,
  BZLA_OPT_PRINT_DIMACS,
  BZLA_OPT_PRODUCE_MODELS,
  BZLA_OPT_PRODUCE_UNSAT_CORES,
  BZLA_OPT_SAT_ENGINE,
  BZLA_OPT_SEED,
  BZLA_OPT_VERBOSITY,

  /* Rewriting/preprocessing (expert) */
  BZLA_OPT_PP_ACKERMANN,
  BZLA_OPT_PP_BETA_REDUCE,
  BZLA_OPT_PP_ELIMINATE_EXTRACTS,
  BZLA_OPT_PP_ELIMINATE_ITES,
  BZLA_OPT_PP_EXTRACT_LAMBDAS,
  BZLA_OPT_PP_MERGE_LAMBDAS,
  BZLA_OPT_PP_NONDESTR_SUBST,
  BZLA_OPT_PP_NORMALIZE_ADD,
  BZLA_OPT_PP_SKELETON_PREPROC,
  BZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION,
  BZLA_OPT_PP_VAR_SUBST,
  BZLA_OPT_RW_EXTRACT_ARITH,
  BZLA_OPT_RW_LEVEL,
  BZLA_OPT_RW_NORMALIZE,
  BZLA_OPT_RW_NORMALIZE_ADD,
  BZLA_OPT_RW_SIMPLIFY_CONSTRAINTS,
  BZLA_OPT_RW_SLT,
  BZLA_OPT_RW_SORT_AIG,
  BZLA_OPT_RW_SORT_AIGVEC,
  BZLA_OPT_RW_SORT_EXP,

  /* Fun engine (expert) */

  BZLA_OPT_FUN_PREPROP,
  BZLA_OPT_FUN_PRESLS,
  BZLA_OPT_FUN_DUAL_PROP,
  BZLA_OPT_FUN_DUAL_PROP_QSORT,
  BZLA_OPT_FUN_JUST,
  BZLA_OPT_FUN_JUST_HEURISTIC,
  BZLA_OPT_FUN_LAZY_SYNTHESIZE,
  BZLA_OPT_FUN_EAGER_LEMMAS,
  BZLA_OPT_FUN_STORE_LAMBDAS,

  /* SLS engine (expert) */

  BZLA_OPT_SLS_JUST,
  BZLA_OPT_SLS_MOVE_GW,
  BZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
  BZLA_OPT_SLS_MOVE_PROP,
  BZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
  BZLA_OPT_SLS_MOVE_PROP_NPROPS,
  BZLA_OPT_SLS_MOVE_PROP_NSLSS,
  BZLA_OPT_SLS_MOVE_RAND_ALL,
  BZLA_OPT_SLS_MOVE_RAND_RANGE,
  BZLA_OPT_SLS_MOVE_RAND_WALK,
  BZLA_OPT_SLS_MOVE_RANGE,
  BZLA_OPT_SLS_MOVE_SEGMENT,
  BZLA_OPT_SLS_NFLIPS,
  BZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
  BZLA_OPT_SLS_STRATEGY,
  BZLA_OPT_SLS_USE_BANDIT,
  BZLA_OPT_SLS_USE_RESTARTS,

  /* Prop engine (expert) */

  BZLA_OPT_PROP_ASHR,
  BZLA_OPT_PROP_CONST_BITS,
  BZLA_OPT_PROP_CONST_DOMAINS,
#if 0
  BZLA_OPT_PROP_DOMAINS,
#endif
  BZLA_OPT_PROP_ENTAILED,
  BZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
  BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
  BZLA_OPT_PROP_INFER_INEQ_BOUNDS,
  BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
  BZLA_OPT_PROP_NPROPS,
  BZLA_OPT_PROP_NUPDATES,
  BZLA_OPT_PROP_PATH_SEL,
  BZLA_OPT_PROP_PROB_AND_FLIP,
  BZLA_OPT_PROP_PROB_EQ_FLIP,
  BZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
  BZLA_OPT_PROP_PROB_FLIP_COND,
  BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
  BZLA_OPT_PROP_PROB_RANDOM_INPUT,
  BZLA_OPT_PROP_PROB_SLICE_FLIP,
  BZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
  BZLA_OPT_PROP_PROB_USE_INV_VALUE,
  BZLA_OPT_PROP_SEXT,
  BZLA_OPT_PROP_SKIP_NO_PROGRESS,
  BZLA_OPT_PROP_USE_BANDIT,
  BZLA_OPT_PROP_USE_INV_LT_CONCAT,
  BZLA_OPT_PROP_USE_RESTARTS,
  BZLA_OPT_PROP_XOR,

  /* Aigprop engine (expert) */

  BZLA_OPT_AIGPROP_NPROPS,
  BZLA_OPT_AIGPROP_USE_BANDIT,
  BZLA_OPT_AIGPROP_USE_RESTARTS,

  /* Quantifier engine (expert) */
  BZLA_OPT_QUANT_SYNTH_SK,
  BZLA_OPT_QUANT_SYNTH_QI,
  BZLA_OPT_QUANT_SKOLEM_UF,
  BZLA_OPT_QUANT_EAGER_SKOLEM,
  BZLA_OPT_QUANT_MBQI,
  BZLA_OPT_QUANT_MODE,

  /* Other expert options */
  BZLA_OPT_AUTO_CLEANUP_INTERNAL,
  BZLA_OPT_CHECK_MODEL,
  BZLA_OPT_CHECK_UNCONSTRAINED,
  BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS,
  BZLA_OPT_DECLSORT_BV_WIDTH,
  BZLA_OPT_LS_SHARE_SAT,
  BZLA_OPT_PARSE_INTERACTIVE,
  BZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
  BZLA_OPT_SAT_ENGINE_LGL_FORK,
  BZLA_OPT_SAT_ENGINE_N_THREADS,
  BZLA_OPT_SMT_COMP_MODE,

  /* this MUST be the last entry! */
  BZLA_OPT_NUM_OPTS,
};
// clang-format on

typedef enum BzlaOption BzlaOption;

/* --------------------------------------------------------------------- */
/* Bitwuzla option values                                               */
/* --------------------------------------------------------------------- */

/* Note: enums with NONE values should start with NONE = 0. If there is no NONE
 * value the enum range should start with 1. This allows us to determine if an
 * option is set by checking if it is > 0. */

enum BzlaOptSatEngine
{
  BZLA_SAT_ENGINE_LINGELING,
  BZLA_SAT_ENGINE_PICOSAT,
  BZLA_SAT_ENGINE_KISSAT,
  BZLA_SAT_ENGINE_GIMSATUL,
  BZLA_SAT_ENGINE_MINISAT,
  BZLA_SAT_ENGINE_CADICAL,
  BZLA_SAT_ENGINE_CMS,
};
typedef enum BzlaOptSatEngine BzlaOptSatEngine;

enum BzlaOptEngine
{
  BZLA_ENGINE_FUN = 1,
  BZLA_ENGINE_SLS,
  BZLA_ENGINE_PROP,
  BZLA_ENGINE_AIGPROP,
  BZLA_ENGINE_QUANT,
};
typedef enum BzlaOptEngine BzlaOptEngine;

enum BzlaOptInputFormat
{
  BZLA_INPUT_FORMAT_NONE,
  BZLA_INPUT_FORMAT_BTOR,
  BZLA_INPUT_FORMAT_BTOR2,
  BZLA_INPUT_FORMAT_SMT2,
};
typedef enum BzlaOptInputFormat BzlaOptInputFormat;

enum BzlaOptOutputBase
{
  BZLA_OUTPUT_BASE_BIN = 1,
  BZLA_OUTPUT_BASE_HEX,
  BZLA_OUTPUT_BASE_DEC,
};
typedef enum BzlaOptOutputBase BzlaOptOutputBase;

enum BzlaOptOutputFormat
{
  BZLA_OUTPUT_FORMAT_NONE,
  BZLA_OUTPUT_FORMAT_BTOR = 1,
  //  BZLA_OUTPUT_FORMAT_BTOR2,
  BZLA_OUTPUT_FORMAT_SMT2,
  BZLA_OUTPUT_FORMAT_AIGER_ASCII,
  BZLA_OUTPUT_FORMAT_AIGER_BINARY,
};
typedef enum BzlaOptOutputFormat BzlaOptOutputFormat;

enum BzlaOptDPQsort
{
  BZLA_DP_QSORT_JUST = 1,
  BZLA_DP_QSORT_ASC,
  BZLA_DP_QSORT_DESC,
};
typedef enum BzlaOptDPQsort BzlaOptDPQsort;

enum BzlaOptJustHeur
{
  BZLA_JUST_HEUR_BRANCH_LEFT = 1,
  BZLA_JUST_HEUR_BRANCH_MIN_APP,
  BZLA_JUST_HEUR_BRANCH_MIN_DEP,
};
typedef enum BzlaOptJustHeur BzlaOptJustHeur;

enum BzlaOptSLSStrat
{
  BZLA_SLS_STRAT_BEST_MOVE = 1,
  BZLA_SLS_STRAT_RAND_WALK,
  BZLA_SLS_STRAT_FIRST_BEST_MOVE,
  BZLA_SLS_STRAT_BEST_SAME_MOVE,
  BZLA_SLS_STRAT_ALWAYS_PROP,
};
typedef enum BzlaOptSLSStrat BzlaOptSLSStrat;

enum BzlaOptPropPathSel
{
  BZLA_PROP_PATH_SEL_ESSENTIAL = 1,
  BZLA_PROP_PATH_SEL_RANDOM,
};
typedef enum BzlaOptPropPathSel BzlaOptPropPathSel;

enum BzlaOptPropEntailed
{
  BZLA_PROP_ENTAILED_MIN,
  BZLA_PROP_ENTAILED_OFF,
  BZLA_PROP_ENTAILED_ALL,
  BZLA_PROP_ENTAILED_FIRST,
  BZLA_PROP_ENTAILED_LAST,
  BZLA_PROP_ENTAILED_MAX,
};
typedef enum BzlaOptPropEntailed BzlaOptPropEntailed;

enum BzlaOptQuantSynth
{
  BZLA_QUANT_SYNTH_NONE,
  BZLA_QUANT_SYNTH_EL,
  BZLA_QUANT_SYNTH_ELMC,
  BZLA_QUANT_SYNTH_EL_ELMC,
  BZLA_QUANT_SYNTH_ELMR,
};
typedef enum BzlaOptQuantSynth BzlaOptQuantSynt;

/** Different modes for handling counterexample literals. */
enum BzlaOptQuantMode
{
  /* Eagerly assume counterexample literals when checking ground formulas. */
  BZLA_QUANT_MODE_EAGER,
  /* Do not assume counterexample literals when checking ground formulas. */
  BZLA_QUANT_MODE_LAZY,
  /**
   * Like BZLA_QUANT_MODE_EAGER, but use model of initial ground check if check
   * was satisfiable with all counterexample literals assumed. */
  BZLA_QUANT_MODE_EAGER_REUSE,
  /**
   * Like BZLA_QUANT_MODE_EAGER, but do additional satisfiability check after
   * counterexample literals were assumed and satisfiable. */
  BZLA_QUANT_MODE_EAGER_CHECK,
  /**
   * Combines BZLA_QUANT_MODE_EAGER_CHECK + BZLA_QUANT_MODE_EAGER +
   * BZLA_QUANT_MODE_LAZY in a sequential portfolio (in case one of the modes
   * returns unknown).
   */
  BZLA_QUANT_MODE_PORTFOLIO,
};
typedef enum BzlaOptQuantMode BzlaOptQuantMode;

#define BZLA_QUANT_MODE_DFLT BZLA_QUANT_MODE_PORTFOLIO
#define BZLA_QUANT_MODE_MIN BZLA_QUANT_MODE_EAGER
#define BZLA_QUANT_MODE_MAX BZLA_QUANT_MODE_PORTFOLIO

enum BzlaOptFunEagerLemmas
{
  BZLA_FUN_EAGER_LEMMAS_NONE,
  BZLA_FUN_EAGER_LEMMAS_CONF,
  BZLA_FUN_EAGER_LEMMAS_ALL,
};
typedef enum BzlaOptFunEagerLemmas BzlaOptFunEagerLemmas;

enum BzlaOptIncrementalSMT1
{
  BZLA_INCREMENTAL_SMT1_BASIC = 1,
  BZLA_INCREMENTAL_SMT1_CONTINUE,
};
typedef enum BzlaOptIncrementalSMT1 BzlaOptIncrementalSMT1;

enum BzlaOptBetaReduceMode
{
  BZLA_BETA_REDUCE_NONE,
  BZLA_BETA_REDUCE_FUN,
  BZLA_BETA_REDUCE_ALL,
};
typedef enum BzlaOptBetaReduceMode BzlaOptBetaReduceMode;

/* --------------------------------------------------------------------- */

struct BzlaOpt
{
  bool expert;               /* expert option? */
  bool isflag;               /* flag? */
  const char *shrt;          /* short option identifier (may be 0) */
  const char *lng;           /* long option identifier */
  const char *desc;          /* description */
  uint32_t val;              /* value */
  uint32_t dflt;             /* default value */
  uint32_t min;              /* min value */
  uint32_t max;              /* max value */
  char *valstr;              /* optional option string value */
  BzlaPtrHashTable *options; /* maps option CL value strings to enum values */
};
typedef struct BzlaOpt BzlaOpt;

/*------------------------------------------------------------------------*/

/**
 * Represents the data required to print help messages for options that
 * expect an enum value rather than an (u)int value. This is mainly needed
 * for invoking the solver via the command line (with '--<opt>=help').
 */
struct BzlaOptHelp
{
  int32_t val;     /* the enum value */
  const char *msg; /* the help message */
};
typedef struct BzlaOptHelp BzlaOptHelp;

/*------------------------------------------------------------------------*/

/* enum BzlaOption is in bzlatypes.h */

#define BZLA_OPT_NUM_OPTS_STR "end_of_options_marker"
#define BZLA_OPT_INVALID_OPT_STR "invalid_option"

/*------------------------------------------------------------------------*/

#define BZLA_VERBOSITY_MAX 4

#define BZLA_PROB_100 1000
#define BZLA_PROB_50 500

/* enums for option values are defined in bzlatypes.h */

#define BZLA_SAT_ENGINE_MIN BZLA_SAT_ENGINE_LINGELING
#define BZLA_SAT_ENGINE_MAX BZLA_SAT_ENGINE_CMS
#ifdef BZLA_USE_CADICAL
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_CADICAL
#elif BZLA_USE_LINGELING
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_LINGELING
#elif BZLA_USE_PICOSAT
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_PICOSAT
#elif BZLA_USE_KISSAT
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_KISSAT
#elif BZLA_USE_MINISAT
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_MINISAT
#elif BZLA_USE_CMS
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_CMS
#elif BZLA_USE_GIMSATUL
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_GIMSATUL
#endif
extern const char *const g_bzla_se_name[BZLA_SAT_ENGINE_MAX + 1];

#define BZLA_ENGINE_MIN BZLA_ENGINE_FUN
#define BZLA_ENGINE_MAX BZLA_ENGINE_AIGPROP
#define BZLA_ENGINE_DFLT BZLA_ENGINE_FUN

#define BZLA_INPUT_FORMAT_MIN BZLA_INPUT_FORMAT_NONE
#define BZLA_INPUT_FORMAT_MAX BZLA_INPUT_FORMAT_SMT2
#define BZLA_INPUT_FORMAT_DFLT BZLA_INPUT_FORMAT_NONE

#define BZLA_OUTPUT_BASE_MIN BZLA_OUTPUT_BASE_BIN
#define BZLA_OUTPUT_BASE_MAX BZLA_OUTPUT_BASE_DEC
#define BZLA_OUTPUT_BASE_DFLT BZLA_OUTPUT_BASE_BIN

#define BZLA_OUTPUT_FORMAT_MIN BZLA_OUTPUT_FORMAT_NONE
#define BZLA_OUTPUT_FORMAT_MAX BZLA_OUTPUT_FORMAT_AIGER_BINARY
#define BZLA_OUTPUT_FORMAT_DFLT BZLA_OUTPUT_FORMAT_NONE

#define BZLA_DP_QSORT_MIN BZLA_DP_QSORT_JUST
#define BZLA_DP_QSORT_MAX BZLA_DP_QSORT_DESC
#define BZLA_DP_QSORT_DFLT BZLA_DP_QSORT_JUST

#define BZLA_JUST_HEUR_MIN BZLA_JUST_HEUR_BRANCH_LEFT
#define BZLA_JUST_HEUR_MAX BZLA_JUST_HEUR_BRANCH_MIN_DEP
#define BZLA_JUST_HEUR_DFLT BZLA_JUST_HEUR_BRANCH_MIN_APP

#define BZLA_SLS_STRAT_MIN BZLA_SLS_STRAT_BEST_MOVE
#define BZLA_SLS_STRAT_MAX BZLA_SLS_STRAT_ALWAYS_PROP
#define BZLA_SLS_STRAT_DFLT BZLA_SLS_STRAT_BEST_MOVE

#define BZLA_PROP_PATH_SEL_MIN BZLA_PROP_PATH_SEL_ESSENTIAL
#define BZLA_PROP_PATH_SEL_MAX BZLA_PROP_PATH_SEL_RANDOM
#define BZLA_PROP_PATH_SEL_DFLT BZLA_PROP_PATH_SEL_ESSENTIAL

#define BZLA_PROP_ENTAILED_DFLT BZLA_PROP_ENTAILED_OFF

#define BZLA_QUANT_SYNTH_MIN BZLA_QUANT_SYNTH_NONE
#define BZLA_QUANT_SYNTH_MAX BZLA_QUANT_SYNTH_ELMR
#define BZLA_QUANT_SYNTH_DFLT BZLA_QUANT_SYNTH_ELMR

#define BZLA_FUN_EAGER_LEMMAS_MIN BZLA_FUN_EAGER_LEMMAS_NONE
#define BZLA_FUN_EAGER_LEMMAS_MAX BZLA_FUN_EAGER_LEMMAS_ALL
#define BZLA_FUN_EAGER_LEMMAS_DFLT BZLA_FUN_EAGER_LEMMAS_CONF

#define BZLA_BETA_REDUCE_MIN BZLA_BETA_REDUCE_NONE
#define BZLA_BETA_REDUCE_MAX BZLA_BETA_REDUCE_ALL
#define BZLA_BETA_REDUCE_DFLT BZLA_BETA_REDUCE_NONE

/*------------------------------------------------------------------------*/

void bzla_opt_init_opts(Bzla *bzla);
void bzla_opt_clone_opts(Bzla *bzla, Bzla *clone);
void bzla_opt_delete_opts(Bzla *bzla);

bool bzla_opt_is_valid(const Bzla *bzla, const BzlaOption opt);

uint32_t bzla_opt_get(const Bzla *bzla, const BzlaOption opt);
uint32_t bzla_opt_get_min(const Bzla *bzla, const BzlaOption opt);
uint32_t bzla_opt_get_max(const Bzla *bzla, const BzlaOption opt);
uint32_t bzla_opt_get_dflt(const Bzla *bzla, const BzlaOption opt);
const char *bzla_opt_get_lng(const Bzla *bzla, const BzlaOption opt);
const char *bzla_opt_get_shrt(const Bzla *bzla, const BzlaOption opt);
const char *bzla_opt_get_desc(const Bzla *bzla, const BzlaOption opt);
const char *bzla_opt_get_valstr(const Bzla *bzla, const BzlaOption opt);

void bzla_opt_set(Bzla *bzla, const BzlaOption opt, uint32_t val);
void bzla_opt_set_str(Bzla *bzla, const BzlaOption opt, const char *str);

bool bzla_opt_is_enum_option(const Bzla *bzla, const BzlaOption opt);
bool bzla_opt_is_enum_option_value(const Bzla *bzla,
                                   const BzlaOption opt,
                                   const char *value);
uint32_t bzla_opt_get_enum_value(Bzla *bzla,
                                 const BzlaOption opt,
                                 const char *value);
/**
 * Get the string representation of the current value of an option that
 * expects an enum value as configuration value.
 */
const char* bzla_opt_get_str_value(Bzla *bzla, const BzlaOption opt);

BzlaOption bzla_opt_first(Bzla *bzla);
BzlaOption bzla_opt_next(Bzla *bzla, BzlaOption cur);

#ifndef NBZLALOG
void bzla_opt_log_opts(Bzla *bzla);
#endif
#endif
