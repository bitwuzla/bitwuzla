/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlamain.h"

#include <assert.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "api/c/bitwuzla.h"
#include "bzlaconfig.h"
#include "bzlacore.h"
#include "bzlaexit.h"
#include "bzlaopt.h"
#include "bzlaparse.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlaoptparse.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

typedef struct BitwuzlaMainApp BitwuzlaMainApp;
static BitwuzlaMainApp *g_app;

static double g_start_time_real;
static uint32_t g_verbosity;
static uint32_t g_set_alarm;

#ifdef BZLA_HAVE_SIGNALS
static bool g_caught_sig;

static void (*sig_int_handler)(int32_t);
static void (*sig_segv_handler)(int32_t);
static void (*sig_abrt_handler)(int32_t);
static void (*sig_term_handler)(int32_t);
static void (*sig_bus_handler)(int32_t);

static void (*sig_alrm_handler)(int32_t);
#endif

/*------------------------------------------------------------------------*/

BZLA_DECLARE_STACK(BzlaOption, BzlaOption);

/*------------------------------------------------------------------------*/

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

/*------------------------------------------------------------------------*/

enum BitwuzlaMainOption
{
  BZLAMAIN_OPT_HELP,
  BZLAMAIN_OPT_HELP_EXPERT,
  BZLAMAIN_OPT_COPYRIGHT,
  BZLAMAIN_OPT_VERSION,
  BZLAMAIN_OPT_TIME,
  BZLAMAIN_OPT_OUTPUT,
  BZLAMAIN_OPT_LGL_NOFORK,
  BZLAMAIN_OPT_HEX,
  BZLAMAIN_OPT_DEC,
  BZLAMAIN_OPT_BIN,
  BZLAMAIN_OPT_BTOR,
  BZLAMAIN_OPT_BTOR2,
  BZLAMAIN_OPT_SMT2,
  BZLAMAIN_OPT_DUMP_BTOR,
#if 0
  BZLAMAIN_OPT_DUMP_BTOR2,
#endif
  BZLAMAIN_OPT_DUMP_SMT,
  BZLAMAIN_OPT_DUMP_AAG,
  BZLAMAIN_OPT_DUMP_AIG,
  BZLAMAIN_OPT_DUMP_AIGER_MERGE,
  /* this MUST be the last entry! */
  BZLAMAIN_OPT_NUM_OPTS,
};
typedef enum BitwuzlaMainOption BitwuzlaMainOption;

typedef struct BzlaMainOpt
{
  bool general;        /* general option? */
  const char *shrt;    /* short option identifier (may be 0) */
  const char *lng;     /* long option identifier */
  const char *desc;    /* description */
  uint32_t val;        /* value */
  uint32_t dflt;       /* default value */
  uint32_t min;        /* min value */
  uint32_t max;        /* max value */
  bool candisable;     /* can be disabled via '-(-)no-XX'? */
  bool isflag;         /* is option flag? */
  BzlaArgExpected arg; /* expects argument? */
} BzlaMainOpt;

/*------------------------------------------------------------------------*/

struct BitwuzlaMainApp
{
  Bitwuzla *bitwuzla;
  Bzla *bzla;
  BzlaMemMgr *mm;
  BzlaMainOpt *options;
  bool done;
  int32_t err;
  char *infile_name;
  FILE *infile;
  int32_t close_infile;
  FILE *outfile;
  char *outfile_name;
  bool close_outfile;
};

/*------------------------------------------------------------------------*/

Bzla *bitwuzla_get_bzla(Bitwuzla *bitwuzla);

/*------------------------------------------------------------------------*/

static void
bzlamain_init_opt(BitwuzlaMainApp *app,
                  BitwuzlaMainOption opt,
                  bool general,
                  bool isflag,
                  char *lng,
                  char *shrt,
                  uint32_t val,
                  uint32_t min,
                  uint32_t max,
                  bool candisable,
                  BzlaArgExpected arg,
                  char *desc)
{
  assert(app);
  assert(lng);
  assert(desc);
  assert(max <= UINT32_MAX);
  assert(min <= val);
  assert(val <= max);

  app->options[opt].general    = general;
  app->options[opt].lng        = lng;
  app->options[opt].shrt       = shrt;
  app->options[opt].val        = val;
  app->options[opt].dflt       = val;
  app->options[opt].min        = min;
  app->options[opt].max        = max;
  app->options[opt].desc       = desc;
  app->options[opt].candisable = candisable;
  app->options[opt].isflag     = isflag;
  app->options[opt].arg        = arg;
}

static void
bzlamain_init_opts(BitwuzlaMainApp *app)
{
  assert(app);

  BZLA_CNEWN(app->mm, app->options, BZLAMAIN_OPT_NUM_OPTS);

  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_HELP,
                    true,
                    true,
                    "help",
                    "h",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "print this message and exit");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_HELP_EXPERT,
                    true,
                    true,
                    "help-expert",
                    "he",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "print help message (including expert options) and exit");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_COPYRIGHT,
                    true,
                    true,
                    "copyright",
                    "c",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "print copyright and exit");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_VERSION,
                    true,
                    true,
                    "version",
                    "V",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "print version and exit");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_TIME,
                    true,
                    false,
                    "time",
                    "t",
                    0,
                    0,
                    UINT32_MAX,
                    false,
                    BZLA_ARG_EXPECT_INT,
                    "set time limit");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_OUTPUT,
                    true,
                    false,
                    "output",
                    "o",
                    0,
                    0,
                    0,
                    false,
                    BZLA_ARG_EXPECT_STR,
                    "set output file for dumping");
#ifdef BZLA_USE_LINGELING
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_LGL_NOFORK,
                    true,
                    true,
                    "lingeling-nofork",
                    0,
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "do not use 'fork/clone' for Lingeling");
#endif
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_HEX,
                    true,
                    true,
                    "hex",
                    "x",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force hexadecimal number output");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DEC,
                    true,
                    true,
                    "dec",
                    "d",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force decimal number output");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_BIN,
                    true,
                    true,
                    "bin",
                    "b",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force binary number output");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_BTOR,
                    true,
                    true,
                    "btor",
                    0,
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force BTOR input format");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_BTOR2,
                    true,
                    true,
                    "btor2",
                    0,
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force BTOR2 input format");

  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_SMT2,
                    true,
                    true,
                    "smt2",
                    0,
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "force SMT-LIB v2 input format");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DUMP_BTOR,
                    true,
                    true,
                    "dump-bzla",
                    "db",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "dump formula in BTOR format");
#if 0
  bzlamain_init_opt (app, BZLAMAIN_OPT_DUMP_BTOR2, true, true,
                     "dump-btor2", "db2", 0, 0, 1,
                     false, BZLA_ARG_EXPECT_NONE,
                     "dump formula in BTOR 2.0 format");
#endif
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DUMP_SMT,
                    true,
                    true,
                    "dump-smt",
                    "ds",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "dump formula in SMT-LIB v2 format");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DUMP_AAG,
                    true,
                    true,
                    "dump-aag",
                    "daa",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "dump QF_BV formula in ascii AIGER format");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DUMP_AIG,
                    true,
                    true,
                    "dump-aig",
                    "dai",
                    0,
                    0,
                    1,
                    false,
                    BZLA_ARG_EXPECT_NONE,
                    "dump QF_BV formula in binary AIGER format");
  bzlamain_init_opt(app,
                    BZLAMAIN_OPT_DUMP_AIGER_MERGE,
                    true,
                    true,
                    "dump-aiger-merge",
                    "dam",
                    0,
                    0,
                    1,
                    true,
                    BZLA_ARG_EXPECT_NONE,
                    "merge all roots of AIG [0]");
}

static bool
bzlamain_opt_has_str_arg(const char *opt, BzlaOpt *bzla_opts)
{
  assert(opt);

  BitwuzlaMainOption mopt;
  BzlaMainOpt *mo;
  size_t i;

  for (mopt = 0; mopt < BZLAMAIN_OPT_NUM_OPTS; mopt++)
  {
    mo = &g_app->options[mopt];
    if ((mo->shrt && strcmp(mo->shrt, opt) == 0)
        || (mo->lng && strcmp(mo->lng, opt) == 0))
      return g_app->options[mopt].arg == BZLA_ARG_EXPECT_STR;
  }
  for (i = 0; i < BITWUZLA_OPT_NUM_OPTS; i++)
  {
    if (((bzla_opts[i].shrt && strcmp(opt, bzla_opts[i].shrt) == 0)
         || strcmp(opt, bzla_opts[i].lng) == 0)
        && bzla_opts[i].options)
      return true;
  }
  return false;
}

static void
bzlamain_print_stats(Bitwuzla *bitwuzla)
{
  bzla_sat_print_stats(bzla_get_sat_mgr(bitwuzla_get_bzla(bitwuzla)));
  bzla_print_stats(bitwuzla_get_bzla(bitwuzla));
}

/*------------------------------------------------------------------------*/

static BitwuzlaMainApp *
bzlamain_new_bzlamain(Bitwuzla *bitwuzla)
{
  assert(bitwuzla);

  BitwuzlaMainApp *res;
  BzlaMemMgr *mm;

  mm = bzla_mem_mgr_new();
  BZLA_CNEWN(mm, res, 1);
  res->mm          = mm;
  res->bitwuzla    = bitwuzla;
  res->bzla        = bitwuzla_get_bzla(bitwuzla);
  res->infile      = stdin;
  res->infile_name = "<stdin>";
  res->outfile     = stdout;
  bzlamain_init_opts(res);
  return res;
}

static void
bzlamain_delete_bzlamain(BitwuzlaMainApp *app)
{
  assert(app);

  BzlaMemMgr *mm;

  mm = app->mm;
  BZLA_DELETEN(mm, app->options, BZLAMAIN_OPT_NUM_OPTS);
  bitwuzla_delete(app->bitwuzla);
  BZLA_DELETE(mm, app);
  bzla_mem_mgr_delete(mm);
}

/*------------------------------------------------------------------------*/

static void
bzlamain_error(BitwuzlaMainApp *app, char *msg, ...)
{
  assert(app);

  va_list list;
  va_start(list, msg);
  fputs("bitwuzla: ", stderr);
  vfprintf(stderr, msg, list);
  fprintf(stderr, "\n");
  va_end(list);
  app->err = BZLA_ERR_EXIT;
}

static void
bzlamain_msg(char *msg, ...)
{
  assert(msg);

  va_list list;
  va_start(list, msg);
  fprintf(stdout, "[bitwuzla>main] ");
  vfprintf(stdout, msg, list);
  fprintf(stdout, "\n");
  va_end(list);
}

/*------------------------------------------------------------------------*/

#define LEN_OPTSTR 38
#define LEN_PARAMSTR 16
#define LEN_HELPSTR 81

#define IS_OPT(optlng, lng) (!strcmp(optlng, lng))

static const char *
get_opt_val_string(BzlaPtrHashTable *options, int32_t val)
{
  BzlaPtrHashTableIterator it;
  BzlaOptHelp *h;
  char *s = 0;

  if (options)
  {
    bzla_iter_hashptr_init(&it, options);
    while (bzla_iter_hashptr_has_next(&it))
    {
      h = (BzlaOptHelp *) it.bucket->data.as_ptr;
      s = bzla_iter_hashptr_next(&it);
      if (val == h->val) break;
    }
  }
  return s;
}

static char *
get_opt_vals_string(BzlaMemMgr *mm, BzlaOpt *bo)
{
  size_t i;
  char *s = 0;
  BzlaCharStack argopts;
  BzlaPtrHashTableIterator it;

  if (bo->options)
  {
    BZLA_INIT_STACK(mm, argopts);
    bzla_iter_hashptr_init(&it, bo->options);
    while (bzla_iter_hashptr_has_next(&it))
    {
      s = bzla_iter_hashptr_next(&it);
      for (i = 0; s[i]; i++) BZLA_PUSH_STACK(argopts, s[i]);
      if (bzla_iter_hashptr_has_next(&it))
      {
        BZLA_PUSH_STACK(argopts, ',');
        BZLA_PUSH_STACK(argopts, ' ');
      }
    }
    BZLA_PUSH_STACK(argopts, '\0');
    s = bzla_mem_strdup(mm, argopts.start);
    BZLA_RELEASE_STACK(argopts);
  }
  return s;
}

static void
print_opt_line_fmt(BitwuzlaMainApp *app,
                   char *str,
                   char *prefix,
                   size_t prefix_len,
                   size_t max_len)
{
  size_t i, j, len, slen;
  char *line, *word, *s;
  BzlaCharPtrStack words_stack;

  BZLA_CNEWN(app->mm, line, max_len);
  BZLA_INIT_STACK(app->mm, words_stack);

  slen = strlen(str) + 1;
  BZLA_CNEWN(app->mm, s, slen);
  strcpy(s, str);
  word = strtok(s, " ");
  while (word)
  {
    BZLA_PUSH_STACK(words_stack, bzla_mem_strdup(app->mm, word));
    word = strtok(0, " ");
  }
  BZLA_DELETEN(app->mm, s, slen);

  sprintf(line, "%s ", prefix);
  i = 0;
  do
  {
    j = prefix_len;
    for (; i < BZLA_COUNT_STACK(words_stack); i++)
    {
      word = BZLA_PEEK_STACK(words_stack, i);
      len  = strlen(word);
      /* word does not fit into remaining line */
      if (j + 1 + len >= max_len) break;
      strcpy(line + j, word);
      j += len;
      line[j++] = ' ';
    }
    line[j] = 0;
    fprintf(app->outfile, "%s\n", line);
    BZLA_CLRN(line, max_len);
    memset(line, ' ', prefix_len * sizeof(char));
  } while (i < BZLA_COUNT_STACK(words_stack));

  BZLA_DELETEN(app->mm, line, max_len);
  while (!BZLA_EMPTY_STACK(words_stack))
    bzla_mem_freestr(app->mm, BZLA_POP_STACK(words_stack));
  BZLA_RELEASE_STACK(words_stack);
}

static void
print_opt(BitwuzlaMainApp *app,
          const char *lng,
          const char *shrt,
          bool isflag,
          uint32_t dflt,
          const char *dflt_str,
          const char *opts_str,
          const char *desc,
          bool print_dflt)
{
  assert(app);
  assert(lng);
  assert(desc);

  char paramstr[LEN_PARAMSTR];
  char *str;
  size_t i, len, len_paramstr;
  BzlaCharStack optstr;
  BzlaMemMgr *mm;

  mm = app->mm;

  if (!strcmp(lng, "time"))
    sprintf(paramstr, "<seconds>");
  else if (!strcmp(lng, "output"))
    sprintf(paramstr, "<file>");
  else if (!strcmp(lng, bzla_opt_get_lng(app->bzla, BZLA_OPT_ENGINE))
           || !strcmp(lng, bzla_opt_get_lng(app->bzla, BZLA_OPT_SAT_ENGINE)))
    sprintf(paramstr, "<engine>");
  else if (!isflag)
  {
    if (!dflt_str)
      sprintf(paramstr, "<n>");
    else
      sprintf(paramstr, "<mode>");
  }
  else
    paramstr[0] = '\0';

  /* option string ------------------------------------------ */
  BZLA_INIT_STACK(mm, optstr);
  BZLA_PUSH_STACK(optstr, ' ');
  BZLA_PUSH_STACK(optstr, ' ');
  len_paramstr = strlen(paramstr);
  if (shrt)
  {
    if (len_paramstr)
    {
      fprintf(app->outfile, "  -%s %s,\n", shrt, paramstr);
      BZLA_PUSH_STACK(optstr, ' ');
      BZLA_PUSH_STACK(optstr, ' ');
    }
    else
    {
      BZLA_PUSH_STACK(optstr, '-');
      for (i = 0, len = strlen(shrt); i < len; i++)
        BZLA_PUSH_STACK(optstr, shrt[i]);
      if (len_paramstr > 0) BZLA_PUSH_STACK(optstr, ' ');
      for (i = 0; i < len_paramstr; i++) BZLA_PUSH_STACK(optstr, paramstr[i]);
      BZLA_PUSH_STACK(optstr, ',');
      BZLA_PUSH_STACK(optstr, ' ');
    }
  }
  BZLA_PUSH_STACK(optstr, '-');
  BZLA_PUSH_STACK(optstr, '-');
  for (i = 0, len = strlen(lng); i < len; i++) BZLA_PUSH_STACK(optstr, lng[i]);
  if (len_paramstr > 0) BZLA_PUSH_STACK(optstr, '=');
  for (i = 0; i < len_paramstr; i++) BZLA_PUSH_STACK(optstr, paramstr[i]);

  len = BZLA_COUNT_STACK(optstr);
  for (i = len; i < LEN_OPTSTR - 1; i++) BZLA_PUSH_STACK(optstr, ' ');
  BZLA_PUSH_STACK(optstr, '\0');
  assert(strlen(optstr.start) <= LEN_OPTSTR);

  /* formatted description ---------------------------------- */
  /* append default value to description */
  if (print_dflt)
  {
    if (dflt_str)
    {
      len = strlen(desc) + 3 + strlen(opts_str) + 3 + strlen(dflt_str);
      BZLA_CNEWN(mm, str, len + 1);
      sprintf(str, "%s {%s} [%s]", desc, opts_str, dflt_str);
    }
    else
    {
      len = strlen(desc) + 3 + bzla_util_num_digits(dflt);
      BZLA_CNEWN(mm, str, len + 1);
      sprintf(str, "%s [%u]", desc, dflt);
    }
  }
  else
  {
    len = strlen(desc);
    BZLA_CNEWN(mm, str, len + 1);
    sprintf(str, "%s", desc);
  }

  print_opt_line_fmt(app, str, optstr.start, LEN_OPTSTR, LEN_HELPSTR);
  BZLA_DELETEN(mm, str, len + 1);

  /* cleanup */
  BZLA_RELEASE_STACK(optstr);
}

static void
print_opt_help(BitwuzlaMainApp *app,
               const char *shrt,
               const char *lng,
               const char *desc,
               BzlaPtrHashTable *opts)
{
  assert(app);
  assert(lng);
  assert(desc);
  assert(opts);

  BzlaPtrHashTableIterator it;
  BzlaOptHelp *hdata;

  if (shrt)
    fprintf(app->outfile, "Modes for option -%s, --%s: %s\n", shrt, lng, desc);
  else
    fprintf(app->outfile, "Modes for option --%s: %s\n", lng, desc);

  bzla_iter_hashptr_init(&it, opts);
  while (bzla_iter_hashptr_has_next(&it))
  {
    fprintf(app->outfile, "\n  + %s:\n", (char *) it.cur);
    hdata = (BzlaOptHelp *) bzla_iter_hashptr_next_data(&it)->as_ptr;
    print_opt_line_fmt(app, (char *) hdata->msg, "    ", 4, LEN_HELPSTR);
  }
}

#define PRINT_MAIN_OPT(app, opt) \
  do                             \
  {                              \
    print_opt(app,               \
              (opt)->lng,        \
              (opt)->shrt,       \
              (opt)->isflag,     \
              (opt)->dflt,       \
              0,                 \
              0,                 \
              (opt)->desc,       \
              false);            \
  } while (0)

#define BITWUZLA_OPTS_INFO_MSG                                                 \
  "The following options can also be used in the form '-<short name>=<int>'"   \
  "\n"                                                                         \
  "and '--<long name>=<int>'. Flags are disabled with 0 and enabled with a "   \
  "pos."                                                                       \
  "\n"                                                                         \
  "integer. Alternatively, use '-no-<short name>' and '--no-<long name>' for"  \
  "\n"                                                                         \
  "disabling, and '-<short name>' and '--<long name>' for enabling flags."     \
  "\n\n"                                                                       \
  "You can query a more detailed help message for options that select a "      \
  "<mode>"                                                                     \
  "\n"                                                                         \
  "with -<short name>=help or --<long name>=help."                             \
  "\n\n"                                                                       \
  "Note that all of the following options can also be set via env. variables " \
  "of"                                                                         \
  "\n"                                                                         \
  "the form 'BZLA<capitalized long name without '-' and ':'>=<int>'."          \
  "\n\n"

static void
print_help(BitwuzlaMainApp *app, bool include_expert_opts)
{
  assert(app);

  BzlaOption o;
  BzlaOptionStack ostack;
  BitwuzlaMainOption mo;
  FILE *out;
  char *s;
  size_t i;

  Bzla *bzla = app->bzla;

  BZLA_INIT_STACK(app->mm, ostack);

  out = app->outfile;

  fprintf(out, "usage: bitwuzla [<option>...][<input>]\n");
  fprintf(out, "\n");
  fprintf(out, "where <option> is one of the following:\n");
  fprintf(out, "\n");

  for (mo = 0; mo < BZLAMAIN_OPT_NUM_OPTS; mo++)
  {
    if (!app->options[mo].general) continue;
    if (mo == BZLAMAIN_OPT_TIME || mo == BZLAMAIN_OPT_HEX
        || mo == BZLAMAIN_OPT_BTOR || mo == BZLAMAIN_OPT_BTOR2
        || mo == BZLAMAIN_OPT_DUMP_BTOR)
      fprintf(out, "\n");
    PRINT_MAIN_OPT(app, &app->options[mo]);
  }

  fprintf(out, "\n");

  for (mo = 0; mo < BZLAMAIN_OPT_NUM_OPTS; mo++)
  {
    if (app->options[mo].general) continue;
    if (mo == BZLAMAIN_OPT_LGL_NOFORK) continue;
    PRINT_MAIN_OPT(app, &app->options[mo]);
    if (mo == BZLAMAIN_OPT_DUMP_AIGER_MERGE) fprintf(out, "\n");
  }

  BZLA_PUSH_STACK(ostack, BZLA_OPT_ENGINE);
  BZLA_PUSH_STACK(ostack, BZLA_OPT_SAT_ENGINE);
  for (i = 0; i < BZLA_COUNT_STACK(ostack); i++)
  {
    o = BZLA_PEEK_STACK(ostack, i);
    s = get_opt_vals_string(app->mm, &bzla->options[o]);
    print_opt(
        app,
        bzla->options[o].lng,
        bzla->options[o].shrt,
        bzla->options[o].isflag,
        bzla->options[o].dflt,
        get_opt_val_string(bzla->options[o].options, bzla->options[o].dflt),
        s,
        bzla->options[o].desc,
        true);
    if (s) bzla_mem_freestr(app->mm, s);
  }
#ifdef BZLA_USE_LINGELING
  PRINT_MAIN_OPT(app, &app->options[BZLAMAIN_OPT_LGL_NOFORK]);
#endif

  fprintf(out, "\n");

  fprintf(out, BITWUZLA_OPTS_INFO_MSG);

  for (o = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, o);
       o = bzla_opt_next(bzla, o))
  {
    if (!include_expert_opts && bzla->options[o].expert) continue;

    s = get_opt_vals_string(app->mm, &bzla->options[o]);
    print_opt(
        app,
        bzla->options[o].lng,
        bzla->options[o].shrt,
        bzla->options[o].isflag,
        bzla->options[o].dflt,
        get_opt_val_string(bzla->options[o].options, bzla->options[o].dflt),
        s,
        bzla->options[o].desc,
        true);
    if (s) bzla_mem_freestr(app->mm, s);
    if (o == BZLA_OPT_AUTO_CLEANUP || o == BZLA_OPT_PP_BETA_REDUCE
        || o == BZLA_OPT_INCREMENTAL || o == BZLA_OPT_INPUT_FORMAT
        || o == BZLA_OPT_ENGINE || o == BZLA_OPT_RW_LEVEL
        || o == BZLA_OPT_RW_SORT_EXP)
    {
      fprintf(out, "\n");
    }
  }

  app->done = true;
  BZLA_RELEASE_STACK(ostack);
}

static void
print_static_stats(int32_t sat_res)
{
#ifdef BZLA_TIME_STATISTICS
  double real    = bzla_util_current_time() - g_start_time_real;
  double process = bzla_util_time_stamp();
  bzlamain_msg("%.3f seconds process", process);
  bzlamain_msg("%.3f seconds real", real);
#endif
  bzlamain_msg("%s",
               sat_res == BITWUZLA_SAT
                   ? "sat"
                   : (sat_res == BITWUZLA_UNSAT ? "unsat" : "unknown"));
}

static void
print_sat_result(BitwuzlaMainApp *app, int32_t sat_result)
{
  assert(app);
  if (sat_result == BITWUZLA_UNSAT)
    fprintf(app->outfile, "unsat\n");
  else if (sat_result == BITWUZLA_SAT)
    fprintf(app->outfile, "sat\n");
  else
  {
    assert(sat_result == BITWUZLA_UNKNOWN);
    fprintf(app->outfile, "unknown\n");
  }
}

/*------------------------------------------------------------------------*/

#ifdef BZLA_HAVE_SIGNALS
static void
reset_sig_handlers(void)
{
  (void) signal(SIGINT, sig_int_handler);
  (void) signal(SIGSEGV, sig_segv_handler);
  (void) signal(SIGABRT, sig_abrt_handler);
  (void) signal(SIGTERM, sig_term_handler);
  (void) signal(SIGBUS, sig_bus_handler);
}

static void
catch_sig(int32_t sig)
{
  if (!g_caught_sig)
  {
    g_caught_sig = true;
    if (g_verbosity > 0)
    {
      bzlamain_print_stats(g_app->bitwuzla);
      print_static_stats(0);
    }
    bzlamain_msg("CAUGHT SIGNAL %d", sig);
    fputs("unknown\n", stdout);
    fflush(stdout);
  }
  reset_sig_handlers();
  raise(sig);
}

static void
set_sig_handlers(void)
{
  sig_int_handler  = signal(SIGINT, catch_sig);
  sig_segv_handler = signal(SIGSEGV, catch_sig);
  sig_abrt_handler = signal(SIGABRT, catch_sig);
  sig_term_handler = signal(SIGTERM, catch_sig);
  sig_bus_handler  = signal(SIGBUS, catch_sig);
}

static void
reset_alarm(void)
{
  alarm(0);
  (void) signal(SIGALRM, sig_alrm_handler);
}

static void
catch_alarm(int32_t sig)
{
  (void) sig;
  assert(sig == SIGALRM);
  if (g_set_alarm > 0)
  {
    bzlamain_msg("ALARM TRIGGERED: time limit %d seconds reached", g_set_alarm);
    if (g_verbosity > 0)
    {
      bzlamain_print_stats(g_app->bitwuzla);
      print_static_stats(0);
    }
    fputs("unknown\n", stdout);
    fflush(stdout);
  }
  reset_alarm();
  _exit(0);
}

static void
set_alarm(void)
{
  sig_alrm_handler = signal(SIGALRM, catch_alarm);
  assert(g_set_alarm > 0);
  alarm(g_set_alarm);
}
#endif

/*------------------------------------------------------------------------*/

int32_t
bitwuzla_main(int32_t argc, char **argv)
{
  size_t i, len;
  int32_t res;
  int32_t parse_res;
  BitwuzlaResult parsed_status;
  int32_t sat_res;
  uint32_t format, mgen, pmodel, inc, dump;
  uint32_t val;
  char *cmd, *parse_err_msg;
  BzlaParsedOpt *po;
  BzlaParsedOptPtrStack opts;
  BzlaParsedInput *pin;
  BzlaParsedInputPtrStack infiles;
  BzlaOption bopt;
  BzlaOpt *bo;
  BitwuzlaMainOption bmopt;
  BzlaMainOpt *bmo;
  BzlaMemMgr *mm;
  Bzla *bzla;
  Bitwuzla *bitwuzla;
  BzlaPtrHashBucket *b;

  g_start_time_real = bzla_util_current_time();

  g_app    = bzlamain_new_bzlamain(bitwuzla_new());
  bitwuzla = g_app->bitwuzla;
  bzla     = bitwuzla_get_bzla(bitwuzla);
  mm       = g_app->mm;

  res           = BZLA_UNKNOWN_EXIT;
  parsed_status = BITWUZLA_UNKNOWN;
  sat_res       = BITWUZLA_UNKNOWN;

  inc    = 0;
  mgen   = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS);
  pmodel = 0;
  dump   = 0;

  BZLA_INIT_STACK(mm, opts);
  BZLA_INIT_STACK(mm, infiles);

  bzla_optparse_parse(mm,
                      argc,
                      argv,
                      &opts,
                      &infiles,
                      bitwuzla_get_bzla(bitwuzla)->options,
                      bzlamain_opt_has_str_arg);

  /* input file ======================================================= */

  if (BZLA_COUNT_STACK(infiles) > 1)
  {
    bzlamain_error(g_app, "multiple input files");
    goto DONE;
  }
  else if (BZLA_COUNT_STACK(infiles) == 1)
  {
    g_app->infile_name = BZLA_PEEK_STACK(infiles, 0)->name;
    if (!bzla_util_file_exists(g_app->infile_name))
    {
      g_app->infile = 0;
    }
    else if (bzla_util_file_has_suffix(g_app->infile_name, ".gz")
             || bzla_util_file_has_suffix(g_app->infile_name, ".bz2")
             || bzla_util_file_has_suffix(g_app->infile_name, ".7z")
             || bzla_util_file_has_suffix(g_app->infile_name, ".zip"))
    {
      len = strlen(g_app->infile_name);
      BZLA_NEWN(g_app->mm, cmd, len + 40);
      if (bzla_util_file_has_suffix(g_app->infile_name, ".gz"))
        sprintf(cmd, "gunzip -c %s", g_app->infile_name);
      else if (bzla_util_file_has_suffix(g_app->infile_name, ".bz2"))
        sprintf(cmd, "bzcat %s", g_app->infile_name);
      else if (bzla_util_file_has_suffix(g_app->infile_name, ".7z"))
        sprintf(cmd, "7z x -so %s 2> /dev/null", g_app->infile_name);
      else if (bzla_util_file_has_suffix(g_app->infile_name, ".zip"))
        sprintf(cmd, "unzip -p %s", g_app->infile_name);

      if ((g_app->infile = popen(cmd, "r"))) g_app->close_infile = 2;

      BZLA_DELETEN(g_app->mm, cmd, len + 40);
    }
    else if ((g_app->infile = fopen(g_app->infile_name, "r")))
    {
      g_app->close_infile = 1;
    }

    if (!g_app->infile)
    {
      bzlamain_error(g_app, "can not read '%s'", g_app->infile_name);
      goto DONE;
    }
  }

  /* options ========================================================== */

  for (i = 0; i < BZLA_COUNT_STACK(opts); i++)
  {
    po = BZLA_PEEK_STACK(opts, i);

    for (bmopt = 0, bmo = 0; bmopt < BZLAMAIN_OPT_NUM_OPTS; bmopt++)
    {
      bmo = &g_app->options[bmopt];
      if ((po->isshrt && bmo->shrt && !strcmp(bmo->shrt, po->name.start))
          || (!po->isshrt && bmo->lng && !strcmp(bmo->lng, po->name.start)))
      {
        break;
      }
      bmo = 0;
    }

    /* main options ----------------------------------------------------- */
    if (bmo)
    {
      /* check opt */
      if (po->isdisable && !bmo->candisable)
      {
        bzlamain_error(g_app, "invalid option '%s'", po->orig.start);
        goto DONE;
      }
      if (bmo->arg == BZLA_ARG_EXPECT_NONE)
      {
        if (BZLA_ARG_IS_UNEXPECTED(bmo->arg, po->readval, po->isdisable))
        {
          bzlamain_error(
              g_app, "option '%s' does not expect an argument", po->orig.start);
          goto DONE;
        }
      }
      else
      {
        if (BZLA_ARG_IS_MISSING(bmo->arg, bmo->candisable, po->readval))
        {
          bzlamain_error(g_app, "missing argument for '%s'", po->orig.start);
          goto DONE;
        }
        if (BZLA_ARG_IS_INVALID(bmo->arg, bmo->candisable, po->readval))
        {
          bzlamain_error(
              g_app, "invalid argument for '%s', expected int", po->orig.start);
          goto DONE;
        }
      }
      /* set opt */
      switch (bmopt)
      {
        case BZLAMAIN_OPT_HELP: print_help(g_app, false); goto DONE;

        case BZLAMAIN_OPT_HELP_EXPERT: print_help(g_app, true); goto DONE;

        case BZLAMAIN_OPT_COPYRIGHT:
          fprintf(g_app->outfile, "%s", bitwuzla_copyright(bitwuzla));
          g_app->done = true;
          goto DONE;

        case BZLAMAIN_OPT_VERSION:
          fprintf(g_app->outfile, "%s\n", bitwuzla_version(bitwuzla));
          g_app->done = true;
          goto DONE;

        case BZLAMAIN_OPT_TIME: g_set_alarm = po->val; break;

        case BZLAMAIN_OPT_OUTPUT:
          if (g_app->close_outfile)
          {
            bzlamain_error(g_app, "multiple output files");
            goto DONE;
          }
          g_app->outfile_name = po->valstr;
          break;

        case BZLAMAIN_OPT_LGL_NOFORK:
          bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_SAT_ENGINE_LGL_FORK, 0);
          break;

        case BZLAMAIN_OPT_HEX:
          format = BZLA_OUTPUT_BASE_HEX;
        SET_OUTPUT_NUMBER_FORMAT:
          bitwuzla_set_option(
              bitwuzla, BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT, format);
          break;

        case BZLAMAIN_OPT_DEC:
          format = BZLA_OUTPUT_BASE_DEC;
          goto SET_OUTPUT_NUMBER_FORMAT;

        case BZLAMAIN_OPT_BIN:
          format = BZLA_OUTPUT_BASE_BIN;
          goto SET_OUTPUT_NUMBER_FORMAT;

        case BZLAMAIN_OPT_BTOR:
          format = BZLA_INPUT_FORMAT_BTOR;
        SET_INPUT_FORMAT:
          bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_INPUT_FORMAT, format);
          break;

        case BZLAMAIN_OPT_BTOR2:
          format = BZLA_INPUT_FORMAT_BTOR2;
          goto SET_INPUT_FORMAT;

        case BZLAMAIN_OPT_SMT2:
          format = BZLA_INPUT_FORMAT_SMT2;
          goto SET_INPUT_FORMAT;

        case BZLAMAIN_OPT_DUMP_BTOR:
          dump = BZLA_OUTPUT_FORMAT_BTOR;
        SET_OUTPUT_FORMAT:
          bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_OUTPUT_FORMAT, dump);
          bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PARSE_INTERACTIVE, 0);
          break;
#if 0
              case BZLAMAIN_OPT_DUMP_BTOR2:
                dump = BZLA_OUTPUT_FORMAT_BTOR2;
                goto SET_OUTPUT_FORMAT;
#endif
        case BZLAMAIN_OPT_DUMP_SMT:
          dump = BZLA_OUTPUT_FORMAT_SMT2;
          goto SET_OUTPUT_FORMAT;

        case BZLAMAIN_OPT_DUMP_AAG:
          dump = BZLA_OUTPUT_FORMAT_AIGER_ASCII;
          goto SET_OUTPUT_FORMAT;

        case BZLAMAIN_OPT_DUMP_AIG:
          dump = BZLA_OUTPUT_FORMAT_AIGER_BINARY;
          goto SET_OUTPUT_FORMAT;

        default:
          /* get rid of compiler warnings, should be unreachable */
          assert(bmopt == BZLAMAIN_OPT_NUM_OPTS);
      }
    }
    /* >> bzla options ------------------------------------------------ */
    else
    {
      for (bopt = bzla_opt_first(bzla), bo = 0; bzla_opt_is_valid(bzla, bopt);
           bopt = bzla_opt_next(bzla, bopt))
      {
        bo = &bzla->options[bopt];
        if ((po->isshrt && bo->shrt && !strcmp(bo->shrt, po->name.start))
            || (!po->isshrt && !strcmp(bo->lng, po->name.start)))
        {
          break;
        }
        bo = 0;
      }
      /* check opt */
      if (!bo)
      {
        bzlamain_error(g_app, "invalid option '%s'", po->orig.start);
        goto DONE;
      }
      if ((bo->options
           && BZLA_ARG_IS_MISSING(BZLA_ARG_EXPECT_STR, bo->isflag, po->readval))
          || (!bo->options
              && BZLA_ARG_IS_MISSING(
                  BZLA_ARG_EXPECT_INT, bo->isflag, po->readval)))
      {
        bzlamain_error(g_app, "missing argument for '%s'", po->orig.start);
        goto DONE;
      }
      if (bo->options)
      {
        if (strcmp(po->valstr, "help") == 0)
        {
          print_opt_help(g_app, bo->shrt, bo->lng, bo->desc, bo->options);
          goto DONE;
        }
        else if (!(b = bzla_hashptr_table_get(bo->options, po->valstr)))
        {
          char *s = get_opt_vals_string(mm, bo);
          assert(s);
          bzlamain_error(g_app,
                         "invalid argument '%s' for '%s', expected one of '%s'",
                         po->valstr,
                         po->orig.start,
                         s);
          bzla_mem_freestr(mm, s);
          goto DONE;
        }

        bitwuzla_set_option(bitwuzla,
                            bitwuzla_options[bopt],
                            ((BzlaOptHelp *) b->data.as_ptr)->val);
      }
      else
      {
        if (BZLA_ARG_IS_INVALID(BZLA_ARG_EXPECT_INT, bo->isflag, po->readval))
        {
          bzlamain_error(
              g_app, "invalid argument for '%s', expected int", po->orig.start);
          goto DONE;
        }

        if (bo->isflag)
        {
          if (po->isdisable)
          {
            if (bopt == BZLA_OPT_PRODUCE_MODELS)
            {
              mgen   = 0;
              pmodel = 0;
            }
            else
            {
              bitwuzla_set_option(bitwuzla, bitwuzla_options[bopt], 0);
            }
          }
          else
          {
            switch (bopt)
            {
              case BZLA_OPT_PRODUCE_MODELS:
                if (BZLA_ARG_READ_IS_INT(po->readval) && po->val == 0)
                {
                  mgen   = 0;
                  pmodel = 0;
                }
                else
                {
                  mgen += 1;
                  pmodel = 1;
                }
                break;
              case BITWUZLA_OPT_VERBOSITY:
              case BITWUZLA_OPT_LOGLEVEL:
                if (BZLA_ARG_READ_IS_INT(po->readval))
                {
                  bitwuzla_set_option(
                      bitwuzla, bitwuzla_options[bopt], po->val);
                }
                else
                {
                  bitwuzla_set_option(bitwuzla,
                                      bitwuzla_options[bopt],
                                      bzla_opt_get(bzla, bopt) + 1);
                }
                break;
              default:
                assert(bopt != BZLA_OPT_NUM_OPTS);
                if (BZLA_ARG_READ_IS_INT(po->readval))
                {
                  bitwuzla_set_option(
                      bitwuzla, bitwuzla_options[bopt], po->val);
                }
                else
                {
                  bitwuzla_set_option(bitwuzla, bitwuzla_options[bopt], 1);
                }
            }
          }
        }
        else
        {
          assert(BZLA_ARG_READ_IS_INT(po->readval));
          bitwuzla_set_option(bitwuzla, bitwuzla_options[bopt], po->val);
        }
      }
    }
  }

  assert(!g_app->done && !g_app->err);

  g_verbosity = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_VERBOSITY);

  /* open output file */
  if (g_app->outfile_name)
  {
    if (!strcmp(g_app->outfile_name, g_app->infile_name))
    {
      bzlamain_error(g_app, "input and output file must not be the same");
      goto DONE;
    }

    g_app->outfile = fopen(g_app->outfile_name, "w");
    if (!g_app->outfile)
    {
      bzlamain_error(g_app, "can not create '%s'", g_app->outfile_name);
      goto DONE;
    }
    g_app->close_outfile = true;
  }

  // TODO: disabling model generation not yet supported (ma)
  if (mgen > 0)
    bitwuzla_set_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS, mgen);

  /* print verbose info and set signal handlers */
  if (g_verbosity)
  {
    if (inc) bzlamain_msg("incremental mode through command line option");
    bzlamain_msg("Bitwuzla Version %s %s", BZLA_VERSION, BZLA_GIT_ID);
    bzlamain_msg("%s", BZLA_CFLAGS);
    bzlamain_msg("released %s", BZLA_RELEASED);
    bzlamain_msg("compiled %s", BZLA_COMPILED);
    if (*BZLA_CC) bzlamain_msg("%s", BZLA_CC);
    bzlamain_msg("setting signal handlers");
  }
#ifdef BZLA_HAVE_SIGNALS
  set_sig_handlers();

  /* set alarm */
  if (g_set_alarm)
  {
    if (g_verbosity)
      bzlamain_msg("setting time limit to %d seconds", g_set_alarm);
    set_alarm();
  }
  else if (g_verbosity)
    bzlamain_msg("no time limit given");
#endif

  if (inc && g_verbosity) bzlamain_msg("starting incremental mode");

  /* parse */
  bool parsed_smt2 = false;
  val              = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_INPUT_FORMAT);
  switch (val)
  {
    case BZLA_INPUT_FORMAT_BTOR:
      if (g_verbosity)
        bzlamain_msg("BTOR input forced through cmd line options");
      parse_res = bitwuzla_parse_format(bitwuzla,
                                        "btor",
                                        g_app->infile,
                                        g_app->infile_name,
                                        g_app->outfile,
                                        &parse_err_msg,
                                        &parsed_status);
      break;
    case BZLA_INPUT_FORMAT_BTOR2:
      if (g_verbosity)
        bzlamain_msg("BTOR2 input forced through cmd line options");
      parse_res = bitwuzla_parse_format(bitwuzla,
                                        "btor2",
                                        g_app->infile,
                                        g_app->infile_name,
                                        g_app->outfile,
                                        &parse_err_msg,
                                        &parsed_status);
      break;
    case BZLA_INPUT_FORMAT_SMT2:
      if (g_verbosity)
        bzlamain_msg("SMT-LIB v2 input forced through cmd line options");
      parse_res   = bitwuzla_parse_format(bitwuzla,
                                        "smt2",
                                        g_app->infile,
                                        g_app->infile_name,
                                        g_app->outfile,
                                        &parse_err_msg,
                                        &parsed_status);
      parsed_smt2 = true;
      break;

    default:
      parse_res = bitwuzla_parse(bitwuzla,
                                 g_app->infile,
                                 g_app->infile_name,
                                 g_app->outfile,
                                 &parse_err_msg,
                                 &parsed_status,
                                 &parsed_smt2);
  }

  /* verbosity may have been increased via input (set-option) */
  g_verbosity = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_VERBOSITY);

  if (parse_err_msg)
  {
    /* NOTE: do not use bzlamain_error here as 'parse_err_msg' must not be
     * treated as format string --- it might contain unescaped '%' due to
     * invalid user input. */
    fprintf(stderr, "bitwuzla: %s\n", parse_err_msg);
    free(parse_err_msg);
    g_app->err = BZLA_ERR_EXIT;
    goto DONE;
  }

  /* incremental mode */
  if (inc)
  {
    if (parse_res == BITWUZLA_SAT)
    {
      if (g_verbosity) bzlamain_msg("one formula SAT in incremental mode");
      sat_res = BITWUZLA_SAT;
    }
    else if (parse_res == BITWUZLA_UNSAT)
    {
      if (g_verbosity) bzlamain_msg("all formulas UNSAT in incremental mode");
      sat_res = BITWUZLA_UNSAT;
    }

    if (g_verbosity) bzlamain_print_stats(bitwuzla);

    if (pmodel && sat_res == BITWUZLA_SAT)
    {
      assert(bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS));
      format = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_OUTPUT_FORMAT);
      if (format == BZLA_OUTPUT_FORMAT_BTOR || !parsed_smt2)
      {
        bitwuzla_print_model(bitwuzla, "btor", g_app->outfile);
      }
      else
      {
        bitwuzla_print_model(bitwuzla, "smt2", g_app->outfile);
      }
    }

#ifdef BZLA_TIME_STATISTICS
    if (g_verbosity) bzlamain_msg("%.1f seconds", bzla_util_time_stamp());
#endif
    goto DONE;
  }
  /* we don't dump formula(s) in incremental mode */
  else if (dump)
  {
    (void) bitwuzla_simplify(bitwuzla);

    switch (dump)
    {
      case BZLA_OUTPUT_FORMAT_BTOR:
        if (g_verbosity) bzlamain_msg("dumping BTOR expressions");
        bitwuzla_dump_formula(bitwuzla, "btor", g_app->outfile);
        break;
      case BZLA_OUTPUT_FORMAT_SMT2:
        if (g_verbosity) bzlamain_msg("dumping in SMT 2.0 format");
        bitwuzla_dump_formula(bitwuzla, "smt2", g_app->outfile);
        break;
      case BZLA_OUTPUT_FORMAT_AIGER_ASCII:
        if (g_verbosity) bzlamain_msg("dumping in ascii AIGER format");
        bitwuzla_dump_formula(bitwuzla, "aiger_ascii", g_app->outfile);
        break;
      default:
        assert(dump == BZLA_OUTPUT_FORMAT_AIGER_BINARY);
        if (g_verbosity) bzlamain_msg("dumping in binary AIGER format");
        bitwuzla_dump_formula(bitwuzla, "aiger_binary", g_app->outfile);
    }

    if (g_verbosity) bzlamain_print_stats(bitwuzla);

    goto DONE;
  }

  /* call sat (if not yet called) */
  if (parse_res == BITWUZLA_UNKNOWN && !bzla_terminate(bzla) && !parsed_smt2)
  {
    sat_res = bitwuzla_check_sat(bitwuzla);
    print_sat_result(g_app, sat_res);
  }
  else
    sat_res = parse_res;

  /* check if status is equal to benchmark status (if provided) */
  if (sat_res == BITWUZLA_SAT && parsed_status == BITWUZLA_UNSAT)
    bzlamain_error(g_app,
                   "'sat' but status of benchmark in '%s' is 'unsat'",
                   g_app->infile_name);
  else if (sat_res == BITWUZLA_UNSAT && parsed_status == BITWUZLA_SAT)
    bzlamain_error(g_app,
                   "'unsat' but status of benchmark in '%s' is 'sat'",
                   g_app->infile_name);

  /* print stats */
  if (g_verbosity)
  {
    bzlamain_print_stats(bitwuzla);
    print_static_stats(sat_res);
  }

  /* print model */
  if (pmodel && sat_res == BITWUZLA_SAT)
  {
    assert(bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_PRODUCE_MODELS));
    format = bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_OUTPUT_FORMAT);
    if (format == BZLA_OUTPUT_FORMAT_BTOR || !parsed_smt2)
    {
      bitwuzla_print_model(bitwuzla, "btor", g_app->outfile);
    }
    else
    {
      bitwuzla_print_model(bitwuzla, "smt2", g_app->outfile);
    }
  }

DONE:
  if (g_app->done)
    res = BZLA_SUCC_EXIT;
  else if (g_app->err)
    res = BZLA_ERR_EXIT;
  else if (sat_res == BITWUZLA_UNSAT)
    res = BZLA_UNSAT_EXIT;
  else if (sat_res == BITWUZLA_SAT)
    res = BZLA_SAT_EXIT;

  assert(res == BZLA_ERR_EXIT || res == BZLA_SUCC_EXIT || res == BZLA_SAT_EXIT
         || res == BZLA_UNSAT_EXIT || res == BZLA_UNKNOWN_EXIT);

  if (g_app->close_infile == 1)
    fclose(g_app->infile);
  else if (g_app->close_infile == 2)
    pclose(g_app->infile);
  if (g_app->close_outfile) fclose(g_app->outfile);

  if (!bitwuzla_get_option(bitwuzla, BITWUZLA_OPT_EXIT_CODES))
  {
    switch (res)
    {
      case BZLA_UNSAT_EXIT:
      case BZLA_SAT_EXIT: res = BZLA_SUCC_EXIT; break;
      default: res = BZLA_ERR_EXIT;
    }
  }

  while (!BZLA_EMPTY_STACK(opts))
  {
    po = BZLA_POP_STACK(opts);
    assert(po->mm == mm);
    BZLA_RELEASE_STACK(po->orig);
    BZLA_RELEASE_STACK(po->name);
    BZLA_DELETE(mm, po);
  }
  BZLA_RELEASE_STACK(opts);
  while (!BZLA_EMPTY_STACK(infiles))
  {
    pin = BZLA_POP_STACK(infiles);
    assert(pin->mm == mm);
    BZLA_DELETE(mm, pin);
  }
  BZLA_RELEASE_STACK(infiles);

  bzlamain_delete_bzlamain(g_app);
#ifdef BZLA_HAVE_SIGNALS
  reset_sig_handlers();
#endif

  return res;
}
