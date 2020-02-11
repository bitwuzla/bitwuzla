/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2020 Aina Niemetz.
 *  Copyright (C) 2014-2017 Mathias Preiner.
 *  Copyright (C) 2014-2015 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAOPTS_H_INCLUDED
#define BZLAOPTS_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "bzlatypes.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

struct BzlaOpt
{
  bool internal;             /* internal option? */
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
#elif BZLA_USE_MINISAT
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_MINISAT
#elif BZLA_USE_CMS
#define BZLA_SAT_ENGINE_DFLT BZLA_SAT_ENGINE_CMS
#endif
extern const char *const g_bzla_se_name[BZLA_SAT_ENGINE_MAX + 1];

#define BZLA_ENGINE_MIN BZLA_ENGINE_FUN
#define BZLA_ENGINE_MAX BZLA_ENGINE_QUANT
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

#define BZLA_PROP_PATH_SEL_MIN BZLA_PROP_PATH_SEL_CONTROLLING
#define BZLA_PROP_PATH_SEL_MAX BZLA_PROP_PATH_SEL_RANDOM
#define BZLA_PROP_PATH_SEL_DFLT BZLA_PROP_PATH_SEL_ESSENTIAL

#define BZLA_PROP_ENTAILED_DFLT BZLA_PROP_ENTAILED_OFF

#define BZLA_QUANT_SYNTH_MIN BZLA_QUANT_SYNTH_NONE
#define BZLA_QUANT_SYNTH_MAX BZLA_QUANT_SYNTH_ELMR
#define BZLA_QUANT_SYNTH_DFLT BZLA_QUANT_SYNTH_ELMR

#define BZLA_FUN_EAGER_LEMMAS_MIN BZLA_FUN_EAGER_LEMMAS_NONE
#define BZLA_FUN_EAGER_LEMMAS_MAX BZLA_FUN_EAGER_LEMMAS_ALL
#define BZLA_FUN_EAGER_LEMMAS_DFLT BZLA_FUN_EAGER_LEMMAS_CONF

#define BZLA_INCREMENTAL_SMT1_MIN BZLA_INCREMENTAL_SMT1_BASIC
#define BZLA_INCREMENTAL_SMT1_MAX BZLA_INCREMENTAL_SMT1_CONTINUE
#define BZLA_INCREMENTAL_SMT1_DFLT BZLA_INCREMENTAL_SMT1_BASIC

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

BzlaOption bzla_opt_first(Bzla *bzla);
BzlaOption bzla_opt_next(Bzla *bzla, BzlaOption cur);

#ifndef NBZLALOG
void bzla_opt_log_opts(Bzla *bzla);
#endif
#endif
