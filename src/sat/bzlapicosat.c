/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "sat/bzlapicosat.h"

#include "utils/bzlaabort.h"

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_PICOSAT
/*------------------------------------------------------------------------*/

#include "bzlacore.h"
#include "picosat.h"

static void *
init(BzlaSATMgr *smgr)
{
  PicoSAT *res;

  BZLA_MSG(smgr->bzla->msg, 1, "PicoSAT Version %s", picosat_version());

  res = picosat_minit(smgr->bzla->mm,
                      (picosat_malloc) bzla_mem_sat_malloc,
                      (picosat_realloc) bzla_mem_sat_realloc,
                      (picosat_free) bzla_mem_sat_free);

  picosat_set_global_default_phase(res, 0);

  return res;
}

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  (void) picosat_add(smgr->solver, lit);
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  return picosat_sat(smgr->solver, limit);
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  return picosat_deref(smgr->solver, lit);
}

static void
reset(BzlaSATMgr *smgr)
{
  picosat_reset(smgr->solver);
  smgr->solver = 0;
}

static void
set_output(BzlaSATMgr *smgr, FILE *output)
{
  picosat_set_output(smgr->solver, output);
}

static void
set_prefix(BzlaSATMgr *smgr, const char *prefix)
{
  picosat_set_prefix(smgr->solver, prefix);
}

static void
enable_verbosity(BzlaSATMgr *smgr, int32_t level)
{
  if (level >= 2) picosat_set_verbosity(smgr->solver, level - 1);
}

static int32_t
inc_max_var(BzlaSATMgr *smgr)
{
  return picosat_inc_max_var(smgr->solver);
}

static void
stats(BzlaSATMgr *smgr)
{
  picosat_stats(smgr->solver);
}

static int32_t
fixed(BzlaSATMgr *smgr, int32_t lit)
{
  return picosat_deref_toplevel(smgr->solver, lit);
}

/*------------------------------------------------------------------------*/

static void
assume(BzlaSATMgr *smgr, int32_t lit)
{
  (void) picosat_assume(smgr->solver, lit);
}

static int32_t
failed(BzlaSATMgr *smgr, int32_t lit)
{
  return picosat_failed_assumption(smgr->solver, lit);
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_picosat(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_picosat'");

  smgr->name = "PicoSAT";

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.melt             = 0;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = set_output;
  smgr->api.set_prefix       = set_prefix;
  smgr->api.stats            = stats;
  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
