/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "sat/bzlakissat.h"

#include "utils/bzlaabort.h"

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "bzlacore.h"
#include "kissat.h"

static void *
init(BzlaSATMgr *smgr)
{
  kissat *slv;

  BZLA_MSG(smgr->bzla->msg, 1, "Kissat Version %s", kissat_version());

  slv = kissat_init();

  return slv;
}

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  kissat_add(smgr->solver, lit);
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  (void) limit;
  return kissat_solve(smgr->solver);
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  int32_t val;
  val = kissat_value(smgr->solver, lit);
  if (val > 0) return 1;
  if (val < 0) return -1;
  return 0;
}

static void
reset(BzlaSATMgr *smgr)
{
  kissat_release(smgr->solver);
  smgr->solver = 0;
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_kissat(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_kissat'");

  smgr->name = "Kissat";

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = 0;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = 0;
  smgr->api.failed           = 0;
  smgr->api.fixed            = 0;
  smgr->api.inc_max_var      = 0;
  smgr->api.init             = init;
  smgr->api.melt             = 0;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = 0;
  smgr->api.set_prefix       = 0;
  smgr->api.stats            = 0;
  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
