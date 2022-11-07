/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

extern "C" {
#include "sat/bzlakissat.h"

#include "utils/bzlaabort.h"
}

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "sat/kissat.h"

static void *
init(BzlaSATMgr *smgr)
{
  (void) smgr;
  return new bzla::sat::Kissat();
}

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  static_cast<bzla::sat::Kissat *>(smgr->solver)->add(lit);
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  (void) limit;
  Result res = static_cast<bzla::sat::Kissat *>(smgr->solver)->solve();
  if (res == Result::SAT) return 10;
  if (res == Result::UNSAT) return 20;
  return 0;
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  return static_cast<bzla::sat::Kissat *>(smgr->solver)->value(lit);
}

static void
reset(BzlaSATMgr *smgr)
{
  delete static_cast<bzla::sat::Kissat *>(smgr->solver);
  smgr->solver = 0;
}

static void
setterm(BzlaSATMgr *smgr)
{
  static_cast<bzla::sat::Kissat *>(smgr->solver)
      ->set_terminate(smgr->term.fun, smgr->term.state);
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
  smgr->api.setterm          = setterm;
  return true;
}
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
