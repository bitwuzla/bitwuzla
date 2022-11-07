/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*------------------------------------------------------------------------*/

extern "C" {
#include "bzlacadical.h"

#include "utils/bzlaabort.h"
}

#include "sat/cadical.h"

static void *
init(BzlaSATMgr *smgr)
{
  (void) smgr;
  return new bzla::sat::Cadical();
}

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  static_cast<bzla::sat::Cadical *>(smgr->solver)->add(lit);
}

static void
assume(BzlaSATMgr *smgr, int32_t lit)
{
  static_cast<bzla::sat::Cadical *>(smgr->solver)->assume(lit);
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  return static_cast<bzla::sat::Cadical *>(smgr->solver)->value(lit);
}

static int32_t
failed(BzlaSATMgr *smgr, int32_t lit)
{
  return static_cast<bzla::sat::Cadical *>(smgr->solver)->failed(lit);
}

static int32_t
fixed(BzlaSATMgr *smgr, int32_t lit)
{
  return static_cast<bzla::sat::Cadical *>(smgr->solver)->fixed(lit);
}

static void
reset(BzlaSATMgr *smgr)
{
  delete static_cast<bzla::sat::Cadical *>(smgr->solver);
  smgr->solver = 0;
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  (void) limit;
  bzla::Result res = static_cast<bzla::sat::Cadical *>(smgr->solver)->solve();
  if (res == bzla::Result::SAT) return 10;
  if (res == bzla::Result::UNSAT) return 20;
  return 0;
}

static void
setterm(BzlaSATMgr *smgr)
{
  static_cast<bzla::sat::Cadical *>(smgr->solver)
      ->set_terminate(smgr->term.fun, smgr->term.state);
}

bool
bzla_sat_enable_cadical(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_cadical'");

  smgr->name = "CaDiCaL";

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = 0;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
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

  smgr->have_restore = true;

  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
