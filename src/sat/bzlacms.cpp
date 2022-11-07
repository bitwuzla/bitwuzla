/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifdef BZLA_USE_CMS

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstring>
#include <vector>

#include "sat/cryptominisat.h"

extern "C" {
#include "bzlaopt.h"
#include "bzlasat.h"
#include "sat/bzlacms.h"
#include "utils/bzlaabort.h"
}

/*------------------------------------------------------------------------*/

static void*
init(BzlaSATMgr* smgr)
{
  (void) smgr;
  bzla::sat::CryptoMiniSat* res = new bzla::sat::CryptoMiniSat();
  uint32_t nthreads;
  if ((nthreads = bzla_opt_get(smgr->bzla, BZLA_OPT_SAT_ENGINE_N_THREADS)) > 1)
  {
    res->set_num_threads(nthreads);
  }
  return res;
}

static void
add(BzlaSATMgr* smgr, int32_t lit)
{
  static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->add(lit);
}

static int32_t
sat(BzlaSATMgr* smgr, int32_t limit)
{
  (void) limit;
  bzla::Result res =
      static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->solve();
  if (res == bzla::Result::SAT) return 10;
  if (res == bzla::Result::UNSAT) return 20;
  return 0;
}

static int32_t
deref(BzlaSATMgr* smgr, int32_t lit)
{
  return static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->value(lit);
}

static void
reset(BzlaSATMgr* smgr)
{
  delete static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver);
  smgr->solver = 0;
}

static int32_t
inc_max_var(BzlaSATMgr* smgr)
{
  return static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->new_var();
}

static void
assume(BzlaSATMgr* smgr, int32_t lit)
{
  static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->assume(lit);
}

static int32_t
fixed(BzlaSATMgr* smgr, int32_t lit)
{
  return static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->fixed(lit);
}

static int32_t
failed(BzlaSATMgr* smgr, int32_t lit)
{
  return static_cast<bzla::sat::CryptoMiniSat*>(smgr->solver)->failed(lit);
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_cms(BzlaSATMgr* smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_cms'");

  smgr->name = "CryptoMiniSat";

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = 0;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = 0;
  smgr->api.set_prefix       = 0;
  smgr->api.stats            = 0;
  return true;
}

#endif
