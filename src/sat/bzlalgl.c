/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "sat/bzlalgl.h"

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_LINGELING
/*------------------------------------------------------------------------*/

#include <ctype.h>
#include <limits.h>

#include "bzlacore.h"
#include "bzlaopt.h"
#include "utils/bzlaabort.h"

#define BZLA_LGL_SIMP_DELAY 10000
#define BZLA_LGL_MIN_BLIMIT 50000
#define BZLA_LGL_MAX_BLIMIT 200000

/*------------------------------------------------------------------------*/
//#define BZLA_PRINT_DIMACS_FOR_LINGELING // enable to print dimacs files
#ifdef BZLA_PRINT_DIMACS_FOR_LINGELING
#include <sys/types.h>  // for getpid
#include <unistd.h>     // for getpid
#endif

/*------------------------------------------------------------------------*/

static void *
init(BzlaSATMgr *smgr)
{
  BzlaLGL *res;

  if (bzla_opt_get(smgr->bzla, BZLA_OPT_VERBOSITY) >= 1)
  {
    lglbnr("Lingeling", "[lingeling] ", stdout);
    fflush(stdout);
  }

  BZLA_CNEW(smgr->bzla->mm, res);
  res->lgl = lglminit(smgr->bzla->mm,
                      (lglalloc) bzla_mem_sat_malloc,
                      (lglrealloc) bzla_mem_sat_realloc,
                      (lgldealloc) bzla_mem_sat_free);

  res->blimit = BZLA_LGL_MIN_BLIMIT;

  return res;
}

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  lgladd(blgl->lgl, lit);
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  BzlaLGL *blgl = smgr->solver;
  LGL *lgl      = blgl->lgl, *clone;
  const char *str;
  int32_t res, bfres;
  size_t len;
  char *name;

  assert(smgr->satcalls >= 1);

  lglsetopt(lgl, "simplify", 1);

#ifdef BZLA_PRINT_DIMACS_FOR_LINGELING
  {
    static int32_t count = 0;
    char name[80];
    FILE *file;
    snprintf(
        name, 80, "/tmp/bzla_lingeling_sat_%05d_%08d.cnf", getpid(), count++);
    file = fopen(name, "w");
    lglprint(lgl, file);
    fclose(file);
    BZLA_MSG(smgr->bzla->msg, 0, "wrote %s", name);
  }
#endif

  if (smgr->inc_required
      && (smgr->satcalls == 1 || (smgr->satcalls & (smgr->satcalls - 1))))
    lglsetopt(lgl, "simpdelay", BZLA_LGL_SIMP_DELAY);
  else
    lglsetopt(lgl, "simpdelay", 0);

  if (smgr->inc_required)
  {
    lglsetopt(lgl, "flipping", 0);
    lglsetopt(lgl, "locs", 0);
  }
  else
  {
    lglsetopt(lgl, "clim", -1);
    res = lglsat(lgl);
    return res;
  }

  if (!smgr->fork || (0 <= limit && limit < blgl->blimit))
  {
    if (limit < INT32_MAX) lglsetopt(lgl, "clim", limit);
    res = lglsat(lgl);
  }
  else
  {
    BZLA_MSG(smgr->bzla->msg, 2, "blimit = %d", blgl->blimit);
    lglsetopt(lgl, "clim", blgl->blimit);
    if (!(res = lglsat(lgl)))
    {
      blgl->blimit *= 2;
      if (blgl->blimit > BZLA_LGL_MAX_BLIMIT)
        blgl->blimit = BZLA_LGL_MAX_BLIMIT;

      blgl->nforked++;
      clone = lglclone(lgl);
      lglfixate(clone);
      lglmeltall(clone);
      str = "clone";
      lglsetopt(clone, "clim", limit);
      /* callbacks are not cloned in Lingeling */
      if (smgr->term.fun) lglseterm(clone, smgr->term.fun, smgr->term.state);
      len = strlen(smgr->bzla->msg->prefix) + strlen(str) + 8 + 8;
      BZLA_NEWN(smgr->bzla->mm, name, len);
      snprintf(name,
               len,
               "[%s lgl%s%d] ",
               smgr->bzla->msg->prefix,
               str,
               blgl->nforked);
      lglsetprefix(clone, name);
      BZLA_DELETEN(smgr->bzla->mm, name, len);
      lglsetout(clone, smgr->output);

#ifndef NDEBUG
      res =
#else
      (void)
#endif
          lglsat(clone);
      if (bzla_opt_get(smgr->bzla, BZLA_OPT_VERBOSITY) > 0) lglstats(clone);
      bfres = lglunclone(lgl, clone);
      lglrelease(clone);
      /* it may happen that the lglsat call returns a result sat or unsat,
       * but in lglunclone the terminate callback forces lglunclone to
       * return unknown */
      assert((!res || bfres == res)
             || (bfres != res && smgr->term.fun(smgr->term.state)));
      res = bfres;
    }
    else
    {
      blgl->blimit = 9 * (blgl->blimit / 10);
      if (blgl->blimit < BZLA_LGL_MIN_BLIMIT)
        blgl->blimit = BZLA_LGL_MIN_BLIMIT;
    }
  }
  return res;
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  return lglderef(blgl->lgl, lit);
}

static int32_t
repr(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  return lglrepr(blgl->lgl, lit);
}

static void
reset(BzlaSATMgr *smgr)
{
  BzlaLGL *blgl = smgr->solver;
  lglrelease(blgl->lgl);
  BZLA_DELETE(smgr->bzla->mm, blgl);
}

static void
set_output(BzlaSATMgr *smgr, FILE *output)
{
  BzlaLGL *blgl = smgr->solver;
  lglsetout(blgl->lgl, output);
}

static void
set_prefix(BzlaSATMgr *smgr, const char *prefix)
{
  BzlaLGL *blgl = smgr->solver;
  lglsetprefix(blgl->lgl, prefix);
}

static void
enable_verbosity(BzlaSATMgr *smgr, int32_t level)
{
  BzlaLGL *blgl = smgr->solver;
  if (level <= 0)
    lglsetopt(blgl->lgl, "verbose", -1);
  else if (level >= 2)
    lglsetopt(blgl->lgl, "verbose", level - 1);
}

static int32_t
inc_max_var(BzlaSATMgr *smgr)
{
  BzlaLGL *blgl = smgr->solver;
  int32_t res   = lglincvar(blgl->lgl);
  if (smgr->inc_required) lglfreeze(blgl->lgl, res);
  return res;
}

static void
stats(BzlaSATMgr *smgr)
{
  BzlaLGL *blgl = smgr->solver;
  lglstats(blgl->lgl);
  BZLA_MSG(smgr->bzla->msg, 1, "%d forked", blgl->nforked);
}

/*------------------------------------------------------------------------*/

static void
assume(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  lglassume(blgl->lgl, lit);
}

static void
melt(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  if (smgr->inc_required) lglmelt(blgl->lgl, lit);
}

static int32_t
failed(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  return lglfailed(blgl->lgl, lit);
}

static int32_t
fixed(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaLGL *blgl = smgr->solver;
  return lglfixed(blgl->lgl, lit);
}

static void *
clone(Bzla *bzla, BzlaSATMgr *smgr)
{
  assert(smgr);

  BzlaLGL *res, *blgl;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  blgl = smgr->solver;

  /* not initialized yet */
  if (!blgl) return 0;

  BZLA_CNEW(mm, res);
  res->nforked = blgl->nforked;
  res->blimit  = blgl->blimit;
  res->lgl     = lglmclone(blgl->lgl,
                       mm,
                       (lglalloc) bzla_mem_sat_malloc,
                       (lglrealloc) bzla_mem_sat_realloc,
                       (lgldealloc) bzla_mem_sat_free);
  return res;
}

static void
setterm(BzlaSATMgr *smgr)
{
  assert(smgr);

  BzlaLGL *blgl;
  blgl = smgr->solver;
  lglseterm(blgl->lgl, smgr->term.fun, smgr->term.state);
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_lingeling(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_lingeling'");

  smgr->name = "Lingeling";
  smgr->fork = bzla_opt_get(smgr->bzla, BZLA_OPT_SAT_ENGINE_LGL_FORK);

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.melt             = melt;
  smgr->api.repr             = repr;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = set_output;
  smgr->api.set_prefix       = set_prefix;
  smgr->api.stats            = stats;
  smgr->api.clone            = clone;
  smgr->api.setterm          = setterm;
  return true;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
