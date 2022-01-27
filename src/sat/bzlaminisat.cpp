/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifdef BZLA_USE_MINISAT

#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS
#endif

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include <cassert>
#include <cstdio>
#include <cstring>

#include "minisat/simp/SimpSolver.h"

extern "C" {

#include "bzlasat.h"
#include "sat/bzlaminisat.h"
#include "utils/bzlaabort.h"

using namespace Minisat;

/*------------------------------------------------------------------------*/

class BzlaMiniSAT : public SimpSolver
{
  vec<Lit> assumptions, clause;
  int32_t szfmap;
  signed char* fmap;
  bool nomodel;
  Lit import(int32_t lit)
  {
    assert(0 < abs(lit) && abs(lit) <= nVars());
    return mkLit(Var(abs(lit) - 1), (lit < 0));
  }

  void reset()
  {
    if (fmap) delete[] fmap, fmap = 0, szfmap = 0;
  }

  void ana()
  {
    fmap = new signed char[szfmap = nVars()];
    memset(fmap, 0, szfmap);
    for (int32_t i = 0; i < conflict.size(); i++)
    {
      int32_t tmp = var(conflict[i]);
      assert(0 <= tmp && tmp < szfmap);
      fmap[tmp] = 1;
    }
  }

 public:
  BzlaMiniSAT() : szfmap(0), fmap(0), nomodel(true) {}

  ~BzlaMiniSAT() { reset(); }

  int32_t inc()
  {
    nomodel     = true;
    int32_t res = newVar();
    assert(0 <= res && res == nVars() - 1);
    return res + 1;
  }

  void assume(int32_t lit)
  {
    nomodel = true;
    assumptions.push(import(lit));
  }

  void add(int32_t lit)
  {
    nomodel = true;
    if (lit)
      clause.push(import(lit));
    else
      addClause(clause), clause.clear();
  }

  unsigned long long calls;

  int32_t sat(bool simp)
  {
    calls++;
    reset();
    lbool res = solveLimited(assumptions, simp);
    assumptions.clear();
    nomodel = res != l_True;
    return res == l_Undef ? 0 : (res == l_True ? 10 : 20);
  }

  int32_t failed(int32_t lit)
  {
    if (!fmap) ana();
    int32_t tmp = var(import(lit));
    assert(0 <= tmp && tmp < nVars());
    return fmap[tmp];
  }

  int32_t fixed(int32_t lit)
  {
    Var v       = var(import(lit));
    int32_t idx = v, res;
    assert(0 <= idx && idx < nVars());
    lbool val = assigns[idx];
    if (val == l_Undef || level(v))
      res = 0;
    else
      res = (val == l_True) ? 1 : -1;
    if (lit < 0) res = -res;
    return res;
  }

  int32_t deref(int32_t lit)
  {
    if (nomodel) return fixed(lit);
    lbool res = modelValue(import(lit));
    return (res == l_True) ? 1 : -1;
  }
};

/*------------------------------------------------------------------------*/

static void*
init(BzlaSATMgr* smgr)
{
  (void) smgr;
  BzlaMiniSAT* res = new BzlaMiniSAT();
  return res;
}

static void
add(BzlaSATMgr* smgr, int32_t lit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  solver->add(lit);
}

static int32_t
sat(BzlaSATMgr* smgr, int32_t limit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  if (limit < 0)
    solver->budgetOff();
  else
    solver->setConfBudget(limit);
  return solver->sat(!smgr->inc_required);
}

static int32_t
deref(BzlaSATMgr* smgr, int32_t lit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  return solver->deref(lit);
}

static void
reset(BzlaSATMgr* smgr)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  delete solver;
}

static int32_t
inc_max_var(BzlaSATMgr* smgr)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  return solver->inc();
}

static void
assume(BzlaSATMgr* smgr, int32_t lit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  solver->assume(lit);
}

static int32_t
fixed(BzlaSATMgr* smgr, int32_t lit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  return solver->fixed(lit);
}

static int32_t
failed(BzlaSATMgr* smgr, int32_t lit)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  return solver->failed(lit);
}

static void
enable_verbosity(BzlaSATMgr* smgr, int32_t level)
{
  (void) smgr;
  if (level >= 2) ((BzlaMiniSAT*) smgr->solver)->verbosity = level - 1;
}

static void
stats(BzlaSATMgr* smgr)
{
  BzlaMiniSAT* solver = (BzlaMiniSAT*) smgr->solver;
  printf(
      "[minisat] calls %llu\n"
      "[minisat] restarts %llu\n"
      "[minisat] conflicts %llu\n"
      "[minisat] decisions %llu\n"
      "[minisat] propagations %llu\n",
      (unsigned long long) solver->calls,
      (unsigned long long) solver->starts,
      (unsigned long long) solver->conflicts,
      (unsigned long long) solver->decisions,
      (unsigned long long) solver->propagations);
  fflush(stdout);
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_minisat(BzlaSATMgr* smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_minisat'");

  smgr->name = "MiniSAT";

  BZLA_CLR(&smgr->api);
  smgr->api.add              = add;
  smgr->api.assume           = assume;
  smgr->api.deref            = deref;
  smgr->api.enable_verbosity = enable_verbosity;
  smgr->api.failed           = failed;
  smgr->api.fixed            = fixed;
  smgr->api.inc_max_var      = inc_max_var;
  smgr->api.init             = init;
  smgr->api.repr             = 0;
  smgr->api.reset            = reset;
  smgr->api.sat              = sat;
  smgr->api.set_output       = 0;
  smgr->api.set_prefix       = 0;
  smgr->api.stats            = stats;
  return true;
}
};
#endif
