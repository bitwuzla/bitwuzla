/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasat.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdlib.h>

#include "bzlaconfig.h"
#include "bzlacore.h"
#include "sat/bzlacadical.h"
#include "sat/bzlacms.h"
#include "sat/bzlagimsatul.h"
#include "sat/bzlakissat.h"
#include "sat/bzlalgl.h"
#include "sat/bzlaminisat.h"
#include "sat/bzlapicosat.h"
#include "utils/bzlaabort.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#if !defined(BZLA_USE_LINGELING) && !defined(BZLA_USE_PICOSAT)  \
    && !defined(BZLA_USE_MINISAT) && !defined(BZLA_USE_CADICAL) \
    && !defined(BZLA_USE_CMS) && !defined(BZLA_USE_KISSAT)      \
    && !defined(BZLA_USE_GIMSATUL)
#error "no SAT solver configured"
#endif

static bool enable_dimacs_printer(BzlaSATMgr *smgr);

/*------------------------------------------------------------------------*/
/* wrapper functions for SAT solver API                                   */
/*------------------------------------------------------------------------*/

static inline void
add(BzlaSATMgr *smgr, int32_t lit)
{
  assert(smgr->api.add);
  smgr->api.add(smgr, lit);
}

static inline void
assume(BzlaSATMgr *smgr, int32_t lit)
{
  BZLA_ABORT(!smgr->api.assume,
             "SAT solver %s does not support 'assume' API call",
             smgr->name);
  smgr->api.assume(smgr, lit);
}

static inline void *
clone(Bzla *bzla, BzlaSATMgr *smgr)
{
  BZLA_ABORT(!smgr->api.clone,
             "SAT solver %s does not support 'clone' API call",
             smgr->name);
  return smgr->api.clone(bzla, smgr);
}

static inline int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  assert(smgr->api.deref);
  return smgr->api.deref(smgr, lit);
}

static inline void
enable_verbosity(BzlaSATMgr *smgr, int32_t level)
{
  if (smgr->api.enable_verbosity) smgr->api.enable_verbosity(smgr, level);
}

static inline int32_t
failed(BzlaSATMgr *smgr, int32_t lit)
{
  BZLA_ABORT(!smgr->api.failed,
             "SAT solver %s does not support 'failed' API call",
             smgr->name);
  return smgr->api.failed(smgr, lit);
}

static inline int32_t
fixed(BzlaSATMgr *smgr, int32_t lit)
{
  if (smgr->api.fixed) return smgr->api.fixed(smgr, lit);
  return 0;
}

static inline int32_t
inc_max_var(BzlaSATMgr *smgr)
{
  if (smgr->api.inc_max_var) return smgr->api.inc_max_var(smgr);
  return smgr->maxvar + 1;
}

static inline void *
init(BzlaSATMgr *smgr)
{
  assert(smgr->api.init);
  return smgr->api.init(smgr);
}

static inline void
melt(BzlaSATMgr *smgr, int32_t lit)
{
  if (smgr->api.melt) smgr->api.melt(smgr, lit);
  // TODO: else case warning?
}

static inline int32_t
repr(BzlaSATMgr *smgr, int32_t lit)
{
  if (smgr->api.repr) return smgr->api.repr(smgr, lit);
  return lit;
}

static inline void
reset(BzlaSATMgr *smgr)
{
  assert(smgr->api.reset);
  smgr->api.reset(smgr);
}

static inline int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  assert(smgr->api.sat);
  return smgr->api.sat(smgr, limit);
}

static inline void
set_output(BzlaSATMgr *smgr, FILE *output)
{
  if (smgr->api.set_output) smgr->api.set_output(smgr, output);
}

static inline void
set_prefix(BzlaSATMgr *smgr, const char *prefix)
{
  if (smgr->api.set_prefix) smgr->api.set_prefix(smgr, prefix);
}

static inline void
setterm(BzlaSATMgr *smgr)
{
  if (smgr->api.setterm) smgr->api.setterm(smgr);
}

static inline void
stats(BzlaSATMgr *smgr)
{
  if (smgr->api.stats) smgr->api.stats(smgr);
}

/*------------------------------------------------------------------------*/

BzlaSATMgr *
bzla_sat_mgr_new(Bzla *bzla)
{
  assert(bzla);

  BzlaSATMgr *smgr;

  BZLA_CNEW(bzla->mm, smgr);
  smgr->bzla   = bzla;
  smgr->output = stdout;
  return smgr;
}

bool
bzla_sat_mgr_has_clone_support(const BzlaSATMgr *smgr)
{
  if (!smgr) return true;
  return smgr->api.clone != 0;
}

bool
bzla_sat_mgr_has_incremental_support(const BzlaSATMgr *smgr)
{
  if (!smgr) return false;
  return smgr->api.assume != 0 && smgr->api.failed != 0;
}

void
bzla_sat_mgr_set_term(BzlaSATMgr *smgr, int32_t (*fun)(void *), void *state)
{
  assert(smgr);
  smgr->term.fun   = fun;
  smgr->term.state = state;
}

// FIXME log output handling, in particular: sat manager name output
// (see lingeling_sat) should be unique, which is not the case for
// clones
BzlaSATMgr *
bzla_sat_mgr_clone(Bzla *bzla, BzlaSATMgr *smgr)
{
  assert(bzla);
  assert(smgr);

  BzlaSATMgr *res;
  BzlaMemMgr *mm;

  BZLA_ABORT(!bzla_sat_mgr_has_clone_support(smgr),
             "SAT solver does not support cloning");

  mm = bzla->mm;
  BZLA_NEW(mm, res);
  res->solver = clone(bzla, smgr);
  res->bzla   = bzla;
  assert(mm->sat_allocated == smgr->bzla->mm->sat_allocated);
  res->name = smgr->name;
  memcpy(&res->inc_required,
         &smgr->inc_required,
         (char *) smgr + sizeof(*smgr) - (char *) &smgr->inc_required);
  BZLA_CLR(&res->term);
  return res;
}

bool
bzla_sat_is_initialized(BzlaSATMgr *smgr)
{
  assert(smgr);
  return smgr->initialized;
}

int32_t
bzla_sat_mgr_next_cnf_id(BzlaSATMgr *smgr)
{
  int32_t result;
  assert(smgr);
  assert(smgr->initialized);
  result = inc_max_var(smgr);
  if (abs(result) > smgr->maxvar) smgr->maxvar = abs(result);
  BZLA_ABORT(result <= 0, "CNF id overflow");
  if (bzla_opt_get(smgr->bzla, BZLA_OPT_VERBOSITY) > 2 && !(result % 100000))
    BZLA_MSG(smgr->bzla->msg, 2, "reached CNF id %d", result);
  return result;
}

void
bzla_sat_mgr_release_cnf_id(BzlaSATMgr *smgr, int32_t lit)
{
  assert(smgr);
  if (!smgr->initialized) return;
  assert(abs(lit) <= smgr->maxvar);
  if (abs(lit) == smgr->true_lit) return;
  melt(smgr, lit);
}

void
bzla_sat_mgr_delete(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);
  /* if SAT is still initialized, then
   * reset_sat has not been called
   */
  if (smgr->initialized) bzla_sat_reset(smgr);
  BZLA_DELETE(smgr->bzla->mm, smgr);
}

/*------------------------------------------------------------------------*/

void
bzla_sat_set_output(BzlaSATMgr *smgr, FILE *output)
{
  char *prefix, *q;
  const char *p;

  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(output != NULL);
  (void) smgr;
  set_output(smgr, output);
  smgr->output = output;

  prefix = bzla_mem_malloc(smgr->bzla->mm, strlen(smgr->name) + 4);
  sprintf(prefix, "[%s] ", smgr->name);
  q = prefix + 1;
  for (p = smgr->name; *p; p++) *q++ = tolower((int32_t) *p);
  set_prefix(smgr, prefix);
  bzla_mem_free(smgr->bzla->mm, prefix, strlen(smgr->name) + 4);
}

void
bzla_sat_enable_solver(BzlaSATMgr *smgr)
{
  assert(smgr);

  uint32_t opt;

  opt = bzla_opt_get(smgr->bzla, BZLA_OPT_SAT_ENGINE);
  switch (opt)
  {
#ifdef BZLA_USE_LINGELING
    case BZLA_SAT_ENGINE_LINGELING: bzla_sat_enable_lingeling(smgr); break;
#endif
#ifdef BZLA_USE_PICOSAT
    case BZLA_SAT_ENGINE_PICOSAT: bzla_sat_enable_picosat(smgr); break;
#endif
#ifdef BZLA_USE_KISSAT
    case BZLA_SAT_ENGINE_KISSAT: bzla_sat_enable_kissat(smgr); break;
#endif
#ifdef BZLA_USE_MINISAT
    case BZLA_SAT_ENGINE_MINISAT: bzla_sat_enable_minisat(smgr); break;
#endif
#ifdef BZLA_USE_CADICAL
    case BZLA_SAT_ENGINE_CADICAL: bzla_sat_enable_cadical(smgr); break;
#endif
#ifdef BZLA_USE_CMS
    case BZLA_SAT_ENGINE_CMS: bzla_sat_enable_cms(smgr); break;
#endif
#ifdef BZLA_USE_GIMSATUL
    case BZLA_SAT_ENGINE_GIMSATUL: bzla_sat_enable_gimsatul(smgr); break;
#endif
    default: BZLA_ABORT(1, "no sat solver configured");
  }

  BZLA_MSG(smgr->bzla->msg,
           1,
           "%s allows %snon-incremental mode",
           smgr->name,
           smgr->api.assume ? "both incremental and " : "");

  if (bzla_opt_get(smgr->bzla, BZLA_OPT_PRINT_DIMACS))
  {
    enable_dimacs_printer(smgr);
  }
}

static void
init_flags(BzlaSATMgr *smgr)
{
  assert(smgr);
  smgr->initialized  = true;
  smgr->inc_required = true;
  smgr->sat_time     = 0;
}

void
bzla_sat_init(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);
  assert(!smgr->initialized);
  BZLA_MSG(smgr->bzla->msg, 1, "initialized %s", smgr->name);

  init_flags(smgr);

  smgr->solver = init(smgr);
  enable_verbosity(smgr, bzla_opt_get(smgr->bzla, BZLA_OPT_VERBOSITY));

  /* Set terminate callbacks if SAT solver supports it */
  if (smgr->term.fun && smgr->api.setterm)
  {
    setterm(smgr);
  }

  smgr->true_lit = bzla_sat_mgr_next_cnf_id(smgr);
  bzla_sat_add(smgr, smgr->true_lit);
  bzla_sat_add(smgr, 0);
  bzla_sat_set_output(smgr, stdout);
}

void
bzla_sat_print_stats(BzlaSATMgr *smgr)
{
  if (!smgr || !smgr->initialized) return;
  stats(smgr);
  BZLA_MSG(smgr->bzla->msg,
           1,
           "%d SAT calls in %.1f seconds",
           smgr->satcalls,
           smgr->sat_time);
}

void
bzla_sat_add(BzlaSATMgr *smgr, int32_t lit)
{
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  assert(!smgr->satcalls || smgr->inc_required);
  if (!lit) smgr->clauses++;
  add(smgr, lit);
}

BzlaSolverResult
bzla_sat_check_sat(BzlaSATMgr *smgr, int32_t limit)
{
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(!smgr->inc_required || bzla_sat_mgr_has_incremental_support(smgr));

  double start = bzla_util_time_stamp();
  int32_t sat_res;
  BzlaSolverResult res;
  BZLA_MSG(smgr->bzla->msg,
           2,
           "calling SAT solver %s with limit %d",
           smgr->name,
           limit);
  assert(!smgr->satcalls || smgr->inc_required);
  smgr->satcalls++;
  setterm(smgr);
  sat_res = sat(smgr, limit);
  smgr->sat_time += bzla_util_time_stamp() - start;
  switch (sat_res)
  {
    case 10: res = BZLA_RESULT_SAT; break;
    case 20: res = BZLA_RESULT_UNSAT; break;
    default: assert(sat_res == 0); res = BZLA_RESULT_UNKNOWN;
  }
  return res;
}

int32_t
bzla_sat_deref(BzlaSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  return deref(smgr, lit);
}

int32_t
bzla_sat_repr(BzlaSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  return repr(smgr, lit);
}

void
bzla_sat_reset(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);
  assert(smgr->initialized);
  BZLA_MSG(smgr->bzla->msg, 2, "resetting %s", smgr->name);
  reset(smgr);
  smgr->solver      = 0;
  smgr->initialized = false;
}

int32_t
bzla_sat_fixed(BzlaSATMgr *smgr, int32_t lit)
{
  int32_t res;
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  res = fixed(smgr, lit);
  return res;
}

/*------------------------------------------------------------------------*/

void
bzla_sat_assume(BzlaSATMgr *smgr, int32_t lit)
{
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  assert(!smgr->satcalls || smgr->inc_required);
  assume(smgr, lit);
}

int32_t
bzla_sat_failed(BzlaSATMgr *smgr, int32_t lit)
{
  (void) smgr;
  assert(smgr != NULL);
  assert(smgr->initialized);
  assert(abs(lit) <= smgr->maxvar);
  return failed(smgr, lit);
}

/*------------------------------------------------------------------------*/
/* DIMACS printer                                                         */
/*------------------------------------------------------------------------*/

static void *
dimacs_printer_init(BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer  = (BzlaCnfPrinter *) smgr->solver;
  BzlaSATMgr *wrapped_smgr = printer->smgr;

  BZLA_INIT_STACK(smgr->bzla->mm, printer->clauses);
  BZLA_INIT_STACK(smgr->bzla->mm, printer->assumptions);
  printer->out = stdout;

  /* Note: We need to explicitly do the initialization steps for 'wrapped_smgr'
   * here instead of calling bzla_sat_init on 'wrapped_smgr'. Otherwise, not all
   * information is recorded correctly. */
  BZLA_MSG(smgr->bzla->msg, 1, "initialized %s", wrapped_smgr->name);
  init_flags(wrapped_smgr);
  wrapped_smgr->solver = wrapped_smgr->api.init(wrapped_smgr);

  return printer;
}

static void
dimacs_printer_add(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  BZLA_PUSH_STACK(printer->clauses, lit);
  add(printer->smgr, lit);
}

static void
dimacs_printer_assume(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  BZLA_PUSH_STACK(printer->assumptions, lit);
  assume(printer->smgr, lit);
}

static int32_t
dimacs_printer_deref(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  return deref(printer->smgr, lit);
}

static int32_t
dimacs_printer_repr(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  return repr(printer->smgr, lit);
}

static void
dimacs_printer_enable_verbosity(BzlaSATMgr *smgr, int32_t level)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  return enable_verbosity(printer->smgr, level);
}

static int32_t
dimacs_printer_failed(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  return failed(printer->smgr, lit);
}

static int32_t
dimacs_printer_fixed(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  return fixed(printer->smgr, lit);
}

static void
dimacs_printer_reset(BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer  = (BzlaCnfPrinter *) smgr->solver;
  BzlaSATMgr *wrapped_smgr = printer->smgr;

  reset(wrapped_smgr);

  BZLA_DELETE(smgr->bzla->mm, wrapped_smgr);
  BZLA_RELEASE_STACK(printer->clauses);
  BZLA_RELEASE_STACK(printer->assumptions);
  BZLA_DELETE(smgr->bzla->mm, printer);
  smgr->solver = 0;
}

static void
print_dimacs(BzlaSATMgr *smgr)
{
  int32_t lit;
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;

  /* Print CNF in DIMACS format. */
  fprintf(printer->out, "c CNF dump %u start\n", smgr->satcalls);
  fprintf(printer->out, "c Bitwuzla version %s\n", BZLA_GIT_ID);
  fprintf(printer->out, "p cnf %u %u\n", smgr->maxvar, smgr->clauses);

  /* Print clauses */
  for (size_t i = 0; i < BZLA_COUNT_STACK(printer->clauses); i++)
  {
    lit = BZLA_PEEK_STACK(printer->clauses, i);
    if (lit)
      printf("%d ", lit);
    else
      printf("%d\n", lit);
  }

  /* Print assumptions */
  if (!BZLA_EMPTY_STACK(printer->assumptions))
  {
    fprintf(printer->out, "c assumptions\n");
    for (size_t i = 0; i < BZLA_COUNT_STACK(printer->assumptions); i++)
    {
      lit = BZLA_PEEK_STACK(printer->assumptions, i);
      fprintf(printer->out, "%d\n", lit);
    }
  }
  fprintf(printer->out, "c CNF dump %u end\n", smgr->satcalls);
}

static int32_t
dimacs_printer_sat(BzlaSATMgr *smgr, int32_t limit)
{
  BzlaCnfPrinter *printer  = (BzlaCnfPrinter *) smgr->solver;
  BzlaSATMgr *wrapped_smgr = printer->smgr;

  print_dimacs(smgr);

  wrapped_smgr->inc_required = smgr->inc_required;
  wrapped_smgr->satcalls     = smgr->satcalls;

  /* If incremental is disabled, we only print the CNF and return unknown. */
  return smgr->inc_required ? sat(wrapped_smgr, limit) : 0;
}

static void
dimacs_printer_set_output(BzlaSATMgr *smgr, FILE *output)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  printer->out            = output;
  set_output(printer->smgr, output);
}

static void
dimacs_printer_set_prefix(BzlaSATMgr *smgr, const char *prefix)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  set_prefix(printer->smgr, prefix);
}

static void
dimacs_printer_stats(BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  stats(printer->smgr);
}

static void
clone_int_stack(BzlaMemMgr *mm, BzlaIntStack *clone, BzlaIntStack *stack)
{
  size_t size = BZLA_SIZE_STACK(*stack);
  size_t cnt  = BZLA_COUNT_STACK(*stack);

  BZLA_INIT_STACK(mm, *clone);
  if (size)
  {
    BZLA_CNEWN(mm, clone->start, size);
    clone->end = clone->start + size;
    clone->top = clone->start + cnt;
    memcpy(clone->start, stack->start, cnt * sizeof(int32_t));
  }
}

static void *
dimacs_printer_clone(Bzla *bzla, BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer, *printer_clone;
  BzlaMemMgr *mm;

  mm      = bzla->mm;
  printer = (BzlaCnfPrinter *) smgr->solver;

  BZLA_CNEW(mm, printer_clone);
  clone_int_stack(mm, &printer_clone->assumptions, &printer->assumptions);
  clone_int_stack(mm, &printer_clone->clauses, &printer->clauses);
  printer_clone->out  = printer->out;
  printer_clone->smgr = bzla_sat_mgr_clone(bzla, printer->smgr);

  return printer_clone;
}

static void
dimacs_printer_setterm(BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer = (BzlaCnfPrinter *) smgr->solver;
  setterm(printer->smgr);
}

static int32_t
dimacs_printer_inc_max_var(BzlaSATMgr *smgr)
{
  BzlaCnfPrinter *printer    = (BzlaCnfPrinter *) smgr->solver;
  BzlaSATMgr *wrapped_smgr   = printer->smgr;
  wrapped_smgr->inc_required = smgr->inc_required;
  wrapped_smgr->maxvar       = smgr->maxvar;
  return inc_max_var(wrapped_smgr);
}

static void
dimacs_printer_melt(BzlaSATMgr *smgr, int32_t lit)
{
  BzlaCnfPrinter *printer    = (BzlaCnfPrinter *) smgr->solver;
  BzlaSATMgr *wrapped_smgr   = printer->smgr;
  wrapped_smgr->inc_required = smgr->inc_required;
  melt(wrapped_smgr, lit);
}

/*------------------------------------------------------------------------*/

/* The DIMACS printer is a SAT manager that wraps the currently configured SAT
 * mangager. It records the CNF sent to the SAT solver and forwards all API
 * calls to the wrapped SAT manager. The DIMACS printer assumes a SAT solver
 * was already enabled. */
static bool
enable_dimacs_printer(BzlaSATMgr *smgr)
{
  assert(smgr);
  assert(smgr->name);

  BzlaCnfPrinter *printer;

  /* Initialize printer and copy current SAT manager. */
  BZLA_CNEW(smgr->bzla->mm, printer);
  BZLA_CNEW(smgr->bzla->mm, printer->smgr);
  memcpy(printer->smgr, smgr, sizeof(BzlaSATMgr));

  /* Clear API */
  memset(&smgr->api, 0, sizeof(smgr->api));

  smgr->solver               = printer;
  smgr->name                 = "DIMACS Printer";
  smgr->api.add              = dimacs_printer_add;
  smgr->api.deref            = dimacs_printer_deref;
  smgr->api.enable_verbosity = dimacs_printer_enable_verbosity;
  smgr->api.fixed            = dimacs_printer_fixed;
  smgr->api.inc_max_var      = dimacs_printer_inc_max_var;
  smgr->api.init             = dimacs_printer_init;
  smgr->api.melt             = dimacs_printer_melt;
  smgr->api.repr             = dimacs_printer_repr;
  smgr->api.reset            = dimacs_printer_reset;
  smgr->api.sat              = dimacs_printer_sat;
  smgr->api.set_output       = dimacs_printer_set_output;
  smgr->api.set_prefix       = dimacs_printer_set_prefix;
  smgr->api.stats            = dimacs_printer_stats;
  smgr->api.setterm          = dimacs_printer_setterm;

  /* These function are used in bzla_sat_mgr_has_* testers and should only be
   * set if the underlying SAT solver also has support for it. */
  smgr->api.assume = printer->smgr->api.assume ? dimacs_printer_assume : 0;
  smgr->api.failed = printer->smgr->api.failed ? dimacs_printer_failed : 0;
  smgr->api.clone  = printer->smgr->api.clone ? dimacs_printer_clone : 0;

  return true;
}
