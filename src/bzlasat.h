/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASAT_H_INCLUDED
#define BZLASAT_H_INCLUDED

#include <stdbool.h>
#include <stdio.h>

#include "bzlaslv.h"
#include "bzlatypes.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaSATMgr BzlaSATMgr;

struct BzlaSATMgr
{
  /* Note: direct solver reference for PicoSAT, wrapper object for for
   *	   Lingeling (BzlaLGL) and MiniSAT (BzlaMiniSAT). */
  void *solver;
  Bzla *bzla;

  const char *name; /* solver name */

  /* Note: do not change order! (bzla_sat_mgr_clone relies on inc_required
   * to come first of all fields following below.) */
  bool inc_required;
#ifdef BZLA_USE_LINGELING
  bool fork;
#endif
  FILE *output;

  bool initialized;
  int32_t satcalls;
  int32_t clauses;
  int32_t true_lit;
  int32_t maxvar;

  double sat_time;

  struct
  {
    int32_t (*fun)(void *); /* termination callback */
    void *state;
  } term;

  bool have_restore;
  struct
  {
    void (*add)(BzlaSATMgr *, int32_t); /* required */
    void (*assume)(BzlaSATMgr *, int32_t);
    int32_t (*deref)(BzlaSATMgr *, int32_t); /* required */
    void (*enable_verbosity)(BzlaSATMgr *, int32_t);
    int32_t (*failed)(BzlaSATMgr *, int32_t);
    int32_t (*fixed)(BzlaSATMgr *, int32_t);
    int32_t (*inc_max_var)(BzlaSATMgr *);
    void *(*init)(BzlaSATMgr *); /* required */
    void (*melt)(BzlaSATMgr *, int32_t);
    int32_t (*repr)(BzlaSATMgr *, int32_t);
    void (*reset)(BzlaSATMgr *);           /* required */
    int32_t (*sat)(BzlaSATMgr *, int32_t); /* required */
    void (*set_output)(BzlaSATMgr *, FILE *);
    void (*set_prefix)(BzlaSATMgr *, const char *);
    void (*stats)(BzlaSATMgr *);
    void *(*clone)(Bzla *bzla, BzlaSATMgr *);
    void (*setterm)(BzlaSATMgr *);
  } api;
};

/*------------------------------------------------------------------------*/

struct BzlaCnfPrinter
{
  FILE *out;
  BzlaIntStack clauses;
  BzlaIntStack assumptions;
  BzlaSATMgr *smgr; /* SAT manager wrapped by DIMACS printer. */
};

typedef struct BzlaCnfPrinter BzlaCnfPrinter;

/*------------------------------------------------------------------------*/

/* Creates new SAT manager.
 * A SAT manager is used by nearly all functions of the SAT layer.
 */
BzlaSATMgr *bzla_sat_mgr_new(Bzla *bzla);

bool bzla_sat_mgr_has_clone_support(const BzlaSATMgr *smgr);

bool bzla_sat_mgr_has_incremental_support(const BzlaSATMgr *smgr);

void bzla_sat_mgr_set_term(BzlaSATMgr *smgr,
                           int32_t (*fun)(void *),
                           void *state);

/* Clones existing SAT manager (and underlying SAT solver). */
BzlaSATMgr *bzla_sat_mgr_clone(Bzla *bzla, BzlaSATMgr *smgr);

/* Deletes SAT manager from memory. */
void bzla_sat_mgr_delete(BzlaSATMgr *smgr);

/* Generates fresh CNF indices.
 * Indices are generated in consecutive order. */
int32_t bzla_sat_mgr_next_cnf_id(BzlaSATMgr *smgr);

/* Mark old CNF index as not used anymore. */
void bzla_sat_mgr_release_cnf_id(BzlaSATMgr *smgr, int32_t);

#if 0
/* Returns the last CNF index that has been generated. */
int32_t bzla_get_last_cnf_id_sat_mgr (BzlaSATMgr * smgr);
#endif

void bzla_sat_enable_solver(BzlaSATMgr *smgr);

/* Inits the SAT solver. */
void bzla_sat_init(BzlaSATMgr *smgr);

/* Returns if the SAT solver has already been initialized */
bool bzla_sat_is_initialized(BzlaSATMgr *smgr);

/* Sets the output file of the SAT solver. */
void bzla_sat_set_output(BzlaSATMgr *smgr, FILE *output);

/* Prints statistics of SAT solver. */
void bzla_sat_print_stats(BzlaSATMgr *smgr);

/* Adds literal to the current clause of the SAT solver.
 * 0 terminates the current clause.
 */
void bzla_sat_add(BzlaSATMgr *smgr, int32_t lit);

/* Adds assumption to SAT solver.
 * Requires that SAT solver supports this.
 */
void bzla_sat_assume(BzlaSATMgr *smgr, int32_t lit);

/* Checks whether an assumption failed during
 * the last SAT solver call 'bzla_sat_check_sat'.
 */
int32_t bzla_sat_failed(BzlaSATMgr *smgr, int32_t lit);

/* Solves the SAT instance.
 * limit < 0 -> no limit.
 */
BzlaSolverResult bzla_sat_check_sat(BzlaSATMgr *smgr, int32_t limit);

/* Gets assignment of a literal (in the SAT case).
 * Do not call before calling bzla_sat_check_sat.
 */
int32_t bzla_sat_deref(BzlaSATMgr *smgr, int32_t lit);

/* Gets equivalence class represenative of a literal
 * or the literal itself if it is in a singleton
 * equivalence, fixed or eliminated.
 * Do not call before calling bzla_sat_check_sat.
 */
int32_t bzla_sat_repr(BzlaSATMgr *smgr, int32_t lit);

/* Gets assignment of a literal (in the SAT case)
 * similar to 'deref', but only consider top level.
 * Do not call before calling bzla_sat_check_sat.
 */
int32_t bzla_sat_fixed(BzlaSATMgr *smgr, int32_t lit);

/* Resets the status of the SAT solver. */
void bzla_sat_reset(BzlaSATMgr *smgr);

#endif
