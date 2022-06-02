/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "sat/bzlagimsatul.h"

#include "bzlaaig.h"
#include "bzlacore.h"
#include "utils/bzlaabort.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_GIMSATUL
/*------------------------------------------------------------------------*/

#include <gimsatul/clone.h>
#include <gimsatul/detach.h>
#include <gimsatul/options.h>
#include <gimsatul/ruler.h>
#include <gimsatul/simplify.h>
#include <gimsatul/solve.h>
#include <gimsatul/types.h>
#include <gimsatul/witness.h>

struct Gimsatul
{
  struct options options;
  signed char *witness;
  size_t witness_size;
  BzlaIntStack literals;

  size_t max_var;
  uint_least64_t *num_aigs;
  uint_least64_t *num_aig_vars;
};

static void *
init(BzlaSATMgr *smgr)
{
  struct Gimsatul *gim;

  BZLA_NEW(smgr->bzla->mm, gim);
  gim->witness      = 0;
  gim->witness_size = 0;
  gim->max_var      = 0;
  BZLA_INIT_STACK(smgr->bzla->mm, gim->literals);

  BzlaAIGMgr *aigmgr = bzla_get_aig_mgr(smgr->bzla);
  gim->num_aigs      = &aigmgr->max_num_aigs;
  gim->num_aig_vars  = &aigmgr->max_num_aig_vars;

  // Initializes options
  parse_options(1, 0, &gim->options);
  gim->options.threads =
      bzla_opt_get(smgr->bzla, BZLA_OPT_SAT_ENGINE_N_THREADS);
  BZLA_MSG(smgr->bzla->msg, 1, "Configured %u threads", gim->options.threads);

  return gim;
}

#define GIMSATUL_LIT(l) 2 * abs(l) + (l < 0);

static void
add(BzlaSATMgr *smgr, int32_t lit)
{
  // Gimsatul requires the number of total variables when constructed. Hence,
  // we push all literals onto a stack and add the clauses when constructing
  // the solver in sat().
  struct Gimsatul *gim = smgr->solver;
  BZLA_PUSH_STACK(gim->literals, lit);
  if (abs(lit) > gim->max_var)
  {
    gim->max_var = abs(lit);
  }
}

static int32_t
sat(BzlaSATMgr *smgr, int32_t limit)
{
  (void) limit;
  struct Gimsatul *gim = smgr->solver;
  struct ruler *ruler  = new_ruler(gim->max_var + 1, &gim->options);

  // Add all clauses to Gimsatul.
  struct unsigneds clause;
  INIT(clause);
  int32_t lit;
  for (size_t i = 0; i < BZLA_COUNT_STACK(gim->literals); ++i)
  {
    lit = BZLA_PEEK_STACK(gim->literals, i);
    if (lit == 0)
    {
      size_t size = SIZE(clause);
      assert(size);
      unsigned *literals = clause.begin;
      if (size == 1)
      {
        const signed char value = ruler->values[literals[0]];
        if (value < 0)
        {
          assert(!ruler->inconsistent);
          ruler->inconsistent = true;
        }
        else if (!value)
        {
          assign_ruler_unit(ruler, literals[0]);
        }
      }
      else if (size == 2)
      {
        new_ruler_binary_clause(ruler, literals[0], literals[1]);
      }
      else
      {
        struct clause *large_clause =
            new_large_clause(size, literals, false, 0);
        PUSH(ruler->clauses, large_clause);
      }
      CLEAR(clause);
    }
    else
    {
      unsigned unsigned_lit = GIMSATUL_LIT(lit);
      PUSH(clause, unsigned_lit);
    }
  }
  assert(SIZE(clause) == 0);
  BZLA_RESET_STACK(gim->literals);
  RELEASE(clause);
  simplify_ruler(ruler);
  clone_rings(ruler);
  struct ring *winner = solve_rings(ruler);
  int res             = winner ? winner->status : 0;
  if (res == 10)
  {
    if (gim->witness)
    {
      free(gim->witness);
    }
    gim->witness      = extend_witness(winner);
    gim->witness_size = ruler->size;
  }
  detach_and_delete_rings(ruler);
  delete_ruler(ruler);
  return res;
}

static int32_t
deref(BzlaSATMgr *smgr, int32_t lit)
{
  struct Gimsatul *gim = smgr->solver;
  assert(gim->witness);
  unsigned unsigned_lit = GIMSATUL_LIT(lit);
  assert(unsigned_lit < gim->witness_size);
  return gim->witness[unsigned_lit];
}

static void
reset(BzlaSATMgr *smgr)
{
  struct Gimsatul *gim = smgr->solver;
  if (gim->witness)
  {
    free(gim->witness);
    gim->witness = 0;
  }
  BZLA_RELEASE_STACK(gim->literals);
  BZLA_DELETE(smgr->bzla->mm, gim);
  smgr->solver = 0;
}

/*------------------------------------------------------------------------*/

bool
bzla_sat_enable_gimsatul(BzlaSATMgr *smgr)
{
  assert(smgr != NULL);

  BZLA_ABORT(smgr->initialized,
             "'bzla_sat_init' called before 'bzla_sat_enable_gimsatul'");

  smgr->name = "Gimsatul";

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
