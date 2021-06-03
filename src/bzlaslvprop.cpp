/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

extern "C" {
#include "bzlaslvprop.h"

#include "bzlacore.h"
#include "bzlamsg.h"
}

#include <memory>

#include "bzlals.h"
#include "gmpmpz.h"
#include "gmprandstate.h"
#include "rng.h"

namespace bzla {
namespace prop {

class PropSolverState
{
 public:
  PropSolverState(Bzla *bzla, uint32_t max_nprops, uint32_t seed) : d_bzla(bzla)
  {
    d_bzlals.reset(new bzlals::BzlaLs(max_nprops, seed));
  }

 private:
  Bzla *d_bzla;
  std::unique_ptr<bzlals::BzlaLs> d_bzlals;
};

}  // namespace prop
}  // namespace bzla

struct BzlaPropSolver
{
  BZLA_SOLVER_STRUCT;
  std::unique_ptr<bzla::prop::PropSolverState> d_state;
};

namespace {

BzlaSolverResult
check_sat_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  BzlaSolverResult sat_result;
  Bzla *bzla = slv->bzla;
  assert(!bzla->inconsistent);

  if (bzla_terminate(bzla))
  {
    sat_result = BZLA_RESULT_UNKNOWN;
    goto DONE;
  }

  // TODO
  sat_result = BZLA_RESULT_SAT;
  // sat_result = bzla_prop_solver_sat(bzla);
DONE:
  return sat_result;
}

BzlaPropSolver *
clone_prop_solver(Bzla *clone, Bzla *bzla, BzlaNodeMap *exp_map)
{
  (void) clone;
  (void) bzla;
  (void) exp_map;
  return nullptr;
}

void
delete_prop_solver(BzlaPropSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_PROP_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla = slv->bzla;
  delete slv;
  bzla->slv = nullptr;
}

void
generate_model_prop_solver(BzlaPropSolver *slv,
                           bool model_for_all_nodes,
                           bool reset)
{
}

void
print_stats_prop_solver(BzlaPropSolver *slv)
{
  // TODO
}

void
print_time_stats_prop_solver(BzlaPropSolver *slv)
{
  // TODO
}

void
print_model_prop_solver(BzlaPropSolver *slv, const char *format, FILE *file)
{
  // TODO
}
}  // namespace

BzlaSolver *
bzla_new_prop_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaPropSolver *slv = new BzlaPropSolver();
  // TODO: max_nprops, seed
  slv->d_state.reset(new bzla::prop::PropSolverState(bzla, 0, 0));
  slv->kind      = BZLA_PROP_SOLVER_KIND;
  slv->bzla      = bzla;
  slv->api.clone = (BzlaSolverClone) clone_prop_solver;
  slv->api.delet = (BzlaSolverDelete) delete_prop_solver;
  slv->api.sat   = (BzlaSolverSat) check_sat_prop_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_prop_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_prop_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_prop_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_prop_solver;

  BZLA_MSG(bzla->msg, 1, "enabled prop engine");

  return (BzlaSolver *) slv;
}
