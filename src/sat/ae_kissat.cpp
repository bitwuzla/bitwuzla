/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_AE_KISSAT
/*------------------------------------------------------------------------*/

#include "sat/ae_kissat.h"

#include <cassert>

#include "util/exceptions.h"

/*------------------------------------------------------------------------*/

namespace bzla::sat {

/*------------------------------------------------------------------------*/

namespace {
int32_t
kissat_terminate_wrapper(void* state)
{
  bzla::Terminator* terminator = static_cast<bzla::Terminator*>(state);
  return terminator->terminate();
}
}  // namespace

/*------------------------------------------------------------------------*/

AEKissat::AEKissat()
{
  d_solver = kissat_init();
  kissat_set_option(d_solver, "quiet", 1);
}

AEKissat::~AEKissat() { kissat_release(d_solver); }

void
AEKissat::add(int32_t lit)
{
  kissat_add(d_solver, lit);
}

void
AEKissat::assume(int32_t lit)
{
  (void) lit;
  throw Error("Incremental solving not supported in AEKissat");
}

int32_t
AEKissat::value(int32_t lit)
{
  int32_t val = kissat_value(d_solver, lit);
  if (val > 0) return 1;
  if (val < 0) return -1;
  return 0;
}

bool
AEKissat::failed(int32_t lit)
{
  (void) lit;
  throw Error("Incremental solving not supported in AEKissat");
  return false;
}

int32_t
AEKissat::fixed(int32_t lit)
{
  (void) lit;
  throw Error("fixed() not supported in AEKissat");
  return false;
}

Result
AEKissat::solve()
{
  int32_t res = kissat_solve(d_solver);
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
AEKissat::configure_terminator(Terminator* terminator)
{
  if (terminator)
  {
    throw Unsupported("terminator not supported in AEKissat");
    kissat_set_terminate(d_solver, terminator, kissat_terminate_wrapper);
  }
}

const char *
AEKissat::get_version() const
{
  return kissat_version();
}

/*------------------------------------------------------------------------*/

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
