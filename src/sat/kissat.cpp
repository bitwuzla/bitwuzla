/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "sat/kissat.h"

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

Kissat::Kissat() { init(); }

Kissat::~Kissat() { kissat_release(d_solver); }

void
Kissat::add(int32_t lit)
{
  d_literals.push_back(lit);
}

void
Kissat::assume(int32_t lit)
{
  d_assumptions.push_back(lit);
}

int32_t
Kissat::value(int32_t lit)
{
  int32_t val = kissat_value(d_solver, lit);
  if (val > 0) return 1;
  if (val < 0) return -1;
  return 0;
}

bool
Kissat::failed(int32_t lit)
{
  (void) lit;
  throw Error("Incremental solving not supported in Kissat");
  return false;
}

int32_t
Kissat::fixed(int32_t lit)
{
  (void) lit;
  throw Error("fixed() not supported in Kissat");
  return false;
}

Result
Kissat::solve()
{
  if (d_init)
  {
    init();
  }
  size_t size_before_assumptions = d_literals.size();

  for (const auto a : d_assumptions)
  {
    d_literals.push_back(a);
    d_literals.push_back(0);
  }
  d_assumptions.clear();

  for (const auto& lit : d_literals)
  {
    kissat_add(d_solver, lit);
  }

  d_literals.resize(size_before_assumptions);
  int32_t res = kissat_solve(d_solver);
  d_init      = true;
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
Kissat::configure_terminator(Terminator* terminator)
{
  if (terminator)
  {
    throw Unsupported("terminator not supported in Kissat");
    kissat_set_terminate(d_solver, terminator, kissat_terminate_wrapper);
  }
}

const char *
Kissat::get_version() const
{
  return kissat_version();
}

void
Kissat::init()
{
  if (d_solver)
  {
    kissat_release(d_solver);
  }
  d_solver = kissat_init();
  kissat_set_option(d_solver, "quiet", 1);
  d_init = false;
}

/*------------------------------------------------------------------------*/

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
