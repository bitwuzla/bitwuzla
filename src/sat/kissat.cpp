/*------------------------------------------------------------------------*/
#ifdef BZLA_USE_KISSAT
/*------------------------------------------------------------------------*/

#include "sat/kissat.h"

#include <cassert>

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

Kissat::Kissat() { d_solver = kissat_init(); }

Kissat::~Kissat() { kissat_release(d_solver); }

void
Kissat::add(int32_t lit)
{
  kissat_add(d_solver, lit);
}

void
Kissat::assume(int32_t lit)
{
  (void) lit;
  assert(false);
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
  assert(false);
}

int32_t
Kissat::fixed(int32_t lit)
{
  (void) lit;
  assert(false);
}

Result
Kissat::solve()
{
  int32_t res = kissat_solve(d_solver);
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
Kissat::configure_terminator(Terminator* terminator)
{
  if (terminator)
  {
    kissat_set_terminate(d_solver, terminator, kissat_terminate_wrapper);
  }
}

const char *
Kissat::get_version() const
{
  return kissat_version();
}

/*------------------------------------------------------------------------*/

}  // namespace bzla::sat

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
