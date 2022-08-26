#include "sat/cadical.h"

namespace bzla::sat {

Cadical::Cadical()
{
  d_solver.reset(new CaDiCaL::Solver());
  d_solver->set("shrink", 0);
  d_solver->set("quiet", 1);
}

void
Cadical::add(int32_t lit)
{
  d_solver->add(lit);
}

void
Cadical::assume(int32_t lit)
{
  d_solver->assume(lit);
}

int32_t
Cadical::value(int32_t lit)
{
  int32_t val = d_solver->val(lit);
  if (val > 0) return 1;
  if (val < 0) return -1;
  return 0;
}

bool
Cadical::failed(int32_t lit)
{
  return d_solver->failed(lit);
}

int32_t
Cadical::fixed(int32_t lit)
{
  return d_solver->fixed(lit);
}

SatSolver::Result
Cadical::solve()
{
  int32_t res = d_solver->solve();
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
Cadical::set_terminate(int32_t (*fun)(void *), void *state)
{
  CadicalTerminator *term = new CadicalTerminator();
  term->d_state           = state;
  term->f_fun             = fun;
  d_term.reset(term);
  if (fun)
  {
    d_solver->connect_terminator(d_term.get());
  }
  else
  {
    d_solver->disconnect_terminator();
  }
}

bool
CadicalTerminator::terminate()
{
  if (!f_fun) return false;
  return f_fun(d_state);
}

}  // namespace bzla::sat
