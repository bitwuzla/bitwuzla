/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*----------------------------------------------------------------------------*/

#include "sat/cadical.h"

#include <cassert>

#include "bitblast/aig/aig_cnf.h"
#include "sat/interpolants/cadical_tracer.h"
#include "sat/propagator.h"

namespace bzla::sat {

/* CadicalTerminator public ------------------------------------------------- */

CadicalTerminator::CadicalTerminator(bzla::Terminator* terminator)
    : CaDiCaL::Terminator(), d_terminator(terminator)
{
}

bool
CadicalTerminator::terminate()
{
  if (!d_terminator) return false;
  return d_terminator->terminate();
}

/* Cadical public ----------------------------------------------------------- */

Cadical::Cadical()
{
  d_solver.reset(new CaDiCaL::Solver());
  d_solver->set("shrink", 0);
  d_solver->set("quiet", 1);
}

Cadical::~Cadical() {}

int32_t
Cadical::new_var()
{
  if (d_propagator)
  {
    d_propagator->resize(d_max_var);
  }
  return d_max_var++;
}

void
Cadical::add(int32_t lit, int64_t cgroup_id)
{
  (void) cgroup_id;
  int32_t var = std::abs(lit);
  assert(var < d_max_var);
  if (d_propagator && var)
  {
    d_propagator->info(var).active = true;
  }
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

void
Cadical::phase(int32_t lit)
{
  assert(std::abs(lit) < d_max_var);
  assert(d_propagator);
  d_propagator->force_phase(lit);
}

void
Cadical::unphase(int32_t lit)
{
  return d_solver->unphase(lit);
}

void
Cadical::register_propagator(std::unique_ptr<SatPropagator> sp)
{
  // Initialize propagator on demand.
  if (!d_propagator)
  {
    d_propagator.reset(new Propagator());
    d_propagator->attach_solver(d_solver.get());
    d_solver->connect_external_propagator(d_propagator.get());
    d_solver->connect_fixed_listener(d_propagator.get());
    d_propagator->resize(d_max_var);
  }
  d_propagator->register_propagator(std::move(sp));
}

Result
Cadical::solve()
{
  int32_t res = d_solver->solve();
  if (res == 10) return Result::SAT;
  if (res == 20) return Result::UNSAT;
  return Result::UNKNOWN;
}

void
Cadical::configure_terminator(Terminator* terminator)
{
  d_term.reset(new CadicalTerminator(terminator));
  if (terminator)
  {
    d_solver->connect_terminator(d_term.get());
  }
  else
  {
    d_solver->disconnect_terminator();
  }
}

const char *
Cadical::get_version() const
{
  return d_solver->version();
}

/* CadicalInterpol public --------------------------------------------------- */

CadicalInterpol::CadicalInterpol() : Cadical() {}

CadicalInterpol::~CadicalInterpol()
{
  if (d_tracer)
  {
    d_solver->disconnect_proof_tracer(d_tracer.get());
    d_tracer.reset(nullptr);
  }
}

void
CadicalInterpol::connect_tracer(Env& env,
                                bv::AigBitblaster& bitblaster,
                                const bitblast::AigCnfEncoder& cnf_encoder)
{
  d_tracer.reset(
      new sat::interpolants::CadicalTracer(env, bitblaster, cnf_encoder));
  d_solver->connect_proof_tracer(d_tracer.get(), true);
}

void
CadicalInterpol::add(int32_t lit, int64_t cgroup_id)
{
  assert(d_tracer);
  // We need to notify the interpolation SAT proof tracer which AIG id the
  // following, currently encoded SAT clauses are associated with. This
  // mapping is later utilized to generate dynamic labeling of variables and
  // clauses according to the partition of the set of current assertions into
  // A and B formulas.
  d_tracer->set_current_aig_id(cgroup_id);
  Cadical::add(lit);
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::sat

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/
