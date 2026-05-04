/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_CADICAL_H_INCLUDED
#define BZLA_SAT_CADICAL_H_INCLUDED

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*----------------------------------------------------------------------------*/

#include <cadical/cadical.hpp>
#include <memory>

#include "sat/sat_solver.h"
#include "solver/result.h"
#include "terminator.h"

namespace bzla {

class Env;

namespace bitblast {
class AigCnfEncoder;
}
namespace bv {
class AigBitblaster;
}

namespace sat {

namespace interpolants {
class Tracer;
}

class CadicalTerminator : public CaDiCaL::Terminator
{
 public:
  CadicalTerminator(bzla::Terminator* terminator);
  ~CadicalTerminator() {}
  bool terminate() override;

 private:
  bzla::Terminator* d_terminator = nullptr;
};

class Propagator;

class Cadical : public SatSolver
{
 public:
  Cadical();
  ~Cadical();

  int32_t new_var() override;
  void add(int32_t lit, int64_t cgroup_id = 0) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  void phase(int32_t lit) override;
  void unphase(int32_t lit) override;
  void register_propagator(std::unique_ptr<SatPropagator> sp) override;
  Result solve() override;
  void configure_terminator(Terminator* terminator) override;
  const char *get_name() const override { return "CaDiCaL"; }
  const char *get_version() const override;

  CaDiCaL::Solver* solver() { return d_solver.get(); }

 protected:
  int32_t d_max_var                           = 1;
  std::unique_ptr<CaDiCaL::Solver> d_solver   = nullptr;
  std::unique_ptr<CaDiCaL::Terminator> d_term = nullptr;
  std::unique_ptr<Propagator> d_propagator;
};

class CadicalInterpol : public Cadical
{
 public:
  CadicalInterpol();
  ~CadicalInterpol();
  void add(int32_t lit, int64_t cgroup_id = 0) override;
  void connect_tracer(Env& env,
                      bv::AigBitblaster& bitblaster,
                      const bitblast::AigCnfEncoder& cnf_encoder);
  interpolants::Tracer* tracer() { return d_tracer.get(); }

 private:
  /** Interpolation proof tracer. */
  std::unique_ptr<sat::interpolants::Tracer> d_tracer;
};

}  // namespace sat
}  // namespace bzla

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/

#endif
