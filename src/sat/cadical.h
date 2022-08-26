#ifndef BZLA_SAT_CADICAL_H_INCLUDED
#define BZLA_SAT_CADICAL_H_INCLUDED

#include <cadical.hpp>
#include <memory>

#include "sat/sat_solver.h"

namespace bzla::sat {

class CadicalTerminator : public CaDiCaL::Terminator
{
 public:
  CadicalTerminator() : CaDiCaL::Terminator() {}
  ~CadicalTerminator() {}
  bool terminate() override;
  void *d_state            = nullptr;
  int32_t (*f_fun)(void *) = nullptr;
};

class Cadical : public SatSolver
{
 public:
  Cadical();

  void add(int32_t lit) override;
  void assume(int32_t lit) override;
  int32_t value(int32_t lit) override;
  bool failed(int32_t lit) override;
  int32_t fixed(int32_t lit) override;
  Result solve() override;
  void set_terminate(int32_t (*fun)(void *), void *state) override;
  const char *get_name() const override { return "CaDiCaL"; }
  const char *get_version() const override;

 private:
  std::unique_ptr<CaDiCaL::Solver> d_solver   = nullptr;
  std::unique_ptr<CaDiCaL::Terminator> d_term = nullptr;
};

}  // namespace bzla::sat
#endif
