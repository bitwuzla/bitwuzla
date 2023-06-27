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

#include <cadical.hpp>
#include <memory>

#include "sat/sat_solver.h"
#include "terminator.h"

namespace bzla::sat {

class CadicalTerminator : public CaDiCaL::Terminator
{
 public:
  CadicalTerminator(bzla::Terminator* terminator);
  ~CadicalTerminator() {}
  bool terminate() override;

 private:
  bzla::Terminator* d_terminator = nullptr;
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
  void configure_terminator(Terminator* terminator) override;
  const char *get_name() const override { return "CaDiCaL"; }
  const char *get_version() const override;

 private:
  std::unique_ptr<CaDiCaL::Solver> d_solver   = nullptr;
  std::unique_ptr<CaDiCaL::Terminator> d_term = nullptr;
};

}  // namespace bzla::sat
#endif
