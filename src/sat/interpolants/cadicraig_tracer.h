/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_INTERPOLANTS_CADICRAIG_TRACER_H_INCLUDED
#define BZLA_SAT_INTERPOLANTS_CADICRAIG_TRACER_H_INCLUDED

#include <cadical.hpp>
#include <craigtracer.hpp>
#include <tracer.hpp>

#include "sat/interpolants/tracer.h"

namespace bzla::sat::interpolants {

class CadiCraigTracer : public Tracer
{
 public:
  CadiCraigTracer(Env& env, bv::AigBitblaster& bitblaster)
      : Tracer(env, bitblaster)
  {
    d_tracer.reset(new CaDiCraig::CraigTracer());
    d_tracer->set_craig_construction(CaDiCraig::CraigConstruction::ASYMMETRIC);
  }
  ~CadiCraigTracer() {}

  /* CaDiCaL::Tracer interface ------------------------------------------- */

  void add_original_clause(uint64_t id,
                           bool redundant,
                           const std::vector<int32_t>& clause,
                           bool restore = false) override;

  void add_derived_clause(uint64_t id,
                          bool redundant,
                          const std::vector<int>& clause,
                          const std::vector<uint64_t>& proof_chain) override;

  void add_assumption_clause(uint64_t id,
                             const std::vector<int>& clause,
                             const std::vector<uint64_t>& proof_chain) override;

  void delete_clause(uint64_t id,
                     bool redundant,
                     const std::vector<int>& clause) override;

  void add_assumption(int32_t lit) override;

  void add_constraint(const std::vector<int32_t>& clause) override;

  void reset_assumptions() override;

  void conclude_unsat(CaDiCaL::ConclusionType conclusion,
                      const std::vector<uint64_t>& proof_chain) override;

  /* --------------------------------------------------------------------- */

  void label_variable(int32_t id, VariableKind kind) override;

  void label_clause(int32_t id, ClauseKind kind) override;

  Node get_interpolant() override;

 private:
  std::unordered_map<int64_t, Node> map_vars_to_node(
      const std::unordered_set<int64_t>& vars);
  std::unique_ptr<CaDiCraig::CraigTracer> d_tracer;
};

}  // namespace bzla::sat::interpolants

#endif
