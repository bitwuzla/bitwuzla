/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/interpolants/cadical_tracer.h"

#include <cassert>

namespace bzla::sat::interpolants {

/* CaDiCaL::Tracer interface ------------------------------------------- */

void
CadicalTracer::add_original_clause(uint64_t id,
                                   bool redundant,
                                   const std::vector<int32_t>& clauses,
                                   bool restore)
{
}

void
CadicalTracer::add_derived_clause(uint64_t id,
                                  bool redundant,
                                  const std::vector<int32_t>& clause,
                                  const std::vector<uint64_t>& proof_chain)
{
}

// void CadicalTracer::add_assumption_clause(uint64_t id,
//                            const std::vector<int32_t> &clause,
//                            const std::vector<uint64_t> &proof_chain)
//{
//
// }

void
CadicalTracer::delete_clause(uint64_t id,
                             bool redundant,
                             const std::vector<int32_t>& clause)
{
}

void
CadicalTracer::add_assumption(int32_t lit)
{
}

void
CadicalTracer::add_constraint(const std::vector<int>& clause)
{
}

void
CadicalTracer::reset_assumptions()
{
}

void
CadicalTracer::conclude_unsat(CaDiCaL::ConclusionType,
                              const std::vector<uint64_t>& proof_chain)
{
}

/* --------------------------------------------------------------------- */

void
CadicalTracer::label_variable(int32_t id, VariableKind kind)
{
  assert(id > 0);
  d_labeled_vars[id] = kind;
  d_marked_vars[id]  = false;
}

void
CadicalTracer::label_clause(int32_t id, ClauseKind kind)
{
  assert(id > 0);
  d_labeled_clauses[id] = kind;
}

/* --------------------------------------------------------------------- */

}  // namespace bzla::sat::interpolants
