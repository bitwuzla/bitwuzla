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
#include <cmath>

#include "bitblast/aig/aig_node.h"
#include "craigtracer.hpp"

using namespace bzla::bitblast;

namespace bzla::sat::interpolants {

/* CaDiCaL::Tracer interface ------------------------------------------- */

void
CadicalTracer::add_original_clause(uint64_t id,
                                   bool redundant,
                                   const std::vector<int32_t>& clause,
                                   bool restore)
{
  (void) redundant;
  assert(id);

  if (restore)
  {
    assert(d_clauses.size() > id);
    d_clauses[id] = clause;
    return;
  }

  // We allow labeling clauses ahead of adding clauses, so the id of the
  // currently added clause does not necessary match with the last label
  // added. However, the labels are required to be consecutive, so we
  // keep track of the id of the current clause via d_cur_clause_id.
  // Note that the clause `id` given by CaDiCaL here does not necessarily
  // match our clause id as CaDiCaL may have added non-external clauses
  // inbetween.
  d_cur_clause_id += 1;
  assert(id >= d_cur_clause_id);
  auto it_clause = d_labeled_clauses.find(d_cur_clause_id);
#ifndef NDEBUG
  // clause ids must be consecutive when labeled
  assert(it_clause != d_labeled_clauses.end());
  // all literals in the clause must be labeled
  for (int32_t lit : clause)
  {
    assert(d_labeled_vars.find(std::abs(lit)) != d_labeled_vars.end());
  }
#endif
  ClauseKind kind         = it_clause->second;
  Interpolant interpolant = get_interpolant(clause, kind);
  assert(d_clauses.size() == id);
  d_clauses.push_back(clause);
  d_interpolants.push_back(interpolant);
}

void
CadicalTracer::add_derived_clause(uint64_t id,
                                  bool redundant,
                                  const std::vector<int32_t>& clause,
                                  const std::vector<uint64_t>& proof_chain)
{
  (void) id;
  (void) redundant;
  assert(!proof_chain.empty());
#ifndef NDEBUG
  for (uint64_t clause_id : proof_chain)
  {
    assert(clause_id < d_interpolants.size());
    assert(!d_interpolants[clause_id].d_interpolant.is_null());
  }
#endif
  // Mark literals of conflicting clause
  auto& conf_clause = d_clauses[proof_chain.back()];
  for (int32_t lit : conf_clause)
  {
    mark_var(lit);
  }
  // Extend interpolant with pivot lit of each clause that was resolved with.
  Interpolant interpolant = d_interpolants[proof_chain.back()];
  size_t size             = proof_chain.size();
  for (size_t i = 1; i < size; ++i)
  {
    for (int32_t lit : d_clauses[proof_chain[size - i - 1]])
    {
      // skip if not marked with the opposite phase in conflict clause
      if (!mark_var(lit))
      {
        continue;
      }
      extend_interpolant(
          interpolant, d_interpolants[proof_chain[i]], d_labeled_vars.at(lit));
    }
  }
  d_marked_vars.clear();
  assert(d_clauses.size() == id);
  d_clauses.push_back(clause);
  d_interpolants.push_back(interpolant);
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
  // TODO
}

void
CadicalTracer::add_assumption(int32_t lit)
{
  // TODO
}

void
CadicalTracer::add_constraint(const std::vector<int>& clause)
{
  // TODO
}

void
CadicalTracer::reset_assumptions()
{
  // TODO
}

void
CadicalTracer::conclude_unsat(CaDiCaL::ConclusionType,
                              const std::vector<uint64_t>& proof_chain)
{
  // TODO
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

uint8_t
CadicalTracer::mark_var(int32_t lit)
{
  int32_t var    = std::abs(lit);
  uint8_t mask   = (lit < 0) ? 2 : 1;
  uint8_t marked = d_marked_vars[var];
  if (!(marked & mask))
  {
    d_marked_vars[var] |= mask;
  }
  return marked & ~mask;
}

AigNode
CadicalTracer::mk_or(bitblast::AigNode& aig0, bitblast::AigNode& aig1) const
{
  return d_amgr.mk_not(d_amgr.mk_and(d_amgr.mk_not(aig0), d_amgr.mk_not(aig1)));
}

AigNode
CadicalTracer::mk_or(std::vector<AigNode> lits) const
{
  assert(!lits.empty());
  size_t size = lits.size();
  if (size == 1)
  {
    return lits[0];
  }
  AigNode res = d_amgr.mk_true();
  for (const AigNode& l : lits)
  {
    res = d_amgr.mk_and(res, d_amgr.mk_not(l));
  }
  return d_amgr.mk_not(res);
}

CadicalTracer::Interpolant
CadicalTracer::get_interpolant(const std::vector<int32_t>& clause,
                               ClauseKind kind)
{
  assert(!clause.empty());
  AigNode res = d_amgr.mk_true();
  if (kind == ClauseKind::A)
  {
    std::vector<AigNode> lits;
    for (int32_t lit : clause)
    {
      if (d_labeled_vars.at(std::abs(lit)) == VariableKind::GLOBAL)
      {
        lits.push_back(d_amgr.get_node(lit));
      }
      res = mk_or(lits);
    }
  }
  assert(kind == ClauseKind::B);
  return {res, kind};
}

void
CadicalTracer::extend_interpolant(Interpolant& interpolant,
                                  Interpolant& ext,
                                  VariableKind kind)
{
  if (interpolant.d_kind != ext.d_kind)
  {
    interpolant.d_kind = ClauseKind::LEARNED;
  }
  if (kind == VariableKind::A)
  {
    interpolant.d_interpolant =
        mk_or(interpolant.d_interpolant, ext.d_interpolant);
  }
  else
  {
    interpolant.d_interpolant =
        d_amgr.mk_and(interpolant.d_interpolant, ext.d_interpolant);
  }
}

/* --------------------------------------------------------------------- */
}  // namespace bzla::sat::interpolants
