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
#include <iostream>

#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig/aig_node.h"

using namespace bzla::bitblast;

namespace bzla::sat::interpolants {

CadicalTracer::~CadicalTracer() {}

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
  d_part_interpolants.push_back(interpolant);
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
    assert(clause_id < d_part_interpolants.size());
    assert(!d_part_interpolants[clause_id].d_interpolant.is_null());
  }
#endif
  // Mark literals of conflicting clause
  auto& conf_clause = d_clauses[proof_chain.back()];
  std::unordered_map<int32_t, uint8_t> marked_vars;
  for (int32_t lit : conf_clause)
  {
    mark_var(marked_vars, lit);
  }
  assert(!marked_vars.empty());

  // Extend interpolant with pivot lit of each clause that was resolved with.
  Interpolant interpolant = d_part_interpolants[proof_chain.back()];
  size_t size             = proof_chain.size();
  for (size_t i = 1; i < size; ++i)
  {
    size_t idx = size - i - 1;
    for (int32_t lit : d_clauses[proof_chain[idx]])
    {
      // skip if not marked with the opposite phase in conflict clause
      if (!mark_var(marked_vars, lit))
      {
        continue;
      }
      extend_interpolant(interpolant,
                         d_part_interpolants[proof_chain[idx]],
                         d_labeled_vars.at(std::abs(lit)));
    }
  }
  assert(d_clauses.size() == id);
  d_clauses.push_back(clause);
  d_part_interpolants.push_back(interpolant);
}

void
CadicalTracer::add_assumption_clause(uint64_t id,
                                     const std::vector<int32_t>& clause,
                                     const std::vector<uint64_t>& proof_chain)
{
  Interpolant interpolant;

  if (proof_chain.size())
  {
    // We have a resolution of multiple clauses.
    add_derived_clause(id, true, clause, proof_chain);
    assert(id < d_part_interpolants.size());
    interpolant = d_part_interpolants[id];
  }
  else
  {
    assert(clause.size() == 2);
    bool is_ass_lit0 = d_assumptions.find(-clause[0]) != d_assumptions.end();
    bool is_ass_lit1 = d_assumptions.find(-clause[1]) != d_assumptions.end();
    if (!is_ass_lit0 || !is_ass_lit1)
    {
      assert(d_clauses.size() == id);
      int32_t lit = is_ass_lit0 ? -clause[1] : -clause[0];
      d_clauses.push_back({lit});
      d_part_interpolants.push_back(get_interpolant(-lit));
      d_assumption_clauses.push_back(id);
      return;
    }
  }

  for (int32_t lit : clause)
  {
    if (d_assumptions.find(-lit) != d_assumptions.end())
    {
      continue;
    }
    Interpolant ip = get_interpolant(-lit);
    if (!interpolant.is_null())
    {
      extend_interpolant(interpolant, ip, d_labeled_vars.at(std::abs(lit)));
    }
    else
    {
      interpolant = ip;
    }
  }

  if (proof_chain.empty())
  {
    assert(d_clauses.size() == id);
    d_clauses.push_back(clause);
    d_part_interpolants.push_back(interpolant);
  }
  d_assumption_clauses.push_back(id);
}

void
CadicalTracer::delete_clause(uint64_t id,
                             bool redundant,
                             const std::vector<int32_t>& clause)
{
  (void) redundant;
  (void) clause;
  assert(id < d_clauses.size());
#ifndef NDEBUG
  std::unordered_set<int32_t> lits;
  for (int32_t lit : d_clauses[id])
  {
    lits.insert(lit);
  }
  for (int32_t lit : clause)
  {
    assert(lits.find(lit) != lits.end());
  }
  assert(lits.size() == clause.size());
#endif
  d_clauses[id].clear();
}

void
CadicalTracer::add_assumption(int32_t lit)
{
  d_assumptions.insert(lit);
}

void
CadicalTracer::add_constraint(const std::vector<int>& clause)
{
  d_constraint = clause;
}

void
CadicalTracer::reset_assumptions()
{
  for (uint64_t id : d_assumption_clauses)
  {
    d_clauses[id].clear();
  }
  d_assumptions.clear();
  d_constraint.clear();
  d_assumption_clauses.clear();
}

void
CadicalTracer::conclude_unsat(CaDiCaL::ConclusionType conclusion,
                              const std::vector<uint64_t>& proof_chain)
{
  d_interpolant.reset();
  if (conclusion == CaDiCaL::ConclusionType::CONFLICT)
  {
    // Single global conflict, proof chain contains single empty clause.
    assert(proof_chain.size() == 1);
    assert(proof_chain[0] < d_clauses.size());
    assert(d_clauses[proof_chain[0]].empty());
    assert(proof_chain[0] < d_part_interpolants.size());
    d_interpolant = d_part_interpolants[proof_chain[0]];
  }
  else if (conclusion == CaDiCaL::ConclusionType::ASSUMPTIONS)
  {
    // One or more constraints are responsible for the conflict, proof chain
    // contains a single clause with failed assumptions. Note that the
    // interpolant of that clause has already been resolved with the
    // interpolants of the assumptions.
    assert(proof_chain.size() == 1);
    assert(proof_chain[0] < d_clauses.size());
    assert(!d_clauses[proof_chain[0]].empty());
    d_interpolant = d_part_interpolants[proof_chain[0]];
  }
  else
  {
    assert(conclusion == CaDiCaL::ConclusionType::CONSTRAINT);
    // Constraint clause is responsible for the conflict, mark literals.
    assert(!d_constraint.empty());
    std::unordered_map<int32_t, uint8_t> marked_vars;
    for (int32_t lit : d_constraint)
    {
      mark_var(marked_vars, lit);
    }
    d_interpolant = get_interpolant(d_constraint, d_constraint_kind);
    size_t size   = proof_chain.size();
    for (size_t i = 1; i < size; ++i)
    {
      for (int32_t lit : d_clauses[proof_chain[size - i - 1]])
      {
        // skip if not marked with the opposite phase in conflict clause
        if (!mark_var(marked_vars, lit))
        {
          continue;
        }
        extend_interpolant(d_interpolant,
                           d_part_interpolants[proof_chain[i]],
                           d_labeled_vars.at(std::abs(lit)));
      }
    }
  }
}

/* --------------------------------------------------------------------- */

void
CadicalTracer::label_variable(int32_t id, VariableKind kind)
{
  assert(id > 0);
  d_labeled_vars[id] = kind;
}

void
CadicalTracer::label_clause(int32_t id, ClauseKind kind)
{
  assert(id > 0);
  d_labeled_clauses[id] = kind;
}

class CnfSatSolver : public bitblast::SatInterface
{
 public:
  CnfSatSolver(std::vector<std::vector<int32_t>>& cnf) : d_cnf(cnf) {}

  void add(int64_t lit) override
  {
    if (lit == 0)
    {
      d_cnf.push_back(d_clause);
      d_clause.clear();
    }
    else
    {
      d_clause.push_back(lit);
    }
  }

  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (int64_t lit : literals)
    {
      add(lit);
    }
    add(0);
  }

  bool value(int64_t lit) override
  {
    (void) lit;
    assert(false);
    return false;
  }

 private:
  std::vector<int32_t> d_clause;
  std::vector<std::vector<int32_t>>& d_cnf;
};

Tracer::CnfKind
CadicalTracer::create_craig_interpolant(std::vector<std::vector<int32_t>>& cnf,
                                        int32_t& tseitin_offset)
{
  (void) tseitin_offset;
  cnf.clear();

  if (d_interpolant.is_null())
  {
    return CnfKind::NONE;
  }

  if (d_interpolant.d_interpolant.is_true())
  {
    return CnfKind::CONSTANT1;
  }
  if (d_interpolant.d_interpolant.is_false())
  {
    cnf.push_back({});
    return CnfKind::CONSTANT0;
  }
  if (d_interpolant.d_interpolant.is_const())
  {
    int32_t lit = d_interpolant.d_interpolant.get_id();
    assert(lit);
    cnf.push_back({lit});
    return CnfKind::NORMAL;
  }

  CnfSatSolver cnf_converter(cnf);
  bitblast::AigCnfEncoder d_cnf_encoder(cnf_converter);
  d_cnf_encoder.encode(d_interpolant.d_interpolant, true);
  return CnfKind::NORMAL;
}

/* --------------------------------------------------------------------- */

uint8_t
CadicalTracer::mark_var(std::unordered_map<int32_t, uint8_t>& marked_vars,
                        int32_t lit)
{
  int32_t var    = std::abs(lit);
  uint8_t mask   = (lit < 0) ? 2 : 1;
  uint8_t marked = marked_vars[var];
  if (!(marked & mask))
  {
    marked_vars[var] |= mask;
  }
  return marked & ~mask;
}

AigNode
CadicalTracer::mk_or(bitblast::AigNode& aig0, bitblast::AigNode& aig1) const
{
  return d_amgr.mk_not(d_amgr.mk_and(d_amgr.mk_not(aig0), d_amgr.mk_not(aig1)));
}

AigNode
CadicalTracer::mk_or(std::vector<AigNode> aigs) const
{
  assert(!aigs.empty());
  size_t size = aigs.size();
  if (size == 1)
  {
    return aigs[0];
  }
  AigNode res = d_amgr.mk_true();
  for (const AigNode& l : aigs)
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
  return {res, kind};
}

CadicalTracer::Interpolant
CadicalTracer::get_interpolant(int32_t lit)
{
  int32_t var       = std::abs(lit);
  VariableKind kind = d_labeled_vars.at(var);
  if (kind == VariableKind::A)
  {
    return {d_amgr.mk_false(), ClauseKind::A};
  }
  if (kind == VariableKind::B)
  {
    return {d_amgr.mk_true(), ClauseKind::B};
  }
  assert(kind == VariableKind::GLOBAL);
  return {d_amgr.mk_true(), ClauseKind::LEARNED};
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
