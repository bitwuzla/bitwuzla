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

#include "bitblast/aig/aig_node.h"
#include "node/node.h"
#include "node/node_utils.h"

using namespace bzla::bitblast;
using namespace bzla::node;

namespace bzla::sat::interpolants {

CadicalTracer::CadicalTracer(Env& env, bv::AigBitblaster& bitblaster)
    : Tracer(env, bitblaster)
{
}

CadicalTracer::~CadicalTracer() {}

/* CaDiCaL::Tracer interface ------------------------------------------------ */

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
    d_clauses[id].d_clause = clause;
    d_clauses[id].d_type   = ClauseType::ORIGINAL;
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
#ifndef NDEBUG
  auto it = d_labeled_clauses.find(d_cur_clause_id);
  // clause ids must be consecutive when labeled
  assert(it != d_labeled_clauses.end());
  // all literals in the clause must be labeled
  for (int32_t lit : clause)
  {
    assert(d_labeled_vars.find(std::abs(lit)) != d_labeled_vars.end());
  }
#endif
  assert(d_clauses.size() == id);
  d_antecedents.emplace_back();  // original clause, thus no antecedents
  d_clauses.emplace_back(clause, ClauseType::ORIGINAL, d_cur_clause_id);
}

void
CadicalTracer::add_derived_clause(uint64_t id,
                                  bool redundant,
                                  const std::vector<int32_t>& clause,
                                  const std::vector<uint64_t>& antecedents)
{
  (void) id;
  (void) redundant;
  assert(!antecedents.empty());
  assert(d_antecedents.size() == id);
  d_antecedents.push_back(antecedents);
  assert(d_clauses.size() == id);
  d_clauses.emplace_back(clause, ClauseType::DERIVED, 0);
}

void
CadicalTracer::add_assumption_clause(uint64_t id,
                                     const std::vector<int32_t>& clause,
                                     const std::vector<uint64_t>& antecedents)
{
  if (antecedents.size())
  {
    // We have a resolution of multiple clauses.
    add_derived_clause(id, true, clause, antecedents);
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
      d_clauses.push_back({{lit}, ClauseType::ASSUMPTION, 0});
      d_assumption_clauses.push_back(id);
      assert(d_antecedents.size() == id);
      d_antecedents.push_back(antecedents);
      return;
    }
  }

  if (antecedents.empty())
  {
    assert(d_clauses.size() == id);
    d_clauses.emplace_back(clause, ClauseType::ASSUMPTION, 0);
    assert(d_antecedents.size() == id);
    d_antecedents.push_back(antecedents);
  }
  d_assumption_clauses.push_back(id);
}

void
CadicalTracer::delete_clause(uint64_t id,
                             bool redundant,
                             const std::vector<int32_t>& clause)
{
  (void) id;
  (void) redundant;
  (void) clause;
  //   std::cout << "delete: " << id << std::endl;
  //   (void) redundant;
  //   (void) clause;
  //   assert(id < d_clauses.size());
  // #ifndef NDEBUG
  //   std::unordered_set<int32_t> lits;
  //   for (int32_t lit : d_clauses[id].first)
  //   {
  //     lits.insert(lit);
  //   }
  //   for (int32_t lit : clause)
  //   {
  //     assert(lits.find(lit) != lits.end());
  //   }
  //   assert(lits.size() == clause.size());
  // #endif
  //   d_clauses[id].first.clear();
  //   d_clauses[id].second = ClauseType::NONE;
}

void
CadicalTracer::add_assumption(int32_t lit)
{
  d_assumptions.insert(lit);
}

void
CadicalTracer::add_constraint(const std::vector<int>& clause)
{
  (void) clause;
  assert(false);
}

void
CadicalTracer::reset_assumptions()
{
  for (uint64_t id : d_assumption_clauses)
  {
    d_clauses[id].d_clause.clear();
    d_clauses[id].d_type = ClauseType::NONE;
    d_clauses[id].d_id   = 0;
  }
  d_assumptions.clear();
  d_assumption_clauses.clear();
}

void
CadicalTracer::conclude_unsat(CaDiCaL::ConclusionType conclusion,
                              const std::vector<uint64_t>& clause_ids)
{
  assert(conclusion != CaDiCaL::ConclusionType::CONSTRAINT);
#ifndef NDEBUG
  if (conclusion == CaDiCaL::ConclusionType::CONFLICT)
  {
    // Single global conflict, proof chain contains single empty clause.
    assert(clause_ids.size() == 1);
    assert(clause_ids[0] < d_clauses.size());
    assert(d_clauses[clause_ids[0]].d_clause.empty());
  }
  else
  {
    assert(conclusion == CaDiCaL::ConclusionType::ASSUMPTIONS);
    // One or more constraints are responsible for the conflict, proof chain
    // contains a single clause with failed assumptions. Note that the
    // interpolant of that clause has already been resolved with the
    // interpolants of the assumptions.
    assert(clause_ids.size() == 1);
    assert(clause_ids[0] < d_clauses.size());
    assert(!d_clauses[clause_ids[0]].d_clause.empty());
  }
#endif
  d_proof_core.clear();
  assert(d_clauses.size() == d_antecedents.size());
  d_final_clause_ids = clause_ids;
  std::vector<uint64_t> visit{clause_ids};
  std::vector<bool> visited(d_clauses.size(), false);
  // Compute proof core by tracing back from final clause ids
  while (!visit.empty())
  {
    uint64_t id = visit.back();
    visit.pop_back();
    if (!visited[id])
    {
      visited[id] = true;
      d_proof_core.push_back(id);
      const auto& antecedents = d_antecedents[id];
      visit.insert(visit.end(), antecedents.begin(), antecedents.end());
    }
  }
  std::sort(d_proof_core.begin(), d_proof_core.end());
}

/* -------------------------------------------------------------------------- */

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

Node
CadicalTracer::get_interpolant()
{
  for (uint64_t id : d_proof_core)
  {
    assert(id <= d_clauses.size());
    const auto& clause = d_clauses[id].d_clause;
    ClauseType type    = d_clauses[id].d_type;
    assert(type != ClauseType::NONE);
    if (type == ClauseType::ORIGINAL)
    {
      auto it = d_labeled_clauses.find(d_clauses[id].d_id);
      assert(it != d_labeled_clauses.end());
      ClauseKind kind = it->second;
      assert(d_part_interpolants.find(id) == d_part_interpolants.end());
      d_part_interpolants.emplace(id, get_interpolant(clause, kind));
    }
    else if (type == ClauseType::DERIVED)
    {
      assert(id <= d_antecedents.size());
      const auto& antecedents = d_antecedents[id];
      // Mark literals of conflicting clause
      auto& conf_clause = d_clauses[antecedents.back()].d_clause;
      std::unordered_map<int32_t, uint8_t> marked_vars;
      for (int32_t lit : conf_clause)
      {
        mark_var(marked_vars, lit);
      }
      assert(!marked_vars.empty());
      // Extend with pivot lit of each clause that was resolved with.
      Interpolant ipol = d_part_interpolants[antecedents.back()];
      size_t size      = antecedents.size();
      for (size_t i = 1; i < size; ++i)
      {
        size_t idx = size - i - 1;
        for (int32_t lit : d_clauses[antecedents[idx]].d_clause)
        {
          // skip if not marked with the opposite phase in conflict clause
          if (!mark_var(marked_vars, lit))
          {
            continue;
          }
          extend_interpolant(ipol,
                             d_part_interpolants[antecedents[idx]],
                             d_labeled_vars.at(std::abs(lit)));
        }
      }
      d_part_interpolants[id] = ipol;
    }
    else if (type == ClauseType::ASSUMPTION)
    {
      assert(id <= d_antecedents.size());
      const auto& antecedents = d_antecedents[id];
      Interpolant ipol;

      if (antecedents.size())
      {
        auto it = d_part_interpolants.find(id);
        assert(it != d_part_interpolants.end());
        ipol = it->second;
      }
      else
      {
        assert(clause.size() == 2);
        bool is_ass_lit0 =
            d_assumptions.find(-clause[0]) != d_assumptions.end();
        bool is_ass_lit1 =
            d_assumptions.find(-clause[1]) != d_assumptions.end();
        if (!is_ass_lit0 || !is_ass_lit1)
        {
          assert(d_clauses.size() == id);
          int32_t lit = is_ass_lit0 ? -clause[1] : -clause[0];
          assert(d_part_interpolants.find(id) != d_part_interpolants.end());
          d_part_interpolants.emplace(id, get_interpolant(-lit));
          continue;
        }
      }

      for (int32_t lit : clause)
      {
        if (d_assumptions.find(-lit) != d_assumptions.end())
        {
          continue;
        }
        Interpolant ip = get_interpolant(-lit);
        if (!ipol.is_null())
        {
          extend_interpolant(ipol, ip, d_labeled_vars.at(std::abs(lit)));
        }
        else
        {
          ipol = ip;
        }
      }

      if (antecedents.empty())
      {
        assert(d_clauses.size() == id);
        d_part_interpolants[id] = ipol;
      }
    }
  }
  auto it = d_part_interpolants.find(d_final_clause_ids[0]);
  assert(it != d_part_interpolants.end());
  return get_interpolant_node(it->second);
}

Node
CadicalTracer::get_interpolant_node(Interpolant interpolant)
{
  if (interpolant.is_null())
  {
    return Node();
  }

  if (interpolant.d_interpolant.is_true())
  {
    return d_nm.mk_value(true);
  }
  if (interpolant.d_interpolant.is_false())
  {
    return d_nm.mk_value(false);
  }

  RevBitblasterCache rev_bb_cache = compute_rev_bb_cache();

  // Convert AIG interpolant to Node
  bv::AigBitblaster::aig_node_ref_vector visit{interpolant.d_interpolant};
  std::unordered_map<int64_t, Node> vars_to_nodes;
  uint64_t interpol_size = 0;
  do
  {
    const bitblast::AigNode& cur = visit.back();
    int64_t id                   = cur.get_id();
    int64_t var                  = std::abs(id);
    assert(!cur.is_null());
    assert(id != 0);

    auto [it, inserted] = vars_to_nodes.emplace(var, Node());

    if (inserted)
    {
      if (cur.is_and())
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
    }
    else
    {
      if (it->second.is_null())
      {
        it->second =
            get_node_from_bb_cache(std::abs(cur.get_id()), rev_bb_cache);
        if (it->second.is_null())
        {
          int64_t id_left  = cur[0].get_id();
          int64_t id_right = cur[1].get_id();
          Node left        = vars_to_nodes.at(std::abs(id_left));
          if (id_left < 0)
          {
            left = utils::invert_node(d_nm, left);
          }
          Node right = vars_to_nodes.at(std::abs(id_right));
          if (id_right < 0)
          {
            right = utils::invert_node(d_nm, right);
          }
          it->second = d_nm.mk_node(Kind::AND, {left, right});
          interpol_size += 1;
        }
      }
      visit.pop_back();
    }
  } while (!visit.empty());

  if (d_logger.is_log_enabled(2))
  {
    Log(2);
    Log(2) << "SAT vars to nodes:";
    for (const auto& p : vars_to_nodes)
    {
      Log(2) << p.first << ": " << p.second;
    }
    Log(2);
  }

  Log(1) << "SAT interpolant size: " << interpol_size << " ands";
  d_stats.size_interpolant = interpol_size;

  int64_t id = interpolant.d_interpolant.get_id();
  Node res   = vars_to_nodes.at(std::abs(id));
  assert(!res.is_null());
  if (id < 0)
  {
    res = utils::invert_node(d_nm, res);
  }
  return res;
}

/* -------------------------------------------------------------------------- */

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
  if (aigs.empty())
  {
    return d_amgr.mk_false();
  }

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

std::ostream&
operator<<(std::ostream& out, const CadicalTracer::ClauseType& type)
{
  switch (type)
  {
    case CadicalTracer::ClauseType::NONE: out << "NONE"; break;
    case CadicalTracer::ClauseType::ORIGINAL: out << "ORIGINAL"; break;
    case CadicalTracer::ClauseType::DERIVED: out << "DERIVED"; break;
    case CadicalTracer::ClauseType::ASSUMPTION: out << "ASSUMPTION"; break;
  }
  return out;
}

std::ostream&
operator<<(std::ostream& out, const CadicalTracer::Interpolant& interpolant)
{
  out << interpolant.d_interpolant.str() << " (" << interpolant.d_kind << ")";
  return out;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::sat::interpolants
