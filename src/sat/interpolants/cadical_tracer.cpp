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
#include "option/option.h"
#include "sat/interpolants/tracer_kinds.h"

using namespace bzla::bitblast;
using namespace bzla::node;

namespace bzla::sat::interpolants {

CadicalTracer::CadicalTracer(Env& env, bv::AigBitblaster& bitblaster)
    : Tracer(env, bitblaster, env.options().interpolants_lift()),
      d_algo(env.options().interpolants_algo())
{
}

CadicalTracer::~CadicalTracer() {}

namespace {
VariableKind
get_var_label(const std::unordered_map<int64_t, VariableKind>& var_labels,
              int64_t lit)
{
  auto it = var_labels.find(std::abs(lit));
  if (it == var_labels.end())
  {
    // if not labeled, it is not active, i.e., it is part of a definition
    // that is not currently asserted/assumed
    return VariableKind::NONE;
  }
  assert(it->second != VariableKind::NONE);
  return it->second;
}
}  // namespace

/* CaDiCaL::Tracer interface ------------------------------------------------ */

void
CadicalTracer::add_original_clause(uint64_t id,
                                   bool redundant,
                                   const std::vector<int32_t>& clause,
                                   bool restore)
{
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "original clause [" << id << "] (" << redundant << "): {";
    for (const auto& lit : clause)
    {
      ss << " " << lit;
    }
    Log(2) << ss.str() << " } [restore: " << restore << "]";
  }

  (void) redundant;
  assert(id);
  assert(d_cur_aig_id);

  if (restore)
  {
    // We must never delete clauses, for different reasons. Thus we also never
    // restore original clauses.
    return;
  }

  assert(d_clauses.size() == id);
  // original clause, thus no antecedents
  d_clauses.emplace_back(clause, ClauseType::ORIGINAL, d_cur_aig_id);
}

void
CadicalTracer::add_derived_clause(uint64_t id,
                                  bool redundant,
                                  const std::vector<int32_t>& clause,
                                  const std::vector<uint64_t>& antecedents)
{
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "derived clause [" << id << "] (" << redundant << "): {";
    for (const auto& lit : clause)
    {
      ss << " " << lit;
    }
    ss << " } [";
    for (const auto& id : antecedents)
    {
      ss << " " << id;
    }
    Log(2) << ss.str() << " ]";
  }

  (void) id;
  (void) redundant;
  assert(!antecedents.empty());
  assert(d_clauses.size() == id);
  d_clauses.emplace_back(clause, ClauseType::DERIVED, 0, antecedents);
}

void
CadicalTracer::add_assumption_clause(uint64_t id,
                                     const std::vector<int32_t>& clause,
                                     const std::vector<uint64_t>& antecedents)
{
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "assumption clause [" << id << "]: ";
    for (const auto& lit : clause)
    {
      ss << " " << lit;
    }
    Log(2) << ss.str();
  }

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
      d_clauses.push_back({{lit}, ClauseType::ASSUMPTION, 0, antecedents});
      d_assumption_clauses.push_back(id);
      return;
    }
  }

  if (antecedents.empty())
  {
    assert(d_clauses.size() == id);
    d_clauses.emplace_back(clause, ClauseType::ASSUMPTION, 0, antecedents);
  }
  d_assumption_clauses.push_back(id);
}

void
CadicalTracer::delete_clause(uint64_t id,
                             bool redundant,
                             const std::vector<int32_t>& clause)
{
  // We must never delete clauses, for different reasons.
  //
  // If we delete them completely, including the aig-id, we cannot restore the
  // AIG id. If we only delete their clause/antecedents, it will happen that
  // clauses and antecedents in the proof core have been previously deleted
  // (CaDiCaL deletes clauses it simplifies). This applies to any type of
  // clause, including derived clauses.
  //
  // Since we never delete clauses, we also never restore original clauses.
  (void) id;
  (void) redundant;
  (void) clause;
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "delete clause: " << id << " (" << redundant << ") {";
    for (int32_t l : clause)
    {
      ss << " " << l;
    }
    ss << " }";
    Log(2) << ss.str();
  }
}

void
CadicalTracer::add_assumption(int32_t lit)
{
  Log(2) << "assumption: " << lit;
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
    d_clauses[id].d_type   = ClauseType::NONE;
    d_clauses[id].d_aig_id = 0;
  }
  d_assumptions.clear();
  d_assumption_clauses.clear();
}

void
CadicalTracer::conclude_unsat(CaDiCaL::ConclusionType conclusion,
                              const std::vector<uint64_t>& clause_ids)
{
  (void) conclusion;
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
    // One or more constraints are responsible for the conflict, conclusion of
    // proof chain is a single clause with failed assumptions.
    assert(clause_ids.size() == 1);
    assert(clause_ids[0] < d_clauses.size());
    assert(!d_clauses[clause_ids[0]].d_clause.empty());
  }
#endif
  d_conclusion = conclusion;
  d_proof_core.clear();
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
      const auto& antecedents = d_clauses[id].d_antecedents;
      visit.insert(visit.end(), antecedents.begin(), antecedents.end());
    }
  }
  std::sort(d_proof_core.begin(), d_proof_core.end());
  d_stats.size_proof      = d_clauses.size();
  d_stats.size_proof_core = d_proof_core.size();
}

/* -------------------------------------------------------------------------- */

Node
CadicalTracer::get_interpolant(
    const std::unordered_map<int64_t, VariableKind>& var_labels,
    const std::unordered_map<int64_t, ClauseKind>& clause_labels,
    const std::unordered_map<Node, sat::interpolants::VariableKind>&
        term_labels)
{
  d_part_interpolants.clear();
  uint64_t final_clause_id = d_final_clause_ids[0];

  if (d_logger.is_log_enabled(2))
  {
    Log(2);
    Log(2) << "proof core:";
    for (const auto& p : d_proof_core)
    {
      std::stringstream ss;
      ss << "  " << p << ": (";
      for (const auto& lit : d_clauses[p].d_clause)
      {
        ss << " " << lit;
      }
      ss << " ) [";
      for (const auto& ant : d_clauses[p].d_antecedents)
      {
        ss << "  " << ant;
      }
      ss << " ]";
      Log(2) << ss.str();
    }
    Log(2);
    Log(2) << "clause labels:";
    for (const auto& cl : clause_labels)
    {
      (void) cl.first;
      (void) cl.second;
      std::stringstream ss;
      Log(2) << "  " << cl.first << ": " << cl.second;
    }
    Log(2);
    Log(2) << "clauses:";
    for (size_t id = 0, size = d_clauses.size(); id < size; ++id)
    {
      std::stringstream ss;
      auto& clause = d_clauses[id];
      ss << "  " << id << ": [" << clause.d_aig_id << "]: (";
      for (const auto& lit : clause.d_clause)
      {
        ss << " " << lit;
      }
      ss << " )";
      if (clause_labels.find(clause.d_aig_id) != clause_labels.end())
      {
        ss << " [" << clause_labels.at(clause.d_aig_id) << "]";
      }
      else if (clause.d_clause.size() > 1
               && clause_labels.find(-clause.d_aig_id) != clause_labels.end())
      {
        ss << " [" << clause_labels.at(-clause.d_aig_id) << "]";
      }
      Log(2) << ss.str();
    }
    Log(2);
    Log(2) << "variable labels:";
    for (const auto& vl : var_labels)
    {
      Log(2) << "  " << vl.first << ": " << vl.second;
    }
    Log(2);
  }

  for (uint64_t id : d_proof_core)
  {
    assert(id <= d_clauses.size());
    const auto& clause = d_clauses[id];
    ClauseType type    = clause.d_type;
    assert(type != ClauseType::NONE);

    if (type == ClauseType::ORIGINAL)
    {
      // Our clause label mapping maps AIG nodes reachable from assertions
      // to the respective labeling (as given via the assertions). This is
      // sensitive to Boolean negation and thus AIG node ids may be negative.
      //
      // However, our clause to associated AIG node mapping maps clauses
      // associated with AND gates and AIG nodes representing ITEs to the
      // respective, non-negated AIG node (id is always positive). Only leafs
      // of top-level assertions are associated with (potentially negated)
      // AIGs representing top-level assertions.
      //
      // Thus, if we don't find the associated node in the clause label
      // mapping, it must be a clause associated with an AND gate or ITE node
      // and may thus not be unit. Its labeling is independent of negation.
      auto it = clause_labels.find(clause.d_aig_id);
      if (it == clause_labels.end())
      {
        assert(clause.d_clause.size() > 1);
        it = clause_labels.find(-clause.d_aig_id);
      }
      assert(it != clause_labels.end());
      ClauseKind kind = it->second;
      assert(d_part_interpolants.find(id) == d_part_interpolants.end());
      d_part_interpolants.emplace(
          id, get_interpolant(var_labels, clause.d_clause, kind));
    }
    else if (type == ClauseType::DERIVED)
    {
      // CaDiCaL stores the antecedents of a derived clause in the order they
      // were resolved/propagated. We thus have to process these antecedents
      // in reverse order, starting from the last.
      const auto& antecedents = clause.d_antecedents;
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
          auto label = get_var_label(var_labels, lit);
          assert(label != VariableKind::NONE);
          // If NONE, then lit is not active (i.e., it is not part of a
          // clause that is currently asserted/assumed) and thus irrelevant
          // (the interpolant is not extended with it).
          extend_interpolant(
              ipol, d_part_interpolants[antecedents[idx]], lit, label);
        }
      }
      d_part_interpolants[id] = ipol;
    }
    else if (type == ClauseType::ASSUMPTION)
    {
      const auto& antecedents = clause.d_antecedents;
      if (antecedents.empty())
      {
        assert(clause.d_clause.size() == 2);
        bool is_ass_lit0 =
            d_assumptions.find(-clause.d_clause[0]) != d_assumptions.end();
        bool is_ass_lit1 =
            d_assumptions.find(-clause.d_clause[1]) != d_assumptions.end();
        if (!is_ass_lit0 || !is_ass_lit1)
        {
          assert(d_clauses.size() == id);
          int32_t lit = is_ass_lit0 ? -clause.d_clause[1] : -clause.d_clause[0];
          assert(d_part_interpolants.find(id) != d_part_interpolants.end());
          ClauseKind kind = clause_labels.at(-lit);
          d_part_interpolants.emplace(
              id, get_interpolant(var_labels, {-lit}, kind));
          continue;
        }
      }

      Interpolant ipol =
          antecedents.size() ? d_part_interpolants.at(id) : Interpolant();
      for (int32_t lit : clause.d_clause)
      {
        if (d_assumptions.find(-lit) == d_assumptions.end())
        {
          continue;
        }
        ClauseKind kind = clause_labels.at(-lit);
        Interpolant ip = get_interpolant(var_labels, {-lit}, kind);
        assert(!ip.is_null());
        if (!ipol.is_null())
        {
          extend_interpolant(ipol, ip, -lit, get_var_label(var_labels, lit));
        }
        else
        {
          ipol = ip;
        }
      }

      if (antecedents.empty())
      {
        d_part_interpolants[id] = ipol;
      }
    }
  }

  // unsat determined based on assumptions
  if (d_conclusion == CaDiCaL::ConclusionType::ASSUMPTIONS)
  {
    Interpolant interpolant = d_part_interpolants.at(final_clause_id);
    for (int32_t lit : d_clauses[final_clause_id].d_clause)
    {
      ClauseKind kind = clause_labels.at(-lit);
      Interpolant ip = get_interpolant(var_labels, {-lit}, kind);
      assert(!ip.is_null());
      if (!interpolant.is_null())
      {
        extend_interpolant(
            interpolant, ip, -lit, get_var_label(var_labels, lit));
      }
      else
      {
        interpolant = ip;
      }
    }
    return get_interpolant_node(interpolant, term_labels);
  }

  // derived empty clause
  auto it = d_part_interpolants.find(final_clause_id);
  assert(it != d_part_interpolants.end());
  return get_interpolant_node(it->second, term_labels);
}

Node
CadicalTracer::get_interpolant_node(
    Interpolant interpolant,
    const std::unordered_map<Node, sat::interpolants::VariableKind>&
        term_labels)
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
        it->second = get_node_from_bb_cache(cur, rev_bb_cache, term_labels);
        assert(!cur.is_const() || !it->second.is_null());
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

  Log(1) << "SAT interpolant: " << interpolant;
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
CadicalTracer::mk_or(const bitblast::AigNode& aig0,
                     const bitblast::AigNode& aig1) const
{
  return d_amgr.mk_not(d_amgr.mk_and(d_amgr.mk_not(aig0), d_amgr.mk_not(aig1)));
}

AigNode
CadicalTracer::mk_or(const std::vector<AigNode>& aigs) const
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
CadicalTracer::get_interpolant(
    const std::unordered_map<int64_t, VariableKind>& var_labels,
    const std::vector<int32_t>& clause,
    ClauseKind kind)
{
  assert(!clause.empty());
  AigNode res = d_amgr.mk_true();
  if (kind == ClauseKind::A)
  {
    switch (d_algo)
    {
      case option::InterpolantsAlgo::MCMILLAN: {
        std::vector<AigNode> lits;
        for (int32_t lit : clause)
        {
          if (get_var_label(var_labels, lit) == VariableKind::GLOBAL)
          {
            lits.push_back(d_amgr.get_node(lit));
          }
          res = mk_or(lits);
        }
      }
      break;
      case option::InterpolantsAlgo::PUDLAK: res = d_amgr.mk_false(); break;
    }
  }
  return res;
}

void
CadicalTracer::extend_interpolant(Interpolant& interpolant,
                                  Interpolant& ext,
                                  int32_t lit,
                                  VariableKind kind)
{
  // Given two clauses c1 and c2, resolved over var = |lit| with -lit in c1 and
  // lit in c2. We have that
  // interpolant = partial_interpolant(c1)
  // ext         = partial_interpolant(c2)
  // kind        = variable_kind(var)
  //
  // Mc Millan:
  // kind == A: res = partial_interpolant(c1) \/ partial_interpolant(c2)
  // else     : res = partial_interpolant(c1) /\ partial_interpolant(c2)
  //
  // Pudlak:
  // kind == A: res = partial_interpolant(c1) \/ partial_interpolant(c2)
  // kind == B: res = partial_interpolant(c1) /\ partial_interpolant(c2)
  // kind == G: res = (partial_interpolant(c1) \/ -lit)
  //                   /\ (partial_interpolant(c2) \/  lit)

  if (kind == VariableKind::A)
  {
    interpolant.d_interpolant =
        mk_or(interpolant.d_interpolant, ext.d_interpolant);
  }
  else
  {
    switch (d_algo)
    {
      case option::InterpolantsAlgo::MCMILLAN:
        interpolant.d_interpolant =
            d_amgr.mk_and(interpolant.d_interpolant, ext.d_interpolant);
        break;
      case option::InterpolantsAlgo::PUDLAK:
        if (kind == VariableKind::B)
        {
          interpolant.d_interpolant =
              d_amgr.mk_and(interpolant.d_interpolant, ext.d_interpolant);
        }
        else
        {
          assert(kind == VariableKind::GLOBAL);
          interpolant.d_interpolant = d_amgr.mk_and(
              mk_or(interpolant.d_interpolant, d_amgr.get_node(-lit)),
              mk_or(ext.d_interpolant, d_amgr.get_node(lit)));
        }
    }
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
  out << interpolant.d_interpolant.str();
  return out;
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::sat::interpolants
