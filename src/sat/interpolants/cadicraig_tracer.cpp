/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/interpolants/cadicraig_tracer.h"

#include <unordered_map>

#include "node/node_utils.h"
#include "sat/interpolants/tracer.h"

using namespace bzla::bitblast;
using namespace bzla::node;

namespace bzla::sat::interpolants {

static std::unordered_map<Tracer::VariableKind, CaDiCraig::CraigVarType>
    s_var_kind_to_cadicraig = {
        {Tracer::VariableKind::A, CaDiCraig::CraigVarType::A_LOCAL},
        {Tracer::VariableKind::B, CaDiCraig::CraigVarType::B_LOCAL},
        {Tracer::VariableKind::GLOBAL, CaDiCraig::CraigVarType::GLOBAL},
};
static std::unordered_map<Tracer::ClauseKind, CaDiCraig::CraigClauseType>
    s_clause_kind_to_cadicraig = {
        {Tracer::ClauseKind::A, CaDiCraig::CraigClauseType::A_CLAUSE},
        {Tracer::ClauseKind::B, CaDiCraig::CraigClauseType::B_CLAUSE},
        {Tracer::ClauseKind::LEARNED, CaDiCraig::CraigClauseType::L_CLAUSE},
};

void
CadiCraigTracer::add_original_clause(uint64_t id,
                                     bool redundant,
                                     const std::vector<int32_t>& clause,
                                     bool restore)
{
  d_tracer->add_original_clause(id, redundant, clause, restore);
}

void
CadiCraigTracer::add_derived_clause(uint64_t id,
                                    bool redundant,
                                    const std::vector<int>& clause,
                                    const std::vector<uint64_t>& proof_chain)
{
  d_tracer->add_derived_clause(id, redundant, clause, proof_chain);
}

void
CadiCraigTracer::add_assumption_clause(uint64_t id,
                                       const std::vector<int>& clause,
                                       const std::vector<uint64_t>& proof_chain)
{
  d_tracer->add_assumption_clause(id, clause, proof_chain);
}

void
CadiCraigTracer::delete_clause(uint64_t id,
                               bool redundant,
                               const std::vector<int>& clause)
{
  d_tracer->delete_clause(id, redundant, clause);
}

void
CadiCraigTracer::add_assumption(int32_t lit)
{
  d_tracer->add_assumption(lit);
}

void
CadiCraigTracer::add_constraint(const std::vector<int32_t>& clause)
{
  d_tracer->add_constraint(clause);
}

void
CadiCraigTracer::reset_assumptions()
{
  d_tracer->reset_assumptions();
}

void
CadiCraigTracer::conclude_unsat(CaDiCaL::ConclusionType conclusion,
                                const std::vector<uint64_t>& proof_chain)
{
  d_tracer->conclude_unsat(conclusion, proof_chain);
}

void
CadiCraigTracer::label_variable(int32_t id, VariableKind kind)
{
  d_tracer->label_variable(id, s_var_kind_to_cadicraig[kind]);
}

void
CadiCraigTracer::label_clause(int32_t id, ClauseKind kind)
{
  d_tracer->label_clause(id, s_clause_kind_to_cadicraig[kind]);
}

Node
CadiCraigTracer::get_interpolant()
{
  int32_t cur_aig_id  = d_bitblaster.amgr().aig_id_counter();
  int32_t next_aig_id = cur_aig_id + 1;
  Log(3) << "cur_aig_id: " << cur_aig_id;

  std::vector<std::vector<int>> clauses;
  CaDiCraig::CraigCnfType cadicraig_res = d_tracer->create_craig_interpolant(
      CaDiCraig::CraigInterpolant::ASYMMETRIC, clauses, next_aig_id);

  if (cadicraig_res == CaDiCraig::CraigCnfType::NONE)
  {
    Log(1) << "NONE";
    return Node();
  }
  if (cadicraig_res == CaDiCraig::CraigCnfType::CONSTANT0)
  {
    Log(1) << "CONSTANT0";
    return d_nm.mk_value(false);
  }
  if (cadicraig_res == CaDiCraig::CraigCnfType::CONSTANT1)
  {
    Log(1) << "CONSTANT1";
    return d_nm.mk_value(true);
  }

  Log(1) << "NORMAL";

  Log(2);
  Log(2) << "SAT interpolant: ";
  if (d_logger.is_log_enabled(1))
  {
    for (const auto& cl : clauses)
    {
      std::stringstream ss;
      ss << "(";
      for (const auto& l : cl)
      {
        ss << " " << l;
      }
      ss << " )";
      Log(2) << ss.str();
    }
  }

  assert(cadicraig_res == CaDiCraig::CraigCnfType::NORMAL);
  std::unordered_map<int64_t, std::pair<int64_t, int64_t>> and_gates;
  std::unordered_set<int64_t> vars;

  for (const auto& clause : clauses)
  {
    // Every variable with id > cur_aig_id is a tseitin variable introduced
    // by CaDiCraig during CNF conversion of the AIG interpolant. The CNF
    // encoding of an AND gate is of the form, e.g.,
    // (-4 1)
    // (-4 2)
    // (4 -1 -2)
    // where 4 is a tseitin variable, 1 and 2 are the inputs of the AND gate
    // and thus 4 -> (and 1 2).

    // Collect AND gates introduced by CaDiCraig and known SAT vars to be
    // mapped to Nodes.
    int64_t var = std::abs(clause[0]);
    if (var > cur_aig_id)  // tseitin var, clause is part of AND encoding
    {
      if (clause.size() > 1)
      {
        auto [it, inserted] = and_gates.emplace(var, std::make_pair(0, 0));
        if (clause[0] < 0)
        {
          assert(clause.size() == 2);
          if (it->second.first == 0)
          {
            it->second.first = clause[1];
          }
          else
          {
            assert(it->second.second == 0);
            it->second.second = clause[1];
          }
        }
        var = std::abs(clause[1]);
        if (var <= cur_aig_id)
        {
          vars.insert(var);
        }
      }
    }
    else
    {
      assert(clause.size() == 1);
      vars.insert(var);
    }
  }

  Log(2);
  if (d_logger.is_log_enabled(2))
  {
    std::stringstream ss;
    ss << "SAT vars occurring in SAT interpolant: {";
    for (const auto& v : vars)
    {
      ss << " " << v;
    }
    ss << " }";
    Log(2) << ss.str();
  }

  // map SAT vars to Nodes
  auto map = map_vars_to_node(vars);

  if (d_logger.is_log_enabled(2))
  {
    Log(2);
    Log(2) << "SAT vars to nodes:";
    for (const auto& p : map)
    {
      Log(2) << p.first << ": " << p.second;
    }

    Log(2);
    std::stringstream ss;
    ss << "CaDiCraig Tseitin variables: {";
    for (const auto& p : and_gates)
    {
      ss << " " << p.first;
    }
    ss << " }";
    Log(2) << ss.str();
  }

  std::vector<int64_t> roots;
  for (const auto& clause : clauses)
  {
    if (clause.size() == 1)
    {
      roots.push_back(clause[0]);
    }

    for (int64_t lit : clause)
    {
      int64_t var = std::abs(lit);
      auto it     = map.find(var);
      if (it == map.end())
      {
        auto iit = and_gates.find(var);
        assert(iit != and_gates.end());
        int64_t lit_left  = iit->second.first;
        int64_t lit_right = iit->second.second;
        Node left         = map.at(std::abs(lit_left));
        if (lit_left < 0)
        {
          left = utils::invert_node(d_nm, left);
        }
        Node right = map.at(std::abs(lit_right));
        if (lit_right < 0)
        {
          right = utils::invert_node(d_nm, right);
        }
        map[var] = d_nm.mk_node(Kind::AND, {left, right});
      }
    }
  }

  assert(roots.size());
  assert(clauses[clauses.size() - 1].size() == 1 && roots.size() == 1);
  Node res;
  for (int64_t root : roots)
  {
    assert(map.find(std::abs(root)) != map.end());
    Node n = map.at(std::abs(root));
    if (root < 0)
    {
      n = d_nm.mk_node(Kind::NOT, {n});
    }
    res = res.is_null() ? n : d_nm.mk_node(Kind::AND, {res, n});
  }
  return res;
}

/**
 * Helper to map known SAT variables to nodes.
 * @param nm         The associated node manager.
 * @param bitblaster The associated bitblaster.
 * @param logger     The associated logger.
 * @param vars       The known SAT vars occurring in the interpolant.
 */
std::unordered_map<int64_t, Node>
CadiCraigTracer::map_vars_to_node(const std::unordered_set<int64_t>& vars)
{
  std::unordered_map<int64_t, Node> res;
  Node one          = d_nm.mk_value(BitVector::mk_true());
  const auto& cache = d_bitblaster.bitblaster_cache();

  // Map SAT vars to <node, bit index> for vars that do not occur in `vars`,
  // we may need them when creating nodes for internal AIG nodes.
  std::unordered_map<int64_t, std::pair<Node, int64_t>> skipped_vars_to_node;

  Log(2);
  Log(2) << "Bitblaster cache: " << cache.size() << " entries";

  for (const auto& p : cache)
  {
    if (d_logger.is_log_enabled(2))
    {
      std::stringstream ss;
      ss << p.first << ": (";
      for (const auto& a : p.second)
      {
        ss << " " << a.get_id();
      }
      ss << " )";
      Log(2) << ss.str();
    }

    bool is_bv = p.first.type().is_bv();
    assert(is_bv || p.first.type().is_bool());
    for (size_t i = 0, size = p.second.size(); i < size; ++i)
    {
      const AigNode& a = p.second[i];
      int64_t id       = a.get_id();
      int64_t var      = std::abs(id);
      auto it          = res.find(var);
      // already processed
      if (it != res.end())
      {
        continue;
      }
      size_t j = size - 1 - i;
      // don't need to consider
      if (vars.find(var) == vars.end())
      {
        skipped_vars_to_node.emplace(
            var,
            std::make_pair(id < 0 ? utils::invert_node(d_nm, p.first) : p.first,
                           j));
        continue;
      }
      // insert
      Node bit = p.first;
      assert(is_bv || j == 0);
      if (is_bv)
      {
        bit = utils::bv1_to_bool(d_nm,
                                 d_nm.mk_node(Kind::BV_EXTRACT, {bit}, {j, j}));
      }
      res.emplace(var, id < 0 ? d_nm.mk_node(Kind::NOT, {bit}) : bit);
    }
  }
  for (const int64_t var : vars)
  {
    if (res.find(var) != res.end())
    {
      continue;
    }
    // var is a circuit-internal AND gate, reconstruct in terms of inputs
    AigNode aig_node = d_bitblaster.get_node(var);
    bv::AigBitblaster::aig_node_ref_vector visit{aig_node};
    bv::AigBitblaster::unordered_aig_node_ref_map<bool> cache;

    do
    {
      const AigNode& cur = visit.back();
      int64_t id         = cur.get_id();
      int64_t var        = std::abs(id);

      if (res.find(var) != res.end())
      {
        visit.pop_back();
        continue;
      }

      {
        auto it = skipped_vars_to_node.find(var);
        if (it != skipped_vars_to_node.end())
        {
          Node bit   = it->second.first;
          size_t idx = it->second.second;
          assert(bit.type().is_bv() || idx == 0);
          if (bit.type().is_bv())
          {
            bit = utils::bv1_to_bool(
                d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {bit}, {idx, idx}));
          }
          res.emplace(var, bit);
          visit.pop_back();
          continue;
        }
      }

      assert(cur.is_and());

      auto [it, inserted] = cache.emplace(cur, true);

      if (inserted)
      {
        visit.push_back(cur[0]);
        visit.push_back(cur[1]);
      }
      else if (it->second)
      {
        it->second       = false;
        int64_t id_left  = cur[0].get_id();
        int64_t id_right = cur[1].get_id();
        Node left        = res.at(std::abs(id_left));
        if (id_left < 0)
        {
          left = utils::invert_node(d_nm, left);
        }
        Node right = res.at(std::abs(id_right));
        if (id_right < 0)
        {
          right = utils::invert_node(d_nm, right);
        }
        res[var] = d_nm.mk_node(Kind::AND, {left, right});
        visit.pop_back();
      }
    } while (!visit.empty());
  }
  return res;
}
}  // namespace bzla::sat::interpolants
