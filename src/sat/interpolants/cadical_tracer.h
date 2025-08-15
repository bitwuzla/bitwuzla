/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_INTERPOLANTS_CADICAL_TRACER_H_INCLUDED
#define BZLA_SAT_INTERPOLANTS_CADICAL_TRACER_H_INCLUDED

#include <unordered_map>
#include <unordered_set>

#include "sat/interpolants/tracer.h"

namespace bzla::sat::interpolants {

class CadicalTracer : public Tracer
{
 public:
  CadicalTracer(Env& env, bv::AigBitblaster& bitblaster);
  ~CadicalTracer();

  enum class ClauseType
  {
    NONE,
    ORIGINAL,
    DERIVED,
    ASSUMPTION
  };
  struct Clause
  {
    Clause() {}
    Clause(const std::vector<int32_t>& clause,
           ClauseType type,
           int64_t aig_id,
           const std::vector<uint64_t>& antecedents = {})
        : d_clause(clause),
          d_type(type),
          d_aig_id(aig_id),
          d_antecedents(antecedents)
    {
    }

    /** The actual clause, a vector of literals. */
    std::vector<int32_t> d_clause;
    /** The clause type. */
    ClauseType d_type = ClauseType::NONE;
    /** The id of the AIG node this clause is associated with. */
    int64_t d_aig_id = 0;

    /** Antecedents of this clause in the proof. */
    std::vector<uint64_t> d_antecedents;
  };
  struct Interpolant
  {
    Interpolant()
        : d_interpolant(bitblast::AigNode()), d_kind(ClauseKind::LEARNED)
    {
    }
    Interpolant(const bitblast::AigNode& interpolant, ClauseKind kind)
        : d_interpolant(interpolant), d_kind(kind)
    {
    }
    bool is_null() const { return d_interpolant.is_null(); }
    void reset() { d_interpolant = bitblast::AigNode(); }
    bitblast::AigNode d_interpolant;
    ClauseKind d_kind = ClauseKind::LEARNED;
  };

  /* CaDiCaL::Tracer interface ------------------------------------------- */

  void add_original_clause(uint64_t id,
                           bool redundant,
                           const std::vector<int32_t>& clause,
                           bool restore = false) override;

  void add_derived_clause(uint64_t id,
                          bool redundant,
                          const std::vector<int32_t>& clause,
                          const std::vector<uint64_t>& proof_chain) override;

  void add_assumption_clause(uint64_t id,
                             const std::vector<int32_t>& clause,
                             const std::vector<uint64_t>& proof_chain) override;

  void delete_clause(uint64_t id,
                     bool redundant,
                     const std::vector<int32_t>& clause) override;

  void add_assumption(int32_t lit) override;

  void add_constraint(const std::vector<int32_t>& clause) override;

  void reset_assumptions() override;

  void conclude_unsat(CaDiCaL::ConclusionType conclusion,
                      const std::vector<uint64_t>& clause_ids) override;

  /* --------------------------------------------------------------------- */

  /**
   * Get interpolant given the labels for SAT variables and clauses.
   *
   * Variable and clause labels are given as maps from AIG id to variable label.
   * The tracer maintains a mapping from clause to associated AIG node.
   *
   * Requires that the current sat state is unsat.
   *
   * @param var_labels    The labels of the SAT variables.
   * @param clause_labels The labels of the SAT clauses.
   * @return The interpolant.
   */
  Node get_interpolant(
      const std::unordered_map<int64_t, VariableKind>& var_labels,
      const std::unordered_map<int64_t, ClauseKind>& clause_labels) override;

 private:
  /**
   * Construct interpolant for given clause.
   * @param var_kinds The mapping from AIG id to variable kinds.
   * @param clause The clause to construct the interpolant for.
   * @param kind   The kind of the clause.
   * @return The interpolant.
   */
  Interpolant get_interpolant(
      const std::unordered_map<int64_t, VariableKind>& var_kinds,
      const std::vector<int32_t>& clause,
      ClauseKind kind);

  Node get_interpolant_node(Interpolant interpolant);

  /**
   * Extend `interpolant` with interpolant `ext` for a given variable kind.
   * @param interpolant The interpolant to be extended.
   * @param ext         The interpolant to extend with.
   * @param kind        The variable kind.
   */
  void extend_interpolant(Interpolant& interpolant,
                          Interpolant& ext,
                          VariableKind kind);
  /**
   * Mark variable with phase of literal.
   * @param marked_vars The currently marked vars.
   * @param lit         The literal to mark the variable for.
   * @return True if variable was marked but its phase switched.
   */
  uint8_t mark_var(std::unordered_map<int32_t, uint8_t>& marked_vars,
                   int32_t lit);
  /**
   * Helper to create AIG or over two AIGs.
   * @param aig0 The first AIG.
   * @param aig1 The second AIG.
   * @return The AIG representing a logical OR over the given AIGs.
   */
  bitblast::AigNode mk_or(bitblast::AigNode& aig0,
                          bitblast::AigNode& aig1) const;
  /**
   * Helper to create AIG or over a list of AIGs.
   * @param aigs The AIGs.
   * @return The AIG representing a logical OR over the given AIGs.
   */
  bitblast::AigNode mk_or(std::vector<bitblast::AigNode> aigs) const;

  /** Added clauses, dummy at index 0 to enable access via clause id. */
  std::vector<Clause> d_clauses{Clause()};

  /** The currently active assumptions. */
  std::unordered_set<int32_t> d_assumptions;
  /** The clauses observed via add_assumption_clause(). */
  std::vector<uint64_t> d_assumption_clauses;
  /**
   * The partial interpolants, dummy at index 0 to enable access via clause id.
   */
  std::unordered_map<uint64_t, Interpolant> d_part_interpolants = {
      {0, Interpolant()}};

  std::vector<uint64_t> d_final_clause_ids;
  std::vector<uint64_t> d_proof_core;
  CaDiCaL::ConclusionType d_conclusion;
};

std::ostream& operator<<(std::ostream& out,
                         const CadicalTracer::ClauseType& type);
std::ostream& operator<<(std::ostream& out,
                         const CadicalTracer::Interpolant& interpolant);

}  // namespace bzla::sat::interpolants
#endif
