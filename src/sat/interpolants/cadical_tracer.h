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

#include "bitblast/aig/aig_manager.h"
#include "cadical.hpp"
#include "tracer.hpp"

namespace bzla::sat::interpolants {

class Tracer : public CaDiCaL::Tracer
{
 public:
  enum class VariableKind
  {
    A,
    B,
    GLOBAL,
  };
  enum class ClauseKind
  {
    A,
    B,
    LEARNED,  // internal
  };
  // temporary
  enum class CnfKind : uint8_t
  {
    NONE,
    CONSTANT0,
    CONSTANT1,
    NORMAL
  };

  /**
   * Label variable with given kind.
   * @param id   The variable id.
   * @param kind The variable kind.
   */
  virtual void label_variable(int32_t id, VariableKind kind) = 0;

  /**
   * Label clause with given kind.
   * @note Clause IDs must be consecutive.
   * @param id   The clause id.
   * @param kind The clause kind.
   */
  virtual void label_clause(int32_t id, ClauseKind kind) = 0;

  // temporary
  virtual CnfKind create_craig_interpolant(std::vector<std::vector<int>>& cnf,
                                           int& tseitin_offset) = 0;
};

class CadicalTracer : public Tracer
{
 public:
  CadicalTracer(bitblast::AigManager& amgr) : d_amgr(amgr) {}
  ~CadicalTracer();

  struct Interpolant
  {
    bitblast::AigNode d_interpolant;
    ClauseKind d_kind;
    bool is_null() const { return d_interpolant.is_null(); }
    void reset() { d_interpolant = bitblast::AigNode(); }
  };

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

  CnfKind create_craig_interpolant(std::vector<std::vector<int>>& cnf,
                                   int& tseitin_offset) override;

 private:
  /**
   * Construct interpolant for given clause.
   * @param clause The clause to construct the interpolant for.
   * @param kind   The kind of the clause.
   * @return The interpolant.
   */
  Interpolant get_interpolant(const std::vector<int32_t>& clause,
                              ClauseKind kind);
  /**
   * Construct interpolant for given literal (i.e., assumption).
   * @param lit The literal to construct the interpolant for.
   * @return The interpolant.
   */
  Interpolant get_interpolant(int32_t lit);

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
  uint8_t mark_var(std::unordered_map<int32_t, uint8_t> marked_vars,
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

  /** The associated AIG manager. */
  bitblast::AigManager& d_amgr;
  /** The variable labels. */
  std::unordered_map<int32_t, VariableKind> d_labeled_vars;
  /** The clause labels. */
  std::unordered_map<int32_t, ClauseKind> d_labeled_clauses;
  /** The added clauses, dummy at index 0 to enable access via clause id. */
  std::vector<std::vector<int32_t>> d_clauses = {{}};
  /** The id of the most recently added clause. */
  uint64_t d_cur_clause_id = 0;
  /** The current added constraint, empty if none. */
  std::vector<int32_t> d_constraint;
  /** The kind of the currently added constraint. */
  ClauseKind d_constraint_kind = ClauseKind::LEARNED;
  /** The currently active assumptions. */
  std::unordered_set<int32_t> d_assumptions;
  /** The clauses observed via add_assumption_clause(). */
  std::vector<uint64_t> d_assumption_clauses;
  /**
   * The partial interpolants, dummy at index 0 to enable access via clause id.
   */
  std::vector<Interpolant> d_part_interpolants = {
      {bitblast::AigNode(), ClauseKind::LEARNED}};
  /** The interpolant after concluding unsat, is_null() if none. */
  Interpolant d_interpolant;
};

}  // namespace bzla::sat::interpolants
#endif
