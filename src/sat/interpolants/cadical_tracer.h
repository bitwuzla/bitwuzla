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

#include "bitblast/aig/aig_manager.h"
#include "cadical.hpp"
#include "tracer.hpp"

namespace bzla::sat::interpolants {

class CadicalTracer : public CaDiCaL::Tracer
{
 public:
  CadicalTracer(bitblast::AigManager& amgr) : d_amgr(amgr) {}
  ~CadicalTracer();

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

  struct interpolant
  {
    bitblast::AigNode aig;
    ClauseKind kind;
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

  // void add_assumption_clause(uint64_t id,
  //                            const std::vector<int> &clause,
  //                            const std::vector<uint64_t> &proof_chain)
  //                            override;

  void delete_clause(uint64_t id,
                     bool redundant,
                     const std::vector<int>& clause) override;

  void add_assumption(int32_t lit) override;

  void add_constraint(const std::vector<int32_t>& clause) override;

  void reset_assumptions() override;

  void conclude_unsat(CaDiCaL::ConclusionType,
                      const std::vector<uint64_t>& proof_chain) override;

  /* --------------------------------------------------------------------- */

  void label_variable(int32_t id, VariableKind kind);

  void label_clause(int32_t id, ClauseKind kind);

 private:
  struct Interpolant
  {
    bitblast::AigNode d_interpolant;
    ClauseKind d_kind;
  };

  /**
   * Mark variable with phase of literal.
   * @return True if variable was marked but phase switched.
   */
  uint8_t mark_var(int32_t lit);

  Interpolant get_interpolant(const std::vector<int32_t>& clause,
                              ClauseKind kind);
  void extend_interpolant(Interpolant& interpolant,
                          Interpolant& ext,
                          VariableKind kind);
  bitblast::AigNode mk_or(bitblast::AigNode& aig0,
                          bitblast::AigNode& aig1) const;
  bitblast::AigNode mk_or(std::vector<bitblast::AigNode> lits) const;

  /** The associated AIG manager. */
  bitblast::AigManager& d_amgr;
  /** The variable labels. */
  std::unordered_map<int32_t, VariableKind> d_labeled_vars;
  /** The clause labels. */
  std::unordered_map<int32_t, ClauseKind> d_labeled_clauses;
  std::unordered_map<int32_t, uint8_t> d_marked_vars;
  /** The added clauses, dummy at index 0 to enable access via clause id. */
  std::vector<std::vector<int32_t>> d_clauses = {{}};
  /** The id of the most recently added clause. */
  uint64_t d_cur_clause_id = 0;
  /** The interpolants, dummy at index 0 to enable access via clause id. */
  std::vector<Interpolant> d_interpolants = {
      {bitblast::AigNode(), ClauseKind::LEARNED}};
};

}  // namespace bzla::sat::interpolants
#endif
