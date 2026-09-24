/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BITBLAST_AIG_CNF_H
#define BZLA__BITBLAST_AIG_CNF_H
#include "bitblast/aig/aig_node.h"

namespace bzla::bitblast {

class SatInterface
{
 public:
   virtual ~SatInterface() {};

   /**
    * Allocate new variable.
    * @return Fresh variable.
    */
   virtual int32_t new_var() = 0;

   /**
    * Add literal to current clause.
    *
    * @param id Id of literal to be added. 0 terminates the clause.
    * @param aig_id   The AIG id associated with the currently added clause.
    *                 In the case of clauses associated with and nodes or AIGs
    *                 encoding ITEs, this id will always be positive. In the
    *                 case of units encoding (the leafs of AIGs representing)
    *                 top-level assertions, the clause is associated with the
    *                 top-most AIG representing the assertion (and thus the id
    *                 may be negative).
    *
    * @note Parameter `aig_id` is not needed for standard bit-blasting, but may
    *       be required, e.g., for clause labeling when generating interpolants
    *       from the SAT proof.
    */
   virtual void add(int64_t lit, int64_t aig_id = 0) = 0;
   /**
    * Add a set of literals as clause.
    *
    * @param literals List of literals to be added (without terminating 0).
    * @param aig_id   The AIG id associated with this clause. In the case of
    *                 clauses associated with and nodes or AIGs encoding ITEs,
    *                 this id will always be positive. In the case of units
    *                 encoding (the leafs of AIGs representing) top-level
    *                 assertions, the clause is associated with the top-most
    *                 AIG representing the assertion (and thus the id may be
    *                 negative).
    *
    * @note Parameter `aig_id` is not needed for standard bit-blasting, but may
    *       be required, e.g., for clause labeling when generating interpolants
    *       from the SAT proof.
    */
   virtual void add_clause(const std::initializer_list<int64_t>& literals,
                           int64_t aig_id = 0) = 0;

   /** Set assertion level for clauses added via add_clause(). */
   virtual void set_level(uint32_t level) { (void) level; }

   /**
    * Query the value of the given literal.
    * @return True if the literal evaluates to true.
    */
   virtual bool value(int64_t lit) = 0;
};

class AigCnfEncoder
{
 public:
  struct Statistics
  {
    uint64_t allocated_vars = 0;  // Number of allocated SAT variables
    uint64_t num_vars       = 0;  // Number of currently encoded variables
    uint64_t num_clauses    = 0;  // Number of added clauses
    uint64_t num_literals   = 0;  // Number of added literals
    uint64_t num_ites       = 0;  // Number of extracted ites (excluding xors)
    uint64_t num_xors       = 0;  // Number of extracted xor/xnor gates
    uint64_t num_merged     = 0;  // Number of AND nodes merged into an n-ary AND
    uint64_t num_top_ors    = 0;  // Number of top-level ORs encoded as a clause
  };

  AigCnfEncoder(SatInterface& sat_solver);

  /**
   * Recursively encodes AIG node to CNF.
   *
   * @param node The AIG node to encode.
   * @param top_level Indicates whether given node is at the top level, which
   *        enables certain optimization.
   * @param level Assertion level to encode at (forwarded to the SAT solver).
   * */
  void encode(const AigNode& node, bool top_level = false, uint32_t level = 0);

  int32_t value(const AigNode& node);

  /** @return CNF variable of given encoded AIG node. */
  int32_t cnf_var(const AigNode& aig) const;

  /** @return CNF literal of given encoded AIG node. */
  int32_t cnf_lit(const AigNode& aig) const;

  /** @return Whether `aig` was already encoded to CNF. */
  bool is_encoded(const AigNode& aig) const;

  /** @return CNF variable representing true. */
  int32_t true_var() const { return d_true_var; };

  /** @return The AIG id to CNF id map. */
  const std::vector<int32_t>& aig2cnf() const { return d_aig_encoded; }

  /** Push assertion level. */
  void push();

  /**
   * Pop assertion level: reset AIG encoded state for AIGs encoded in the popped
   * assertion levels. SAT variables remain allocated.
   */
  void pop();

  /** @return CNF statistics. */
  const Statistics& statistics() const;

 private:
  /** Maximum number of mergeable leafs collected for an n-ary AND gate. */
  static constexpr size_t s_max_and_size = 64;
  /** Maximum number of literals in the clause emitted for a top-level OR. */
  static constexpr size_t s_max_top_or_size = 256;

  /** Lazily initializes d_true_var on the first encode() call. */
  void initialize();

  /** Encode AIG to CNF. */
  void _encode(const AigNode& node);
  /**
   * Determine whether the AND node `aig` can be merged into the n-ary AND/OR
   * gate of its (unique) parent, i.e., whether it needs no CNF variable.
   *
   * @note Only considers the AND node itself, the caller has to check that
   *       `aig` occurs with the polarity required for merging.
   */
  bool is_mergeable(const AigNode& aig) const;
  /**
   * Determine whether the AND node `aig` will be encoded as an extracted
   * ite(c,a,b) gate, and if so collect its children. The single predicate that
   * decides extraction, asked by both is_mergeable() and _encode().
   *
   * @param children If not null, the children of ite(c,a,b), added as c,~a,~b.
   */
  static bool extracts_as_ite(const AigNode& aig,
                              std::vector<AigNode>* children);
  /**
   * Collect the leafs of the n-ary AND gate rooted at AND node `aig`, i.e.,
   * recursively expand all mergeable AND children.
   *
   * @note Ignores the polarity of `aig` itself, an n-ary OR is collected by
   *       calling this on a negated AND node and negating the leaf literals.
   *
   * @param max_size Maximum number of leafs to collect.
   */
  void collect_and(const AigNode& aig,
                   std::vector<AigNode>& leafs,
                   size_t max_size);
  /** Ensure that `d_aig_encoded` is big enough to store `aig`. */
  void resize(const AigNode& aig);
  /** Mark `aig` as encoded. */
  void set_encoded(const AigNode& aig);

  /**
   * Maps AIG id to CNF id, which indicates whether the AIG was encoded.
   * We distinguish three cases for the entry:
   *
   * (1) 0  ... no SAT variable allocated
   * (2) >0 ... SAT variable allocated, but AIG not encoded
   * (3) <0 ... SAT variable allocated and AIG encoded
   *
   * pop() does not fully delete the entry, but sets AIGs back to state (2).
   */
  std::vector<int32_t> d_aig_encoded;
  /** Tracks the AIGs encoded since last push. */
  std::vector<size_t> d_aig_encoded_ids;
  /** Tracks encoded AIGs by assertion level. */
  std::vector<size_t> d_aig_encoded_ids_control;
  /** Marks AND nodes expanded during traversal in _encode(). */
  std::vector<bool> d_expanded;
  /** Stack of collect_and(), a member to save an allocation per call. */
  std::vector<AigNode> d_visit;
  /** SAT solver. */
  SatInterface& d_sat_solver;
  /** Variable allocated for true/false. */
  int32_t d_true_var = 0;

  /** CNF statistics. */
  Statistics d_statistics;
};
}  // namespace bzla::bitblast
#endif
