/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_ARRAY_ARRAY_SOLVER_H_INCLUDED
#define BZLA_SOLVER_ARRAY_ARRAY_SOLVER_H_INCLUDED

#include <cstdint>
#include <unordered_map>
#include <vector>

#include "backtrack/unordered_map.h"
#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "backtrack/vector_map.h"
#include "solver/solver.h"
#include "util/hash.h"
#include "util/logger.h"
#include "util/statistics.h"

namespace bzla::array {

enum class LemmaId
{
  CONGRUENCE,
  ACCESS_STORE,
  ACCESS_CONST_ARRAY,
  CONST_ARRAY_DIFF,
  DISEQUALITY,
};

std::ostream& operator<<(std::ostream& os, const LemmaId& lid);

class ArraySolver : public Solver
{
 public:
  /**
   * Determine if given term is a leaf node for other solvers than the
   * array solver.
   * @param term The term to query.
   */
  static bool is_theory_leaf(const Node& term);

  ArraySolver(Env& env, SolverState& state);
  ~ArraySolver();

  bool check() override;

  Node value(const Node& term) override;

  /**
   * Get the representative select stored in d_array_models.
   */
  Node repr(const Node& term) const;

  void register_term(const Node& term) override;

 private:
  /**
   * Utility class used to store array selects and stores in d_array_models. It
   * provides uniform access to query the corresponding arrays, indices and
   * elements.
   *
   * A Access class is hashed and compared based on the current model value of
   * the read index.
   *
   * @note: This class caches model values and hash values in order to avoid
   *        repeatedly querying and computing the hash values when accessing an
   *        array model.
   */
  class Access
  {
   public:
    Access(const Node& access, SolverState& state);
    Access(const Node& ca, const Node& ca_index, SolverState& state);

    /** @return Associated access node. */
    const Node& get() const;

    /** @return Associated element term. */
    const Node& element() const;

    /** @return Associated index term. */
    const Node& index() const;

    /** @return Associated array term. */
    const Node& array() const;

    /** @return Value of associated access node. */
    const Node& element_value() const;

    /** @return Value of read index. */
    const Node& index_value() const;

    /** Compute hash value based on d_index_value. */
    size_t hash() const;

   private:
    /** Associated access node. */
    Node d_access;
    /** Cached hash value. */
    size_t d_hash;
    /** Value of the access node. */
    Node d_value;
    /** Value of read index. */
    Node d_index_value;

    Node d_const_array_index;
  };

  /** Hash struct for hashing Access. */
  struct HashAccess
  {
    size_t operator()(const Access* access) const { return access->hash(); }
  };

  struct CompareAccess
  {
    size_t operator()(const Access* acc1, const Access* acc2) const
    {
      return acc1->index_value() == acc2->index_value();
    }
  };

  const Access* get_access(const Node& acc);

  /** Check theory consistency of access. */
  void check_access(const Node& access);

  /** Check theory consistency of constant array default values. */
  void check_default_value(const Node& const_array);

  /** Check theory consistency of array equality. */
  void check_equality(const Node& eq);

  /**
   * Add congruence lemma for (access a i), (access a j).
   *
   * Lemma: <path conditions> /\ i = j => (access a i) (access a j), where
   * <path conditions> are the conditions along the propagation paths of both
   * access nodes. These are constructed via collect_path_conditions().
   */
  void add_congruence_lemma(const Node& array,
                            const Access& acc1,
                            const Access& acc2);
  /**
   * Add access-store lemma (access (store a i e) j).
   *
   * Lemma: <path conditions> /\ i = j => (access (store a i e) j) = e, where
   * <path conditions> are the conditions along the propagation path of the
   * access. These are constructed via collect_path_conditions().
   */
  void add_access_store_lemma(const Access& acc, const Node& store);

  /**
   * Add access-const array lemma (access ((as const (...) v)) i).
   *
   * Lemma: <path conditions> => (access ((as const (...) v)) i) = v, where
   * <path conditions> are the conditions along the propagation path of the
   * access. These are constructed via collect_path_conditions().
   */
  void add_access_const_array_lemma(const Access& acc, const Node& array);

  bool add_const_array_equality_lemma(
      const Access& acc,
      const Node& array,
      const std::vector<std::pair<Node, bool>>& prop_path);

  /**
   * Add array disequality lemma for a = b.
   *
   * Lemma: a != b => a[k] != b[k] for a fresh k, where a[k] and b[k] act as
   * witnesses for the disequality of the two arrays.
   *
   * @return The disequality witnesses (a[k], b[k]).
   */
  std::pair<Node, Node> add_disequality_lemma(const Node& eq);

  /**
   * Find shortest path from access to array and construct the path conditions
   * required to get there.
   */
  void collect_path_conditions(const Access& access,
                               const Node& array,
                               std::vector<Node>& conditions);

  /** Add path condition for given array to conditions vector. */
  void add_path_condition(const Access& access,
                          const Node& array,
                          std::vector<Node>& conditions,
                          std::unordered_set<Node>& cache);

  /**
   * Compute the parents for the array terms in given term.
   *
   * The parents are required for array terms fo doing the upward propagation
   * of access nodes.
   */
  void compute_parents(const Node& term);

  /** Send de-duplicated lemma to solver state */
  void lemma(const Node& lemma, const LemmaId lid);

  /**
   * Construct model value for array.
   *
   * @param term Array term.
   * @param cache Caches array term values.
   * @param selected_index Get model value for given index.
   */
  Node construct_model_value(const Node& term,
                             std::unordered_map<Node, Node>& cache,
                             const Node& selected_index = Node());
  /**
   * Construct model value for array element. This is a helper for
   * construct_model_value().
   *
   * @param term Array element.
   * @param cache Model construction cache.
   */
  Node construct_element_value(const Node& term,
                               std::unordered_map<Node, Node>& cache);

  bool is_equal(const Access* acc1, const Access* acc2);
  bool is_equal(const Access* acc, const Node& a);

  Node const_array_index(const Node& const_array);

  /** Registered array selects. */
  backtrack::vector<Node> d_selects;

  /** Registered array equalities. */
  backtrack::vector<Node> d_equalities;

  std::vector<Node> d_eq_const_arrays;
  std::unordered_map<Node, Node> d_const_array_indices;

  /**
   * Array models constructed during check().
   * @note This cache is reset each check() call.
   */
  std::unordered_map<
      Node,
      std::unordered_set<const Access*, HashAccess, CompareAccess>>
      d_array_models;

  /**
   * Maps (base array id, constant array id) to the store index values
   * overwritten along the propagation path of the constant array's default
   * value to the base array. Recorded in check_default_value
   * and used in construct_model_value so model construction uses the actual
   * updated index sets.
   * @note This cache is reset each check() call.
   */
  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>>
      d_updated_indices;

  /** Maps access node to Access objects. */
  std::unordered_map<Node, Access> d_accesses;

  /**
   * Caches access nodes already checked in check_access().
   * @note This cache is reset each check() call.
   */
  std::unordered_set<Node> d_check_access_cache;

  /**
   * Maps array terms to their array parents, used for upwards propagation.
   * @note This map is computed in compute_parents().
   *
   * Backtrackable and kept in sync with d_active_parents: parent edges added
   * for an equality are rolled back on pop() so that re-asserting the same
   * equality after a pop() does not accumulate duplicate (or stale) parent
   * entries across push/pop cycles.
   */
  backtrack::vector_map<Node, Node> d_parents;
  /** Currently active parents. */
  backtrack::unordered_set<Node> d_active_parents;
  /**
   * Lemma cache for array disequalities. Maps equality to pair of selects,
   * which acts as witnesses for array disequality.
   */
  backtrack::unordered_map<Node, std::pair<Node, Node>>
      d_disequality_lemma_cache;

  backtrack::unordered_set<Node> d_const_array_eq_lemma_cache;

  /** Lemma cache for finding duplicate lemmas in current check() call. */
  std::unordered_set<Node> d_lemma_cache;

  /** Maps currently registered equalities to their current model value. */
  std::unordered_map<Node, bool> d_active_equalities;

  /** Flag that indicates whether array solver is currently in check(). */
  bool d_in_check = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_checks;
    uint64_t& num_propagations;
    uint64_t& num_propagations_up;
    uint64_t& num_propagations_down;
    uint64_t& num_selects;
    uint64_t& num_stores;
    uint64_t& num_equalities;
    util::HistogramStatistic& num_lemma_size;
    util::HistogramStatistic& lemmas;
    util::TimerStatistic& time_check;
  } d_stats;

  util::Logger& d_logger;
};

}  // namespace bzla::array

#endif
