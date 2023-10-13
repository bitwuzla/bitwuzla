/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__LS_LS_H
#define BZLA__LS_LS_H

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace bzla {

class RNG;

namespace ls {

template <class VALUE>
class Node;

/* -------------------------------------------------------------------------- */

enum class NodeKind
{
  CONST,

  AND,
  EQ,
  // IMPLIES,
  ITE,
  NOT,
  XOR,

  BV_ADD,
  BV_AND,
  BV_ASHR,
  BV_CONCAT,
  // BV_DEC,
  BV_EXTRACT,
  // BV_INC,
  BV_MUL,
  // BV_NAND,
  // BV_NE,
  // BV_NEG,
  // BV_NOR,
  BV_NOT,
  // BV_OR,
  // BV_REDAND,
  // BV_REDOR,
  // BV_SDIV,
  BV_SEXT,
  // BV_SGT,
  // BV_SGE,
  BV_SHL,
  BV_SHR,
  BV_SLT,
  // BV_SLE,
  // BV_SREM,
  // BV_SUB,
  BV_UDIV,
  // BV_UGT,
  // BV_UGE,
  BV_ULT,
  // BV_ULE,
  BV_UREM,
  // BV_XNOR,
  BV_XOR,
  // BV_ZEXT,
  /* must be last */
  NUM_OPS,
};

std::ostream& operator<<(std::ostream& out, const NodeKind& kind);

/* -------------------------------------------------------------------------- */

enum class Result
{
  SAT     = 10,
  UNSAT   = 20,
  UNKNOWN = 0,
};

/* -------------------------------------------------------------------------- */

template <class VALUE>
struct LocalSearchMove;

/* -------------------------------------------------------------------------- */

template <class VALUE>
class LocalSearch
{
 public:
  using NodesIdTable = std::vector<std::unique_ptr<Node<VALUE>>>;
  using ParentsSet   = std::unordered_set<uint64_t>;
  using ParentsMap   = std::unordered_map<uint64_t, ParentsSet>;

  struct
  {
    uint64_t d_nprops   = 0;
    uint64_t d_nupdates = 0;
    uint64_t d_nmoves   = 0;

    uint64_t d_nprops_inv  = 0;
    uint64_t d_nprops_cons = 0;

    uint64_t d_nconf_total = 0;

#ifndef NDEBUG
    std::unordered_map<NodeKind, uint64_t> d_ninv;
    std::unordered_map<NodeKind, uint64_t> d_ncons;
    std::unordered_map<NodeKind, uint64_t> d_nconf;
#endif
  } d_statistics;

  /** The configuration options of the local search module. */
  struct
  {
    /**
     * True if path is to be selected based on essential inputs, false if it is
     * to be selected randomly.
     *
     * @note If path selection based on essential inputs is enabled, we do not
     *       always pick an essential input (if there is one) but only with
     *       probability `prob_pick_ess_input` for completeness (to avoid
     *       cycles), and else a random input. Consider the following example:
     *       Assume we have 3 roots:
     *         y_[64] <= z_[64]
     *         z_[64] <= sign_extend((1844674407_[32] + x_[32]), 32)
     *         (844674407_[32] + x_[32]) <= 0_[32]
     *       Now, assume that the first root and one of the other two are
     *       satisfied with the initial assignment where all inputs are
     *       assigned to zero. Now, due to the inequality bounds derived from
     *       root 1 and 2/3 (depending on which one is satisfied), either the
     *       sign extension or the addition are essential, but z never is.
     *       Thus, we never propagate down to z and the first root (and thus
     *       the bounds of these two terms) remain unchanged. This traps us
     *       cycling between root 2 and 3 but never reaching a satisfiable
     *       assignment, which would require us to change the assignments of y
     *       or z.
     */
    bool use_path_sel_essential = true;
    /**
     * True to infer bounds for top-level inequalities for invertibility
     * conditions and inverse value computation.
     */
    bool use_ineq_bounds = false;
    /**
     * True to enable optimization for inverse value computation of
     * inequalities over concat and sign extension operands.
     */
    bool use_opt_lt_concat_sext = false;
    /**
     * Probability for producing an inverse rather than a consistent value when
     * invertibility condition for operand `x` wrt. to target value `t` and
     * constant bits is true. We do not always choose an inverse value for
     * invertible operations for completeness (to avoid cycles), and else a
     * consistent value. Interpreted as prob_inv_value * 1/10 %.
     */
    uint32_t prob_pick_inv_value = 990;
    /**
     * Probability for picking an essential input if there is one, and else
     * a random input (see use_path_sel_essential).
     */
    uint32_t prob_pick_ess_input = 990;
  } d_options;

  /**
   * Constructor.
   * @param max_nprops The maximum number of propagations to perform. Zero
   *                   if unlimited.
   * @param max_nupdates The maximum number of cone updates to perform. Zero
   *                     if unlimited.
   * @param seed The initial seed for the random number generator.
   */
  LocalSearch(uint64_t max_nprops, uint64_t max_nupdates, uint32_t seed = 1234);
  /** Destructor. */
  virtual ~LocalSearch();

  /**
   * Initialize local search module.
   * Must be called after all options are configured and before nodes are
   * created.
   */
  void init();

  /**
   * Configure the maximum number of propagations to perform.
   * @param max The maximum number of propagations.
   */
  void set_max_nprops(uint64_t max) { d_max_nprops = max; }
  /**
   * Configure the maximum number of updates to perform.
   * @param max The maximum number of updates.
   */
  void set_max_nupdates(uint64_t max) { d_max_nupdates = max; }

  /** Push assertion level. */
  void push();
  /** Pop assertion level. */
  void pop();

  /**
   * Kick off normalization of nodes.
   * Call this at the beginning of a satisfiability check.
   */
  virtual void normalize() {}

  /**
   * Get the assignment of the node given by id.
   * @param id The id of the node to query.
   */
  const VALUE& get_assignment(uint64_t id) const;
  /**
   * Set the assignment of the node given by id.
   * @param id The id of the node.
   * @param assignment The assignment to set.
   */
  void set_assignment(uint64_t id, const VALUE& assignment);

  /**
   * Register node as root.
   *
   * @note This not only adds `root` to `d_roots` but also registers unsat
   *       roots (cached in `d_roots_unsat`) and must therefore be called after
   *       initial assignment has been computed.
   *
   * @param root  The id of the node to register as root.
   * @param fixed True if this root is a top-level (assertion level 0) root.
   */
  void register_root(uint64_t root, bool fixed = false);
  /**
   * Get the number of unsat roots.
   * @return The number of unsat roots.
   */
  uint64_t get_num_roots_unsat() const { return d_roots_unsat.size(); }

  /**
   * Get the number of sat roots.
   * @return The number of sat roots.
   */
  uint64_t get_num_roots_sat() const
  {
    return d_roots.size() - d_roots_unsat.size();
  }

  /**
   * Get the number of total roots.
   * @return The number of total roots.
   */
  uint64_t get_num_roots() const { return d_roots.size(); }

  /**
   * Get the root responsible for returning unsat.
   */
  uint64_t get_false_root() const { return d_false_root; }
  // TODO: - we might want to exclude nodes that are not in the formula from
  //         cone updates

  Result move();

  /**
   * Set the log level.
   * @param level The level to set.
   */
  void set_log_level(uint32_t level) { d_log_level = level; }

 protected:
  /**
   * Get node by id.
   * @param id The node id.
   * @return The node with the given id.
   */
  Node<VALUE>* get_node(uint64_t id) const;
  /**
   * Determine if given node is a leaf node (its arity = 0).
   * @param node The node to query.
   * @return True if `node` is a leaf.
   */
  bool is_leaf_node(const Node<VALUE>* node) const;
  /**
   * Get the arity of the node given by id.
   * @param id The id of the node to query.
   */
  uint32_t get_arity(uint64_t id) const;
  /**
   * Get the child at given index of the node given by id.
   * @param id The id of the node to query.
   */
  uint64_t get_child(uint64_t id, uint32_t idx) const;
  /**
   * Determine if given node is an inequality (ULT or SLT) root (this includes
   * negated inequalities).
   * @param node The node to query.
   * @return True if `node` is a (possibly negated) inequality root.
   */
  bool is_ineq_root(const Node<VALUE>* node) const;
  /**
   * Determine if all roots are sat.
   * @return True if all roots are sat.
   */
  bool all_roots_sat() const { return d_roots_unsat.empty(); }
  /**
   * Update information related to the root given by id.
   *
   * This removes given root from the list of unsatisfied roots , adds the root
   * to the list of unsatisfied roots if it is unsatisfied.
   *
   * @note Roots are updated initially on registration, and during updating the
   *       assignments of the cone of influence of the input that has been
   *       updated.
   *
   * @param root The root to update.
   */
  void update_unsat_roots(Node<VALUE>* root);
  /**
   * Recompute normalized node ids.
   *
   * Nodes maintain two ids, the main identifier which is accessed via
   * Node::id() and passed to the user and used to internally, uniquely
   * identify a node, and the normalized id, which is relevant for cone updates.
   * If a normalization performs any (semi-)destructive rewriting resulting in
   * children with a higher id than their parent, this function must be called
   * after normalization (in LocalSearch::normalize()) to recompute their
   * normalized ids in a post-order DAG traversal manner.
   */
  void normalize_ids();
  /**
   * Compute min/max bounds for children of given node.
   *
   * If the bounds are depending on the current assignment, this must be called
   * after update_unsat_roots() has been called and the assignment of all nodes
   * has been computed/updated, i.e., the assignment is consistent.
   *
   * @param node The node.
   */
  virtual void compute_bounds(Node<VALUE>* node) = 0;
  /**
   * Update the assignment of the given node to the given assignment, and
   * recompute the assignment of all nodes in its cone of influence
   *
   * @param node The node to update.
   * @param assignment The new assignment of the given node.
   * @return The number of updated assignments.
   */
  uint64_t update_cone(Node<VALUE>* node, const VALUE& assignment);
  /**
   * Select an input and a new assignment for that input by propagating the
   * given target value `t_root` for the given root along one path towards an
   * input.
   *
   * @param root The root to propagate from.
   * @param t_root The target value of the given root.
   * @return An object encapsulating all information necessary for that move.
   */
  LocalSearchMove<VALUE> select_move(Node<VALUE>* root, const VALUE& t_root);

  /** The random number generator. */
  std::unique_ptr<RNG> d_rng;

  /** Map from node id to nodes. */
  NodesIdTable d_nodes;

  /**
   * The set of currently active roots, organized into assertion levels.
   *
   * This, together with d_roots_control, maintains currently active
   * roots organized into assertion-levels. Assertion levels are pushed via
   * push() and popped via pop() when solving incrementally.
   */
  std::vector<uint64_t> d_roots;
  /**
   * The control stack for d_roots, maintaining the start indices of assertion
   * levels in d_roots.
   */
  std::vector<size_t> d_roots_control;
  /**
   * Map root to its number of occurrences in d_roots.
   * This is to safe guard against non-unique registration of roots.
   */
  std::unordered_map<uint64_t, uint64_t> d_roots_cnt;

  /** The set of unsatisfied roots. */
  std::unordered_set<uint64_t> d_roots_unsat;
  /** Root responsible for unsat result. */
  uint64_t d_false_root;

  /**
   * The set of (to be considered) top-level inequalities. Maps inequality
   * roots to their sat assignment (true for top-level inequalities, false for
   * negated inequality roots).
   *
   * @note This includes top-level inequalities and negated inequalities that
   *       are not roots but whose parents are a top-level NOT.
   */
  std::unordered_map<const Node<VALUE>*, bool> d_roots_ineq;

  /** Map nodes to their parent nodes. */
  ParentsMap d_parents;

  /** The target value for each root. */
  std::unique_ptr<VALUE> d_true;

  /** The log level. */
  uint32_t d_log_level = 0;
  /** The maximum number of propagations, 0 for unlimited. */
  uint64_t d_max_nprops = 0;
  /** The maximum number of cone updates, 0 for unlimited. */
  uint64_t d_max_nupdates = 0;
  /** The seed for the RNG. */
  uint32_t d_seed;
};

/* -------------------------------------------------------------------------- */
}  // namespace ls
}  // namespace bzla

namespace std {
/**
 * Get the string representation of a given node kind.
 * @param kind The node kind.
 * @return The string representation.
 */
std::string to_string(bzla::ls::NodeKind kind);
}  // namespace std
#endif
