#ifndef BZLALS__BZLALS_H
#define BZLALS__BZLALS_H

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace bzla {

class BitVector;
class RNG;

namespace ls {

struct LocalSearchMove;

class BitVectorDomain;
class BitVectorNode;

namespace test {
class TestLsBv;
}

class LocalSearch
{
  friend class test::TestLsBv;

 public:
  using NodesIdTable = std::vector<std::unique_ptr<BitVectorNode>>;
  using ParentsSet   = std::unordered_set<uint64_t>;
  using ParentsMap   = std::unordered_map<uint64_t, ParentsSet>;

  enum Result
  {
    SAT     = 10,
    UNSAT   = 20,
    UNKNOWN = 0,
  };

  enum OperatorKind
  {
    ADD,
    AND,
    ASHR,
    CONCAT,
    // DEC,
    EXTRACT,
    EQ,
    // IMPLIES,
    ITE,
    // INC,
    MUL,
    // NAND,
    // NE,
    // NEG,
    // NOR,
    NOT,
    // OR,
    // REDAND,
    // REDOR,
    // SDIV,
    SEXT,
    // SGT,
    // SGE,
    SHL,
    SHR,
    SLT,
    // SLE,
    // SREM,
    // SUB,
    UDIV,
    // UGT,
    // UGE,
    ULT,
    // ULE,
    UREM,
    // XNOR,
    XOR,
    // ZEXT,
  };

  struct
  {
    uint64_t d_nprops   = 0;
    uint64_t d_nupdates = 0;
    uint64_t d_nmoves   = 0;

    uint64_t d_nprops_inv  = 0;
    uint64_t d_nprops_cons = 0;

    uint64_t d_nconf = 0;

#ifndef NDEBUG
    struct
    {
      uint64_t d_add     = 0;
      uint64_t d_and     = 0;
      uint64_t d_ashr    = 0;
      uint64_t d_concat  = 0;
      uint64_t d_extract = 0;
      uint64_t d_eq      = 0;
      uint64_t d_ite     = 0;
      uint64_t d_mul     = 0;
      uint64_t d_not     = 0;
      uint64_t d_sext    = 0;
      uint64_t d_shl     = 0;
      uint64_t d_shr     = 0;
      uint64_t d_slt     = 0;
      uint64_t d_udiv    = 0;
      uint64_t d_ult     = 0;
      uint64_t d_urem    = 0;
      uint64_t d_xor     = 0;
    } d_ninv;
    struct
    {
      uint64_t d_add     = 0;
      uint64_t d_and     = 0;
      uint64_t d_ashr    = 0;
      uint64_t d_concat  = 0;
      uint64_t d_extract = 0;
      uint64_t d_eq      = 0;
      uint64_t d_ite     = 0;
      uint64_t d_mul     = 0;
      uint64_t d_not     = 0;
      uint64_t d_sext    = 0;
      uint64_t d_shl     = 0;
      uint64_t d_shr     = 0;
      uint64_t d_slt     = 0;
      uint64_t d_udiv    = 0;
      uint64_t d_ult     = 0;
      uint64_t d_urem    = 0;
      uint64_t d_xor     = 0;
    } d_ncons;
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
     * True to infer bounds for top-level inequalities for inverse value
     * computation.
     */
    bool use_ineq_bounds = false;
    /**
     * True to enable optimization for inverse_value computation of
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
  ~LocalSearch();

  /**
   * Initialize local search module.
   * Must be called after all options are configured and before nodes are
   * created.
   */
  void init();

  void set_max_nprops(uint64_t max) { d_max_nprops = max; }
  void set_max_nupdates(uint64_t max) { d_max_nupdates = max; }

  uint64_t mk_node(uint64_t size);
  uint64_t mk_node(OperatorKind kind,
                   uint64_t size,
                   const std::vector<uint64_t>& children);
  uint64_t mk_indexed_node(OperatorKind kind,
                           uint64_t size,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices);

  uint64_t mk_node(const BitVector& assignment, const BitVectorDomain& domain);
  uint64_t mk_node(OperatorKind kind,
                   const BitVectorDomain& domain,
                   const std::vector<uint64_t>& children);
  uint64_t mk_indexed_node(OperatorKind kind,
                           const BitVectorDomain& domain,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices);

  uint64_t invert_node(uint64_t id);

  /**
   * Get the assignment of the node given by id.
   * @param id The id of the node to query.
   */
  const BitVector& get_assignment(uint64_t id) const;
  /**
   * Set the assignment of the node given by id.
   * @param id The id of the node.
   * @param assignment The assignment to set.
   */
  void set_assignment(uint64_t id, const BitVector& assignment);
  /**
   * Get the domain of the node given by id.
   * @param id The id of the node to query.
   * @return The domain of the node given by id.
   */
  const BitVectorDomain& get_domain(uint64_t id) const;
  // void set_domain(uint64_t node, const BitVectorDomain& domain);

  /** Fix domain bit of given node at index 'idx' to 'value'. */
  void fix_bit(uint64_t id, uint32_t idx, bool value);

  /**
   * Register node as root.
   *
   * @note This not only adds `root` to `d_roots` but also registers unsat
   *       roots (cached in `d_roots_unsat`) and must therefore be called after
   *       initial assignment has been computed.
   *
   * @param root The id of the node to register as root.
   */
  void register_root(uint64_t root);
  /**
   * Determine if all roots are sat.
   * @return True if all roots are sat.
   */
  bool all_roots_sat() const { return d_roots_unsat.empty(); }
  /**
   * Get the number of unsat roots.
   * @return The number of unsat roots.
   */
  uint64_t get_num_roots_unsat() const { return d_roots_unsat.size(); }

  // TODO: incremental case:
  //       - we need to be able to unregister roots (assumptions)
  //       - we might want to exclude nodes that are not in the formula from
  //         cone updates

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

  Result move();

  /**
   * Set the log level.
   * @param level The level to set.
   */
  void set_log_level(uint32_t level) { d_log_level = level; }

 private:
  /**
   * Determine if given node is an inequality (ULT or SLT).
   * @param node The node to query.
   * @return True if `node` is an inequality.
   */
  static bool is_ineq_node(const BitVectorNode* node);
  /**
   * Determine if given node is a NOT node.
   * @param node The node to query.
   * @return True if `node` is a NOT node.
   */
  static bool is_not_node(const BitVectorNode* node);
  /**
   * Get node by id.
   * @param id The node id.
   * @return The node with the given id.
   */
  BitVectorNode* get_node(uint64_t id) const;
  /**
   * Determine if given node is a leaf node (its arity = 0).
   * @param node The node to query.
   * @return True if `node` is a leaf.
   */
  bool is_leaf_node(const BitVectorNode* node) const;
  /**
   * Determine if given node is a root node.
   * @param node The node to query.
   * @return True if `node` is a root.
   */
  bool is_root_node(const BitVectorNode* node) const;
  /**
   * Determine if given node is an inequality (ULT or SLT) root (this includes
   * negated inequalities).
   * @param node The node to query.
   * @return True if `node` is a (possibly negated) inequality root.
   */
  bool is_ineq_root(const BitVectorNode* node) const;
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
  void update_unsat_roots(BitVectorNode* root);
  /**
   * Compute min/max bounds for children of given node.
   *
   * This must be called after update_unsat_roots() has been called and the
   * assignment of all nodes has been computed/updated, i.e., the assignment is
   * consistent.
   *
   * @param node The node.
   */
  void compute_bounds(BitVectorNode* node);
  /**
   * Helper for computing bounds of children of root inequalities.
   * @param root The root node.
   * @param pos The position of the child to update, -1 for updating all
   *            children.
   */
  void update_bounds_aux(BitVectorNode* root, int32_t pos);
  /**
   * Update the assignment of the given node to the given assignment, and
   * recompute the assignment of all nodes in its cone of influence
   *
   * @param node The node to update.
   * @param assignment The new assignment of the given node.
   * @return The number of updated assignments.
   */
  uint64_t update_cone(BitVectorNode* node, const BitVector& assignment);
  /**
   * Select an input and a new assignment for that input by propagating the
   * given target value `t_root` for the given root along one path towards an
   * input.
   *
   * @param root The root to propagate from.
   * @param t_root The target value of the given root.
   * @return An object encapsulating all information necessary for that move.
   */
  LocalSearchMove select_move(BitVectorNode* root, const BitVector& t_root);

  /** The random number generator. */
  std::unique_ptr<RNG> d_rng;

  /** Map from node id to nodes. */
  NodesIdTable d_nodes;
  /** The set of roots. */
  std::vector<BitVectorNode*> d_roots;
  /** The set of unsatisfied roots. */
  std::unordered_set<BitVectorNode*> d_roots_unsat;
  /**
   * The set of (to be considered) top-level inequalities. Maps inequality
   * roots to their sat assignment (true for top-level inequalities, false for
   * negated inequality roots).
   *
   * @note This includes top-level inequalities and negated inequalities that
   *       are not roots but whose parents are a top-level NOT.
   */
  std::unordered_map<const BitVectorNode*, bool> d_roots_ineq;
  /** Map nodes to their parent nodes. */
  ParentsMap d_parents;

  /** Bit-vector one of size one, the target value for each root. */
  std::unique_ptr<BitVector> d_one;

  /** The log level. */
  uint32_t d_log_level = 0;
  /** The maximum number of propagations, 0 for unlimited. */
  uint64_t d_max_nprops = 0;
  /** The maximum number of cone updates, 0 for unlimited. */
  uint64_t d_max_nupdates = 0;
  /** The seed for the RNG. */
  uint32_t d_seed;
};

}  // namespace ls
}  // namespace bzla
#endif
