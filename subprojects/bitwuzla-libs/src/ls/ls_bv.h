#ifndef BZLA__LS_LS_BV_H
#define BZLA__LS_LS_BV_H

#include "ls/ls.h"

namespace bzla {

class BitVector;

namespace ls {

class BitVectorDomain;
class BitVectorNode;

class LocalSearchBV : public LocalSearch<BitVector>
{
 public:
  /**
   * Constructor.
   * @param max_nprops The maximum number of propagations to perform. Zero
   *                   if unlimited.
   * @param max_nupdates The maximum number of cone updates to perform. Zero
   *                     if unlimited.
   * @param seed The initial seed for the random number generator.
   */
  LocalSearchBV(uint64_t max_nprops,
                uint64_t max_nupdates,
                uint32_t seed = 1234);

  void compute_bounds(Node<BitVector>* node) override;

  uint64_t mk_node(uint64_t size) override;
  uint64_t mk_node(NodeKind kind,
                   uint64_t size,
                   const std::vector<uint64_t>& children) override;
  uint64_t mk_indexed_node(NodeKind kind,
                           uint64_t size,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices) override;
  uint64_t mk_node(const BitVector& assignment, const BitVectorDomain& domain);
  uint64_t mk_node(NodeKind kind,
                   const BitVectorDomain& domain,
                   const std::vector<uint64_t>& children);
  uint64_t mk_indexed_node(NodeKind kind,
                           const BitVectorDomain& domain,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices);

  uint64_t invert_node(uint64_t id) override;

  void normalize() override;

  /**
   * Get the domain of the node given by id.
   * @param id The id of the node to query.
   * @return The domain of the node given by id.
   */
  const BitVectorDomain& get_domain(uint64_t id) const;

  /** Fix domain bit of given node at index 'idx' to 'value'. */
  void fix_bit(uint64_t id, uint32_t idx, bool value);

 private:
  /**
   * Auxiliary function for creating indexed nodes.
   * @param kind    The kind of the node to create.
   * @param domain  The associated bit-vector domain.
   * @param child0  The child; all indexed bit-vector operations are unary.
   * @param indices The set of indices.
   * @param register_for_normalize
   *                True if this operation is to be registered for
   *                normalization; always true for nodes created via the API.
   * @return The index of the created node.
   */
  uint64_t _mk_indexed_node(NodeKind kind,
                            const BitVectorDomain& domain,
                            uint64_t child0,
                            const std::vector<uint64_t>& indices,
                            bool register_for_normalize);
  /**
   * Get node by id.
   * @param id The node id.
   * @return The node with the given id.
   */
  BitVectorNode* get_node(uint64_t id) const;
  /**
   * Helper for computing bounds of children of root inequalities.
   * @param root The root node.
   * @param pos The position of the child to update, -1 for updating all
   *            children.
   */
  void update_bounds_aux(BitVectorNode* root, int32_t pos);

  std::vector<std::pair<uint64_t, uint64_t>> split_indices(BitVectorNode* node);
  void normalize_extracts(BitVectorNode* node);
  BitVectorNode* mk_normalized_extract(BitVectorNode* child,
                                       uint64_t hi,
                                       uint64_t lo);
  BitVectorNode* mk_normalized_concat(BitVectorNode* child0,
                                      BitVectorNode* child1);

  std::unordered_set<BitVectorNode*> d_to_normalize_nodes;
};

}  // namespace ls
}  // namespace bzla

namespace std {
template <>
struct hash<std::pair<uint64_t, uint64_t>>
{
  /**
   * Hash function for pair of uint64_t.
   * @param p The pair.
   * @return The hash value.
   */
  size_t operator()(const std::pair<uint64_t, uint64_t>& p) const;
};
}  // namespace std

#endif
