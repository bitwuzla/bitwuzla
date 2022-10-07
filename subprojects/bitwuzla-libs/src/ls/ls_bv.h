#ifndef BZLA__LS_LS_BV_H
#define BZLA__LS_LS_BV_H

#include "ls/ls.h"

namespace bzla {

class BitVector;

namespace ls {

class BitVectorDomain;
class BitVectorNode;

class LocalSearchBV : public LocalSearch<BitVector, BitVector, BitVectorNode>
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

  void compute_bounds(BitVectorNode* node) override;

  uint64_t mk_node(uint64_t size) override;
  uint64_t mk_node(OperatorKind kind,
                   uint64_t size,
                   const std::vector<uint64_t>& children) override;
  uint64_t mk_indexed_node(OperatorKind kind,
                           uint64_t size,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices) override;
  uint64_t mk_node(const BitVector& assignment, const BitVectorDomain& domain);
  uint64_t mk_node(OperatorKind kind,
                   const BitVectorDomain& domain,
                   const std::vector<uint64_t>& children);
  uint64_t mk_indexed_node(OperatorKind kind,
                           const BitVectorDomain& domain,
                           uint64_t child0,
                           const std::vector<uint64_t>& indices);

  uint64_t invert_node(uint64_t id) override;
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
   * Helper for computing bounds of children of root inequalities.
   * @param root The root node.
   * @param pos The position of the child to update, -1 for updating all
   *            children.
   */
  void update_bounds_aux(BitVectorNode* root, int32_t pos);
};

}  // namespace ls
}  // namespace bzla
#endif
