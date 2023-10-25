/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__LS_LS_BV_H
#define BZLA__LS_LS_BV_H

#include <optional>
#include <string>

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
  /**
   * Create node.
   * @param kind     The node kind.
   * @param size     The bit-vector size of the node.
   * @param children The children, empty for NodeKind::CONST.
   * @param indices  The set of indices, empty for non-indexed nodes.
   * @param symbol   Optionally, a symbol string identifying the node, only
   *                 used for logging.
   * @return The index of the created node.
   */
  uint64_t mk_node(NodeKind kind,
                   uint64_t size,
                   const std::vector<uint64_t>& children    = {},
                   const std::vector<uint64_t>& indices     = {},
                   const std::optional<std::string>& symbol = std::nullopt);
  /**
   * Create node.
   * @param kind     The node kind.
   * @param domain   The associated bit-vector domain.
   * @param children The children, empty for NodeKind::CONST.
   * @param indices  The set of indices, empty for non-indexed nodes.
   * @param symbol   Optionally, a symbol string identifying the node, only
   *                 used for logging.
   * @return The index of the created node.
   */
  uint64_t mk_node(NodeKind kind,
                   const BitVectorDomain& domain,
                   const std::vector<uint64_t>& children    = {},
                   const std::vector<uint64_t>& indices     = {},
                   const std::optional<std::string>& symbol = std::nullopt);
  /**
   * Create const node.
   * @param assignment The current assignment of the node.
   * @param domain     The associated bit-vector domain.
   * @param symbol     Optionally, a symbol string identifying the node, only
   *                   used for logging.
   * @return The index of the created node.
   */
  uint64_t mk_node(const BitVector& assignment,
                   const BitVectorDomain& domain,
                   const std::optional<std::string>& symbol = std::nullopt);

  /**
   * Invert node given by id.
   * @param id The id of the node to invert.
   * @return The inverted node.
   */
  uint64_t invert_node(uint64_t id);

  /**
   * Get the domain of the node given by id.
   * @param id The id of the node to query.
   * @return The domain of the node given by id.
   */
  const BitVectorDomain& get_domain(uint64_t id) const;

  /** Fix domain bit of given node at index 'idx' to 'value'. */
  void fix_bit(uint64_t id, uint32_t idx, bool value);

  void compute_bounds(Node<BitVector>* node) override;

  void normalize() override;

 private:
  /**
   * Helper for creating a node.
   * @param kind     The node kind.
   * @param size     The bit-vector size of the node.
   * @param children The children, empty for NodeKind::CONST.
   * @param indices  The set of indices, empty for non-indexed nodes.
   * @param normalize True if this operation is to be registered for
   *                  normalization; always true for nodes created via the API.
   * @param symbol   Optionally, a symbol string identifying the node, only
   *                 used for logging.
   * @return The index of the created node.
   */
  uint64_t _mk_node(NodeKind kind,
                    uint64_t size,
                    const std::vector<uint64_t>& children    = {},
                    const std::vector<uint64_t>& indices     = {},
                    bool normalize                           = true,
                    const std::optional<std::string>& symbol = std::nullopt);
  /**
   * Helper for creating a node.
   * @param kind     The node kind.
   * @param domain   The associated bit-vector domain.
   * @param children The children, empty for NodeKind::CONST.
   * @param indices  The set of indices, empty for non-indexed nodes.
   * @param normalize True if this operation is to be registered for
   *                  normalization; always true for nodes created via the API.
   * @param symbol   Optionally, a symbol string identifying the node, only
   *                 used for logging.
   * @return The index of the created node.
   */
  uint64_t _mk_node(NodeKind kind,
                    const BitVectorDomain& domain,
                    const std::vector<uint64_t>& children    = {},
                    const std::vector<uint64_t>& indices     = {},
                    bool normalize                           = true,
                    const std::optional<std::string>& symbol = std::nullopt);
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

  /**
   * Helper to split index ranges of multiple extracts on the same child such
   * that none of the ranges are overlapping.
   * @param node The node with multiple extract parents.
   * @return A list of extract ranges, not overlapping.
   */
  std::vector<std::pair<uint64_t, uint64_t>> split_indices(BitVectorNode* node);
  /**
   * Normalize extract nodes.
   *
   * This normalizes a node with multiple extract nodes as parents, resulting
   * in overlapping extracts if not normalized.
   *
   * For each extract, its child will be replaced with a concat of only the
   * relevant slices of the child, where none of the slices of a node with
   * multiple extract parents are overlapping.
   *
   * @param node The node with multiple extract parents.
   */
  void normalize_extracts(BitVectorNode* node);
  /**
   * Helper to create an extract node during normalization.
   * @param child The child of the extract.
   * @param hi    The upper index.
   * @param lo    The lower index.
   * @return The extract.
   */
  BitVectorNode* mk_normalized_extract(BitVectorNode* child,
                                       uint64_t hi,
                                       uint64_t lo);
  /**
   * Helper to create a concat node during normalization.
   * @param child0 The child at index 0.
   * @param child1 The child at index 1.
   * @return The concat.
   */
  BitVectorNode* mk_normalized_concat(BitVectorNode* child0,
                                      BitVectorNode* child1);

  /**
   * Cache nodes that require normalization.
   * Currently, only children of extracts are normalized.
   */
  std::unordered_set<BitVectorNode*> d_to_normalize_nodes;
};

}  // namespace ls
}  // namespace bzla
#endif
