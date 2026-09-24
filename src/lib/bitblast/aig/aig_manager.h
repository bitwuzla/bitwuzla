/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BITBLAST_AIG_MANAGER_H
#define BZLA__BITBLAST_AIG_MANAGER_H

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "bitblast/aig/aig_node.h"

namespace bzla::bitblast {

// AigNodeUniqueTable
class AigNodeUniqueTable
{
 public:
  AigNodeUniqueTable();

  /**
   * @return Node data of the AND gate with the given children, or nullptr if
   *         it does not exist.
   */
  AigNodeData* find(uintptr_t left, uintptr_t right) const;
  /** Insert node data for an AND gate that is not yet in the table. */
  void insert(AigNodeData* d);
  void erase(const AigNodeData* d);

 private:
  size_t hash(uintptr_t left, uintptr_t right) const
  {
    // The keys are tagged pointers, whose low bits carry little entropy, so
    // mix multiplicatively and index with the high bits of the product.
    uint64_t h = static_cast<uint64_t>(left) * 0x9e3779b97f4a7c15ull
                 + static_cast<uint64_t>(right) * 0xc2b2ae3d27d4eb4full;
    // The number of buckets is always a power of two (see resize()), so
    // size() - 1 is an all-ones mask.
    return static_cast<size_t>(h >> 32) & (d_buckets.size() - 1);
  }
  void resize();

  size_t d_num_elements = 0;
  std::vector<AigNodeData*> d_buckets;
};

class AigManager
{
  friend class AigNodeData;

 public:
  struct Statistics
  {
    uint64_t num_ands   = 0;  // Current number of AND gates
    uint64_t num_consts = 0;  // Current number of AIG constants
    uint64_t num_shared = 0;  // Number of successful AND gate lookups
  };

  AigManager();
  ~AigManager();

  AigNode mk_false() { return d_false; }
  AigNode mk_true() { return d_true; }
  AigNode mk_const()
  {
    ++d_statistics.num_consts;
    return AigNode(new_data());
  }

  AigNode mk_not(const AigNode& a)
  {
    return AigNode(a.data(), !a.is_negated());
  }

  AigNode mk_and(const AigNode& a, const AigNode& b)
  {
    return rewrite_and(a, b);
  }

  /**
   * Get AigNode by id.
   * @param id The id of the AIG node.
   * @return The AIG node.
   */
  AigNode get_node(int64_t id) const;

  /** @return The current AIG id counter. */
  int64_t aig_id_counter() const { return d_aig_id_counter; }

  /** @return AIG statistics. */
  const Statistics& statistics() const;

 private:
  /** Counter for AIG ids. */
  int64_t d_aig_id_counter = AigNode::s_true_id;

  /** Returns the next free AIG id. */
  void init_id(AigNodeData* d);

  /**
   * Get the AND gate with the given children, constructing it if it does not
   * exist yet.
   *
   * @param left Left child of the AND gate.
   * @param right Right child of the AND gate.
   * @return Pointer to the node data of the AND gate.
   */
  AigNodeData* find_or_create_and(const AigNode& left, const AigNode& right);

  /**
   * Implements two-level AIG rewriting from [1].
   *
   * [1] Local Two-Level And-Inverter Graph Minimization without Blowup.
   *     Robert Brummayer, Armin Biere.
   */
  AigNode rewrite_and(const AigNode& left, const AigNode& right);

  /** Get children ids from AND gate. */
  std::pair<int64_t, int64_t> get_children(int64_t id) const;

  /**
   * Construct a new node data.
   */
  AigNodeData* new_data();

  /**
   * Delete given node data.
   */
  void garbage_collect(AigNodeData* d);

  /** Maps node id to node data and stores all created node data. */
  std::vector<std::unique_ptr<AigNodeData>> d_node_data;
  /** AND gate cache used for hash consing. */
  AigNodeUniqueTable d_unique_table;

  /** Indicates whether AIG manager is in garbage collection mode. */
  bool d_gc_mode = false;

  Statistics d_statistics;

  /** AIG nodes representing true/false. Make sure these get destroyed first. */
  AigNode d_true;
  AigNode d_false;
};

}  // namespace bzla::bitblast

#endif
