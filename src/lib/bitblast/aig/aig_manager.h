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
#include <new>
#include <vector>

#include "bitblast/aig/aig_node.h"

namespace bzla::bitblast {

// AigNodeUniqueTable
class AigNodeUniqueTable
{
 public:
  AigNodeUniqueTable(AigManager& mgr);

  /** @return Node data of the AND gate with the given children, if it exists. */
  AigNodeData* lookup(int32_t left, int32_t right) const;
  /** Insert node data of an AND gate that is not in the table yet. */
  void insert(AigNodeData* d);
  void erase(const AigNodeData* d);

 private:
  size_t hash(int32_t left, int32_t right) const;
  void resize();

  /** The manager owning the nodes, to resolve the ids of a collision chain. */
  AigManager& d_mgr;
  size_t d_num_elements = 0;
  /** Id of the first node of each collision chain, 0 if the chain is empty. */
  std::vector<uint32_t> d_buckets;
};

class AigManager
{
  friend class AigNodeData;
  friend class AigNodeUniqueTable;

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
  /**
   * Number of node data slots per block, see AigNodeBlock.
   *
   * Node data is allocated from blocks instead of individually, which saves
   * the 16 bytes of allocator overhead a single node costs and makes the id of
   * a node its position, so that neither a map from id to node data nor an id
   * in the node data is needed. Only the pages a block actually uses are
   * touched, which keeps a block cheap for the short-lived managers that only
   * bit-blast a few nodes, e.g. for AIG scores.
   */
  static constexpr size_t s_block_size =
      (AigNodeBlock::s_bytes - sizeof(AigNodeBlock)) / sizeof(AigNodeData);

  /** Counter for AIG ids. */
  int64_t d_aig_id_counter = AigNode::s_true_id;

  /** @return Node data of the node with the given positive id. */
  AigNodeData* node_data(int64_t id) const
  {
    assert(id > 0);
    assert(id < d_aig_id_counter);
    AigNodeData* d = slot(static_cast<size_t>(id) - 1);
    assert(d->id() == static_cast<uint32_t>(id));
    assert(!d->d_dead);
    return d;
  }

  /** @return The node data slot at the given position. */
  AigNodeData* slot(size_t pos) const
  {
    assert(pos / s_block_size < d_blocks.size());
    std::byte* block = d_blocks[pos / s_block_size].get();
    return reinterpret_cast<AigNodeData*>(
        block + sizeof(AigNodeBlock)
        + (pos % s_block_size) * sizeof(AigNodeData));
  }

  /** @return An uninitialized slot for the next id. */
  void* new_slot();

  /**
   * Find already constructed and gate with given children.
   *
   * @param left Left child of AND gate.
   * @param right Right child of AND gate.
   * @return Pointer to existing node data or nullptr if AND gate was not yet
   * constructed.
   */
  AigNodeData* find_or_create_and(int32_t left, int32_t right);

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

  /** Deleter for the aligned allocation of a node data block. */
  struct BlockDeleter
  {
    void operator()(std::byte* block) const
    {
      ::operator delete(block, std::align_val_t(AigNodeBlock::s_bytes));
    }
  };

  /** Blocks of `s_block_size` node data slots, indexed by node id. */
  std::vector<std::unique_ptr<std::byte[], BlockDeleter>> d_blocks;
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
