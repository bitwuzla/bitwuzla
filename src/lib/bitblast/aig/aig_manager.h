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
#include <unordered_map>
#include <unordered_set>

#include "bitblast/bitblaster.h"

namespace bzla::bb {

class AigNode;
using AigManager = BitInterface<AigNode>;
class AigNodeData;
class AigNodeUniqueTable;

/**
 * Wrapper around AigNodeData with automatic reference counting on
 * construction/destruction.
 */
class AigNode
{
  friend AigManager;
  friend class AigNodeData;

 public:
  AigNode() = default;
  ~AigNode();
  AigNode(const AigNode& other);
  AigNode& operator=(const AigNode& other);
  AigNode(AigNode&& other);
  AigNode& operator=(AigNode&& other);

  bool is_true() const;

  bool is_false() const;

  bool is_and() const;

  bool is_const() const;

  bool is_negated() const;

  const AigNode& operator[](int index) const;

  int64_t get_id() const;

 private:
  static const int64_t s_true_id = 1;

  // Should only be constructed via AigManager
  AigNode(AigNodeData* data, bool negated = false);

  bool is_null() const;
  uint64_t get_refs() const;

  AigNodeData* d_data = nullptr;
  // TODO: optimization hide flag in d_data pointer
  bool d_negated = false;
};

bool operator==(const AigNode& a, const AigNode& b);

bool operator<(const AigNode& a, const AigNode& b);

// AigNodeUniqueTable
class AigNodeUniqueTable
{
 public:
  AigNodeUniqueTable();

  // AigNodeData* lookup(const AigNode& left, const AigNode& right);
  std::pair<bool, AigNodeData*> insert(AigNodeData* d);
  void erase(const AigNodeData* d);

 private:
  size_t hash(const AigNode& left, const AigNode& right);
  void resize();

  size_t d_num_elements = 0;
  std::vector<AigNodeData*> d_buckets;
};

template <>
class BitInterface<AigNode>
{
  friend class AigNodeData;

 public:
  struct Statistics
  {
    uint64_t num_ands       = 0;  // Current number of AND gates
    uint64_t num_consts     = 0;  // Current number of AIG constants
    uint64_t num_shared = 0;  // Number of successful AND gate lookups
  };

  BitInterface<AigNode>();
  ~BitInterface<AigNode>();

  AigNode mk_false();
  AigNode mk_true();
  AigNode mk_bit();
  AigNode mk_not(const AigNode& a);
  AigNode mk_and(const AigNode& a, const AigNode& b);
  AigNode mk_or(const AigNode& a, const AigNode& b);
  AigNode mk_iff(const AigNode& a, const AigNode& b);
  AigNode mk_ite(const AigNode& c, const AigNode& a, const AigNode& b);

  /** @return AIG statistics. */
  const Statistics& statistics() const;

 private:
  /** Counter for AIG ids. */
  int64_t d_aig_id_counter = AigNode::s_true_id;

  /** Returns the next free AIG id. */
  void init_id(AigNodeData* d);

  /**
   * Find already constructed and gate with given children.
   *
   * @param left Left child of AND gate.
   * @param right Right child of AND gate.
   * @return Pointer to existing node data or nullptr if AND gate was not yet
   * constructed.
   */
  AigNodeData* find_or_create_and(const AigNode& left, const AigNode& right);

  /**
   * Implements two-level AIG rewriting from [1].
   *
   * [1] Local Two-Level And-Inverter Graph Minimization without Blowup.
   *     Robert Brummayer, Armin Biere.
   */
  AigNode rewrite_and(const AigNode& left, const AigNode& right);

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

  /** AIG node representing true. */
  AigNode d_true;
  /** AIG node representing false. */
  AigNode d_false;

  /** Indicates whether AIG manager is in garbage collection mode. */
  bool d_gc_mode = false;

  Statistics d_statistics;
};

}  // namespace bzla::bb

namespace std {

template <>
struct hash<bzla::bb::AigNode>
{
  size_t operator()(const bzla::bb::AigNode& aig) const
  {
    return static_cast<size_t>(aig.get_id());
  }
};

}  // namespace std

#endif
