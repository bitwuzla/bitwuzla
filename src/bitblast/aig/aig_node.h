/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BITBLAST_AIG_NODE_H
#define BZLA__BITBLAST_AIG_NODE_H

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <type_traits>

namespace bzla::bitblast {

class AigManager;
class AigNodeData;

/**
 * Header of a block of node data.
 *
 * Node data is not allocated individually but in blocks that are aligned to
 * their size, so that a node finds the block it is stored in, and with it its
 * manager and its id, by masking its own address. See AigManager for the
 * allocation of the blocks.
 */
struct AigNodeBlock
{
  /** Size of a block in bytes. A block is aligned to its size. */
  static constexpr size_t s_bytes = 1 << 20;

  /** @return The block the given node data is stored in. */
  static AigNodeBlock* of(const AigNodeData* d)
  {
    return reinterpret_cast<AigNodeBlock*>(
        reinterpret_cast<uintptr_t>(d)
        & ~(static_cast<uintptr_t>(s_bytes) - 1));
  }

  /** The manager that owns the node data of this block. */
  AigManager* d_mgr;
  /** Id of the first node data slot of this block. */
  uint32_t d_base_id;
};

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
  AigNode(AigNode&& other) noexcept;
  AigNode& operator=(AigNode&& other) noexcept;

  bool is_true() const;

  bool is_false() const;

  bool is_and() const;

  bool is_const() const;

  bool is_negated() const { return d_data & 1; }

  /**
   * @return The given child of an AND node. Children are stored as ids, so
   *         this looks the node up in the manager and returns it by value.
   */
  AigNode operator[](int index) const;

  /** @return The id of the given child of an AND node. */
  int64_t child_id(int index) const;

  int64_t get_id() const;

  uint32_t parents() const;

  /**
   * @return Whether this node keeps a CNF variable of its own, see
   *         require_cnf_var().
   */
  bool requires_cnf_var() const;

  /**
   * Request that this node keeps a CNF variable of its own, i.e., that the CNF
   * encoder does not merge it into the gate of its parent. A merged node has no
   * CNF variable and is invisible to everything that maps between CNF and AIG.
   * The request lives in the node data, so it survives resetting the encoder.
   *
   * @note No-op for anything but AND nodes, only those are ever merged.
   */
  void require_cnf_var() const;

  bool is_null() const { return d_data == 0; }

  std::string str() const;

 private:
  static const int64_t s_true_id = 1;

  // Should only be constructed via AigManager
  AigNode(AigNodeData* data, bool negated = false);

  AigNodeData* data() const
  {
    return reinterpret_cast<AigNodeData*>(d_data & ~1);
  }

  uintptr_t d_data = 0;
};

inline bool
operator==(const AigNode& a, const AigNode& b)
{
  return a.get_id() == b.get_id();
}

inline bool
operator<(const AigNode& a, const AigNode& b)
{
  return a.get_id() < b.get_id();
}

/**
 * AigNodeData storing all node data.
 */
class AigNodeData
{
  friend class AigNode;
  friend AigManager;
  friend class AigNodeUniqueTable;

 public:
  /**
   * A node derives its id and its manager from its own address, see id() and
   * mgr(), so a copy outside of a block would be garbage.
   */
  AigNodeData(const AigNodeData&)            = delete;
  AigNodeData& operator=(const AigNodeData&) = delete;

  void inc_refs()
  {
    if (d_refs == s_max_refs)
    {
      spill_refs();
    }
    else
    {
      ++d_refs;
    }
  }
  void dec_refs()
  {
    if (release())
    {
      gc();
    }
  }

 private:
  /**
   * Largest reference count a node stores itself, the excess goes to the
   * manager, see spill_refs(). A node is referenced by its parents and by every
   * AigNode that holds it, and the latter dominates by orders of magnitude.
   * Most of the 32 bits go here because a node above the limit spills on every
   * single reference it gains or loses, not once. Unlike the parent count below
   * this one has to stay exact: it decides when a node is freed, so a lost
   * reference is a use after free and a surplus one a node that never dies.
   */
  static constexpr uint32_t s_max_refs = (1u << 19) - 1;
  /**
   * Largest number of parents a node counts. This one saturates instead of
   * spilling, and stays saturated once it is: parents() is only ever asked
   * whether it is greater than one, so a node that keeps answering yes is
   * merely never merged into the gate of a parent and never dropped by ite
   * extraction, which is the conservative answer and costs it a CNF variable.
   */
  static constexpr uint32_t s_max_parents = (1u << 11) - 1;

  AigNodeData() : d_refs(0), d_parents(0), d_requires_cnf_var(0), d_dead(0) {}
  AigNodeData(int32_t left, int32_t right)
      : d_refs(0),
        d_parents(0),
        d_requires_cnf_var(0),
        d_dead(0),
        d_left(left),
        d_right(right)
  {
  }

  /**
   * Move a reference that does not fit d_refs to the manager. The references of
   * a node are d_refs plus what the manager holds for it, and the manager holds
   * something only while d_refs is saturated. The node of true/false is not
   * counted, its d_refs stays saturated, see AigManager::AigManager().
   */
  void spill_refs();
  /**
   * Take a spilled reference back, or lower d_refs if none was spilled. No-op
   * for the node of true/false.
   */
  void unspill_refs();

  /** @return True if the last reference was released. */
  bool release()
  {
    assert(d_refs > 0);
    if (d_refs == s_max_refs)
    {
      unspill_refs();
      return false;
    }
    return --d_refs == 0;
  }

  /** Count one more parent, saturating at s_max_parents. */
  void inc_parents()
  {
    if (d_parents < s_max_parents)
    {
      ++d_parents;
    }
  }
  /** Count one less parent, unless the count saturated. */
  void dec_parents()
  {
    if (d_parents < s_max_parents)
    {
      --d_parents;
    }
  }

  void gc();

  /** @return The manager owning this node, which is stored per block. */
  AigManager& mgr() const { return *AigNodeBlock::of(this)->d_mgr; }

  /**
   * @return The id of this node, which is the position of its slot. The id is
   *         not stored but derived from the address of the node.
   */
  uint32_t id() const
  {
    const AigNodeBlock* block = AigNodeBlock::of(this);
    uintptr_t offset          = reinterpret_cast<uintptr_t>(this)
                       - reinterpret_cast<uintptr_t>(block)
                       - sizeof(AigNodeBlock);
    return block->d_base_id
           + static_cast<uint32_t>(offset / sizeof(AigNodeData));
  }

  /** Reference count, spilling to the manager above s_max_refs. */
  uint32_t d_refs : 19;
  /** Number of parents, saturating at s_max_parents. */
  uint32_t d_parents : 11;
  /**
   * True if the node must not be merged into its parent's gate, see
   * AigNode::require_cnf_var().
   */
  uint32_t d_requires_cnf_var : 1;
  /** True if the node was garbage collected, see AigManager::node_data(). */
  uint32_t d_dead : 1;
  /** Id of the left child of an AND gate, 0 if this is not an AND gate. */
  int32_t d_left = 0;
  /** Id of the right child of an AND gate, 0 if this is not an AND gate. */
  int32_t d_right = 0;
  /** Id of the next node in the collision chain, 0 if this is the last one. */
  uint32_t d_next = 0;
};

inline bool
AigNode::is_true() const
{
  return data()->id() == AigNode::s_true_id && !is_negated();
}

inline bool
AigNode::is_false() const
{
  return data()->id() == AigNode::s_true_id && is_negated();
}

inline bool
AigNode::is_and() const
{
  return data()->d_left != 0;
}

inline bool
AigNode::is_const() const
{
  return !is_and() && !is_true() && !is_false();
}

inline int64_t
AigNode::child_id(int index) const
{
  assert(is_and());
  assert(index == 0 || index == 1);
  return index == 0 ? data()->d_left : data()->d_right;
}

inline int64_t
AigNode::get_id() const
{
  // only happens if constructed with default constructor
  if (is_null())
  {
    return 0;
  }
  int64_t id = data()->id();
  return is_negated() ? -id : id;
}

inline uint32_t
AigNode::parents() const
{
  assert(!is_null());
  return data()->d_parents;
}

inline bool
AigNode::requires_cnf_var() const
{
  assert(!is_null());
  return data()->d_requires_cnf_var;
}

inline void
AigNode::require_cnf_var() const
{
  assert(!is_null());
  if (is_and())
  {
    data()->d_requires_cnf_var = 1;
  }
}

/** The AIG is the largest structure Bitwuzla builds, a node must not grow. */
static_assert(sizeof(AigNodeData) == 16, "AigNodeData must stay 16 bytes");
/**
 * A block is freed without destroying the node data in it, see
 * AigManager::BlockDeleter, so node data must not own anything.
 */
static_assert(std::is_trivially_destructible_v<AigNodeData>,
              "AigNodeData must be trivially destructible");

std::ostream& operator<<(std::ostream& out, const AigNode& aig);

}  // namespace bzla::bitblast

namespace std {

template <>
struct hash<bzla::bitblast::AigNode>
{
  size_t operator()(const bzla::bitblast::AigNode& aig) const
  {
    return static_cast<size_t>(aig.get_id());
  }
};

}  // namespace std

#endif
