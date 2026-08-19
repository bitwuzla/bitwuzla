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
#include <cstdint>
#include <functional>
#include <string>

namespace bzla::bitblast {

class AigManager;
class AigNodeData;

/**
 * Wrapper around AigNodeData with automatic reference counting on
 * construction/destruction.
 */
class AigNode
{
  friend AigManager;

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

  const AigNode& operator[](int index) const;

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

  void reset() { d_data = 0; }

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
  AigNodeData() = delete;
  ~AigNodeData() { assert(d_refs == 0); }

  void inc_refs() { ++d_refs; }
  void dec_refs()
  {
    assert(d_refs > 0);
    --d_refs;
    if (d_refs == 0)
    {
      gc();
    }
  }

 private:
  AigNodeData(uint32_t id) : d_id(id), d_parents(0), d_requires_cnf_var(0) {}
  AigNodeData(uint32_t id, const AigNode& left, const AigNode& right)
      : d_id(id),
        d_left(left),
        d_right(right),
        d_parents(0),
        d_requires_cnf_var(0)
  {
  }

  void gc();

  /**
   * AIG node id, also the position of the node data, see AigManager. The
   * manager refuses to create a node whose id does not fit.
   */
  uint32_t d_id = 0;
  /** Reference count. */
  uint32_t d_refs = 0;
  /** Left child of AND gate. */
  AigNode d_left;
  /** Right child of AND gate. */
  AigNode d_right;
  /**
   * Number of parents. Shares its 4 bytes with d_requires_cnf_var, 2^31-1
   * parents is far beyond anything reachable.
   */
  uint32_t d_parents : 31;
  /**
   * True if the node must not be merged into its parent's gate, see
   * AigNode::require_cnf_var().
   */
  uint32_t d_requires_cnf_var : 1;
  /** Id of the next node in the collision chain, 0 if this is the last one. */
  uint32_t d_next = 0;
};

inline bool
AigNode::is_true() const
{
  return data()->d_id == AigNode::s_true_id && !is_negated();
}

inline bool
AigNode::is_false() const
{
  return data()->d_id == AigNode::s_true_id && is_negated();
}

inline bool
AigNode::is_and() const
{
  return !data()->d_left.is_null();
}

inline bool
AigNode::is_const() const
{
  return !is_and() && !is_true() && !is_false();
}

inline const AigNode&
AigNode::operator[](int index) const
{
  assert(is_and());
  if (index == 0)
  {
    return data()->d_left;
  }
  assert(index == 1);
  return data()->d_right;
}

inline int64_t
AigNode::get_id() const
{
  // only happens if constructed with default constructor
  if (is_null())
  {
    return 0;
  }
  int64_t id = data()->d_id;
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
static_assert(sizeof(AigNodeData) == 32, "AigNodeData must stay 32 bytes");

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
