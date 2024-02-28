/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
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
  friend AigNodeData;

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

  bool is_negated() const { return d_negated; }

  const AigNode& operator[](int index) const;

  int64_t get_id() const;

  uint32_t parents() const;

 private:
  static const int64_t s_true_id = 1;

  // Should only be constructed via AigManager
  AigNode(AigNodeData* data, bool negated = false);

  bool is_null() const { return d_data == nullptr; }

  uint64_t get_refs() const;

  AigNodeData* d_data = nullptr;
  // TODO: optimization hide flag in d_data pointer
  bool d_negated = false;
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
  AigNodeData(AigManager* mgr) : d_mgr(mgr) {}
  AigNodeData(AigManager* mgr, const AigNode& left, const AigNode& right)
      : d_mgr(mgr), d_left(left), d_right(right)
  {
  }

  void gc();

  /** Pointer to AIG Manager to allow automatic deletion. */
  AigManager* d_mgr = nullptr;

  /** AIG node id. */
  int64_t d_id = 0;
  /** Reference count. */
  uint32_t d_refs = 0;
  /** Number of parents. */
  uint32_t d_parents = 0;
  /** Left child of AND gate. */
  AigNode d_left;
  /** Right child of AND gate. */
  AigNode d_right;

  /** Next pointer for collision chain. */
  AigNodeData* next = nullptr;
};

inline bool
AigNode::is_true() const
{
  return d_data->d_id == AigNode::s_true_id && !is_negated();
}

inline bool
AigNode::is_false() const
{
  return d_data->d_id == AigNode::s_true_id && is_negated();
}

inline bool
AigNode::is_and() const
{
  return !d_data->d_left.is_null();
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
    return d_data->d_left;
  }
  assert(index == 1);
  return d_data->d_right;
}

inline int64_t
AigNode::get_id() const
{
  // only happens if constructed with default constructor
  if (is_null())
  {
    return 0;
  }
  return is_negated() ? -d_data->d_id : d_data->d_id;
}

inline uint32_t
AigNode::parents() const
{
  assert(!is_null());
  return d_data->d_parents;
}

inline uint64_t
AigNode::get_refs() const
{
  assert(!is_null());
  return d_data->d_refs;
}

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
