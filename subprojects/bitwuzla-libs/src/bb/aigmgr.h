#ifndef BZLA__BB_AIGMGR_H
#define BZLA__BB_AIGMGR_H

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <unordered_map>
#include <unordered_set>

#include "bb/bitblast.h"

namespace bzla::bb {

class AigNode;
using AigManager = BitInterface<AigNode>;
class AigNodeData;

/**
 * Wrapper around AigNodeData with automatic reference counting on
 * construction/destruction.
 */
class AigNode
{
  friend AigManager;
  friend class AigNodeData;

 public:
  static const int64_t s_true_id = 1;

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

  bool operator==(const AigNode& other) const;

  int64_t get_id() const;

 private:
  // Should only be constructed via AigManager
  AigNode() = default;
  AigNode(AigNodeData* data, bool negated = false);

  bool is_null() const;

  AigNodeData* d_data = nullptr;
  // TODO: optimization hide flag in d_data pointer
  bool d_negated = false;
};

template <>
class BitInterface<AigNode>
{
  friend class AigNodeData;

 public:
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

 private:
  /** Counter for AIG ids. */
  int64_t d_aig_id_counter = AigNode::s_true_id;

  /** Returns the next free AIG id. */
  int64_t next_id();

  /**
   * Find already constructed and gate with given children.
   *
   * @param left Left child of AND gate.
   * @param right Right child of AND gate.
   * @return Pointer to existing node data or nullptr if AND gate was not yet
   * constructed.
   */
  AigNodeData* find_and(const AigNode& left, const AigNode& right);

  /**
   * Construct a new node data.
   */
  AigNodeData* new_data();

  /**
   * Construct new AND node data.
   *
   * @param left Left child of AND gate.
   * @param right Right child of AND gate.
   */
  AigNodeData* new_data(const AigNode& left, const AigNode& right);

  /**
   * Delete given node data.
   */
  void delete_data(AigNodeData* d);

  /** Hash node data based on the AND gate children used for hash consing. */
  struct AigNodeDataHash
  {
    size_t operator()(const AigNodeData* d) const;
  };

  /** Compare node data based on AND gate children. Used for hash consing. */
  struct AigNodeDataKeyEqual
  {
    bool operator()(const AigNodeData* d0, const AigNodeData* d1) const;
  };

  /** Maps node id to node data and stores all created node data. */
  std::unordered_map<int64_t, std::unique_ptr<AigNodeData>> d_node_data;
  /** AND gate cache used for hash consing. */
  std::unordered_set<AigNodeData*, AigNodeDataHash, AigNodeDataKeyEqual>
      d_unique_ands;

  /** AIG node representing true. */
  AigNode d_true;
  /** AIG node representing false. */
  AigNode d_false;

  struct
  {
    uint64_t num_ands   = 0;
    uint64_t num_consts = 0;
  } d_statistics;
};

}  // namespace bzla::bb

namespace std {

template <>
struct hash<bzla::bb::AigNode>
{
  size_t operator()(const bzla::bb::AigNode& aig) const { return aig.get_id(); }
};

}  // namespace std

#endif
