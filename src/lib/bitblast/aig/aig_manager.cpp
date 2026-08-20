/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bitblast/aig/aig_manager.h"

#include <cstdlib>
#include <new>

namespace bzla::bitblast {

// AigNodeUniqueTable

AigNodeUniqueTable::AigNodeUniqueTable(AigManager& mgr) : d_mgr(mgr)
{
  d_buckets.resize(16, 0);
}

AigNodeData*
AigNodeUniqueTable::lookup(int32_t left, int32_t right) const
{
  // Check collision chain.
  uint32_t cur = d_buckets[hash(left, right)];
  while (cur != 0)
  {
    AigNodeData* d = d_mgr.node_data(cur);
    if (d->d_left == left && d->d_right == right)
    {
      return d;
    }
    cur = d->d_next;
  }
  return nullptr;
}

void
AigNodeUniqueTable::insert(AigNodeData* d)
{
  assert(lookup(d->d_left, d->d_right) == nullptr);
  if (d_num_elements == d_buckets.size())
  {
    resize();
  }
  size_t h = hash(d->d_left, d->d_right);
  assert(d->d_next == 0);
  d->d_next    = d_buckets[h];
  d_buckets[h] = d->id();

  ++d_num_elements;
}

void
AigNodeUniqueTable::erase(const AigNodeData* d)
{
  size_t h     = hash(d->d_left, d->d_right);
  uint32_t cur = d_buckets[h];
  assert(cur != 0);

  // Should not happen
  if (cur == 0)
  {
    return;
  }

  // Find data in collision chain.
  AigNodeData* prev = nullptr;
  AigNodeData* c    = nullptr;
  while (cur != 0)
  {
    c = d_mgr.node_data(cur);
    if (c->d_left == d->d_left && c->d_right == d->d_right)
    {
      break;
    }
    prev = c;
    cur  = c->d_next;
  }
  assert(cur != 0);

  // Update collision chain.
  if (prev == nullptr)
  {
    d_buckets[h] = c->d_next;
  }
  else
  {
    prev->d_next = c->d_next;
  }
  --d_num_elements;
}

size_t
AigNodeUniqueTable::hash(int32_t left, int32_t right) const
{
  size_t lhs = static_cast<size_t>(std::abs(left));
  size_t rhs = static_cast<size_t>(std::abs(right));
  size_t h   = 547789289u * lhs + 786695309u * rhs;
  // The number of buckets is always a power of two (see resize()), so size() -
  // 1 is an all-ones mask.
  return h & (d_buckets.size() - 1);
}

void
AigNodeUniqueTable::resize()
{
  auto buckets = std::move(d_buckets);

  d_buckets.clear();
  // Double the number of buckets, keeping it a power of two.
  d_buckets.resize(buckets.size() * 2, 0);

  // Rehash elements.
  for (uint32_t cur : buckets)
  {
    while (cur != 0)
    {
      AigNodeData* d = d_mgr.node_data(cur);
      size_t h       = hash(d->d_left, d->d_right);
      uint32_t next  = d->d_next;
      d->d_next      = d_buckets[h];
      d_buckets[h]   = cur;
      cur            = next;
    }
  }
}

// BitNodeInterface<AigNode>

AigManager::AigManager()
    : d_unique_table(*this),
      d_true(new_data(), false),
      d_false(d_true.data(), true)
{
  assert(d_true.get_id() == AigNode::s_true_id);
  assert(d_false.get_id() == -AigNode::s_true_id);
  // Every constant bit references the node of true/false, which would keep its
  // count above the limit and send every copy of a constant through
  // d_refs_overflow. The manager holds the node until it is destroyed itself,
  // so it needs no count: saturate it for good, see AigNodeData::spill_refs().
  d_true.data()->d_refs = AigNodeData::s_max_refs;
}

AigManager::~AigManager() {}

const AigManager::Statistics&
AigManager::statistics() const
{
  return d_statistics;
}

void*
AigManager::new_slot()
{
  assert(d_aig_id_counter > 0);
  // Child ids are signed 32-bit integers, see AigNodeData::d_left.
  if (d_aig_id_counter > INT32_MAX)
  {
    throw std::bad_alloc();
  }
  size_t pos = static_cast<size_t>(d_aig_id_counter) - 1;
  if (pos == d_blocks.size() * s_block_size)
  {
    std::byte* block = static_cast<std::byte*>(::operator new(
        AigNodeBlock::s_bytes, std::align_val_t(AigNodeBlock::s_bytes)));
    new (block) AigNodeBlock{this, static_cast<uint32_t>(d_aig_id_counter)};
    d_blocks.emplace_back(block);
  }
  ++d_aig_id_counter;
  return slot(pos);
}

AigNodeData*
AigManager::find_or_create_and(int32_t left, int32_t right)
{
  assert(std::abs(left) < std::abs(right));
  AigNodeData* d = d_unique_table.lookup(left, right);
  if (d != nullptr)
  {
    ++d_statistics.num_shared;
    return d;
  }

  void* mem = new_slot();
  d         = new (mem) AigNodeData(left, right);
  // The children are ids and thus hold no reference of their own.
  for (int32_t child : {left, right})
  {
    AigNodeData* c = node_data(std::abs(child));
    c->inc_refs();
    c->inc_parents();
  }
  d_unique_table.insert(d);
  ++d_statistics.num_ands;
  return d;
}

AigNode
AigManager::rewrite_and(const AigNode& l, const AigNode& r)
{
  const auto true_id  = AigNode::s_true_id;
  const auto false_id = -AigNode::s_true_id;
  auto left           = l.get_id();
  auto right          = r.get_id();
  do
  {
    /** Optimization level 1 */

    // Neutrality rule
    //   shape:  a /\ 1
    //   result: a
    //
    // Idempotence rule
    //   shape:     a /\ b
    //   condition: a = b
    //   result:    a
    if (left == true_id || left == right)
    {
      return get_node(right);
    }
    if (right == true_id)
    {
      return get_node(left);
    }
    // Boundedness rule
    //   shape:  a /\ 0
    //   result: 0
    //
    // Contradiction rule
    //   shape:     a /\ ~b
    //   condition: a = b
    //   result:    0
    if (left == false_id || right == false_id || left == -right)
    {
      return d_false;
    }

    const auto [a, b] = get_children(left);
    const auto [c, d] = get_children(right);
    bool left_is_and  = a != 0;
    bool right_is_and = c != 0;
    bool left_is_neg  = left < 0;
    bool right_is_neg = right < 0;

    /** Optimization level 2 */

    // Contradiction rule (asymmetric)
    //   shape:     (a /\ b) /\ c
    //   condition: (a = ~c) \/ (b = ~c)
    //   result:    0
    if (!left_is_neg && left_is_and && (a == -right || b == -right))
    {
      return d_false;
    }
    if (!right_is_neg && right_is_and && (c == -left || d == -left))
    {
      return d_false;
    }

    // Contradiction rule (symmetric)
    //   shape:     (a /\ b) /\ (c /\ d)
    //   condition: (a = ~c) \/ (a = ~d) \/ (b = ~c) \/ (b = ~d)
    //   result:    0
    if (!left_is_neg && !right_is_neg && left_is_and && right_is_and
        && (a == -c || a == -d || b == -c || b == -d))
    {
      return d_false;
    }

    // Subsumption rule (asymmetric)
    //   shape:     ~(a /\ b) /\ c
    //   condition: (a = ~c) \/ (b = ~c)
    //   result:    c
    if (left_is_neg && left_is_and && (a == -right || b == -right))
    {
      return get_node(right);
    }
    if (right_is_neg && right_is_and && (c == -left || d == -left))
    {
      return get_node(left);
    }

    // Subsumption rule (symmetric)
    //   shape:     ~(a /\ b) /\ (c /\ d)
    //   condition: (a = ~c) \/ (a = ~d) \/ (b = ~c) \/ (b = ~d)
    //   result:    c /\ d
    if (left_is_neg && !right_is_neg && left_is_and && right_is_and
        && (a == -c || a == -d || b == -c || b == -d))
    {
      return get_node(right);
    }
    if (right_is_neg && !left_is_neg && right_is_and && left_is_and
        && (c == -a || c == -b || d == -a || d == -b))
    {
      return get_node(left);
    }

    // Idempotence rule
    //   shape:     (a /\ b) /\ c
    //   condition: (a = c) \/ (b = c)
    //   result:    (a /\ b)
    if (!left_is_neg && left_is_and && (a == right || b == right))
    {
      return get_node(left);
    }
    if (!right_is_neg && right_is_and && (c == left || d == left))
    {
      return get_node(right);
    }

    // Resolution rule
    //   shape:     ~(a /\ b) /\ ~(c /\ d)
    //   condition: (a = d) /\ (b = ~c)
    //   result:    ~a
    if (left_is_neg && right_is_neg && left_is_and && right_is_and)
    {
      if ((a == c && b == -d) || (a == d && b == -c))
      {
        return get_node(-a);
      }
      if ((d == b && c == -a) || (d == a && c == -b))
      {
        return get_node(-d);
      }
    }

    /** Optimization level 3 **/

    // Substitution rule (asymmetric)
    //   shape:     ~(a /\ b) /\ c
    //   condition: b = c
    //   result:    ~a /\ c
    if (left_is_neg && left_is_and)
    {
      // (a = c) -> ~b /\ c
      if (a == right)
      {
        left = -b;
        continue;
      }
      // (b = c) -> ~a /\ c
      if (b == right)
      {
        left = -a;
        continue;
      }
    }
    if (right_is_neg && right_is_and)
    {
      if (c == left)
      {
        right = -d;
        continue;
      }
      else if (d == left)
      {
        right = -c;
        continue;
      }
    }

    // Substitution rule (symmetric)
    //   shape:     ~(a /\ b) /\ (c /\ d)
    //   condition: b = c
    //   result:    ~a /\ (c /\ d)
    if (left_is_neg && !right_is_neg && left_is_and && right_is_and)
    {
      // (a = c) \/ (a = d) -> ~b /\ (c /\ d)
      if (a == c || a == d)
      {
        left = -b;
        continue;
      }
      // (b = c) \/ (b = d) -> ~a /\ (c /\ d)
      if (b == c || b == d)
      {
        left = -a;
        continue;
      }
    }
    if (right_is_neg && !left_is_neg && right_is_and && left_is_and)
    {
      // (a = c) \/ (a = d) -> ~b /\ (c /\ d)
      if (c == a || c == b)
      {
        right = -d;
        continue;
      }
      // (b = c) \/ (b = d) -> ~a /\ (c /\ d)
      if (d == a || d == b)
      {
        right = -c;
        continue;
      }
    }

    /** Optimization level 4 */

    // Idempotence rule
    //   shape: (a /\ b) /\ (c /\ d)
    if (!left_is_neg && !right_is_neg && left_is_and && right_is_and)
    {
      // (a = c) \/ (b = c)
      if (a == c || b == c)
      {
        right = d;
        continue;
      }
      // (a = d) \/ (b = d)
      if (a == d || b == d)
      {
        right = c;
        continue;
      }
    }

    break;
  } while (true);

  // Normalize ANDs
  if (std::abs(left) > std::abs(right))
  {
    std::swap(left, right);
  }

  // create AND with left, right
  AigNodeData* d = find_or_create_and(static_cast<int32_t>(left),
                                      static_cast<int32_t>(right));
  return AigNode(d);
}

AigNode
AigManager::get_node(int64_t id) const
{
  return AigNode(node_data(std::abs(id)), id < 0);
}

std::pair<int64_t, int64_t>
AigManager::get_children(int64_t id) const
{
  const AigNodeData* d = node_data(std::abs(id));
  return {d->d_left, d->d_right};
}

AigNodeData*
AigManager::new_data()
{
  void* mem = new_slot();
  return new (mem) AigNodeData();
}

void
AigManager::garbage_collect(AigNodeData* d)
{
  assert(d->d_refs == 0);

  if (d_gc_mode)
  {
    assert(false);
    return;
  }

  d_gc_mode = true;

  AigNodeData *cur, *data;
  std::vector<AigNodeData*> visit{d};

  do
  {
    cur = visit.back();
    visit.pop_back();
    assert(cur->d_refs == 0);

    // Decrement reference counts for children of AND nodes
    if (cur->d_left != 0)
    {
      assert(cur->d_right != 0);

      // Erase node data from unique table before we modify children.
      d_unique_table.erase(cur);

      for (int32_t child : {cur->d_left, cur->d_right})
      {
        data = node_data(std::abs(child));
        data->dec_parents();
        if (data->release())
        {
          visit.push_back(data);
        }
      }
      cur->d_left  = 0;
      cur->d_right = 0;
      --d_statistics.num_ands;
    }
    else
    {
      --d_statistics.num_consts;
    }

    // Mark the slot as dead, see node_data(). The node data is not destroyed
    // and its slot is not reused: it owns no memory, its children were
    // released above, and ids have to stay unique since, e.g., AigCnfEncoder
    // maps them to CNF variables.
    assert(!cur->d_dead);
    cur->d_dead = 1;
  } while (!visit.empty());

  d_gc_mode = false;
}

}  // namespace bzla::bitblast
