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

namespace bzla::bb {

bool
operator==(const AigNode& a, const AigNode& b)
{
  return a.get_id() == b.get_id();
}

bool
operator<(const AigNode& a, const AigNode& b)
{
  return a.get_id() < b.get_id();
}

/**
 * AigNodeData storing all node data.
 */
class AigNodeData
{
  friend AigManager;
  friend class AigNode;
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
      d_mgr->garbage_collect(this);
    }
  }

 private:
  AigNodeData(AigManager* mgr) : d_mgr(mgr) {}
  AigNodeData(AigManager* mgr, const AigNode& left, const AigNode& right)
      : d_mgr(mgr), d_left(left), d_right(right)
  {
  }

  /** Pointer to AIG Manager to allow automatic deletion. */
  AigManager* d_mgr = nullptr;

  /** AIG node id. */
  int64_t d_id = 0;
  /** Reference count. */
  uint64_t d_refs = 0;
  /** Left child of AND gate. */
  AigNode d_left;
  /** Right child of AND gate. */
  AigNode d_right;

  /** Next pointer for collision chain. */
  AigNodeData* next = nullptr;
};

// AigNodeUniqueTable

AigNodeUniqueTable::AigNodeUniqueTable() { d_buckets.resize(16, nullptr); }

std::pair<bool, AigNodeData*>
AigNodeUniqueTable::insert(AigNodeData* d)
{
  size_t h         = hash(d->d_left, d->d_right);
  AigNodeData* cur = d_buckets[h];
  int64_t left_id  = d->d_left.get_id();
  int64_t right_id = d->d_right.get_id();

  // Check collision chain.
  while (cur)
  {
    if (cur->d_left.get_id() == left_id && cur->d_right.get_id() == right_id)
    {
      return std::make_pair(false, cur);
    }
    cur = cur->next;
  }

  if (d_num_elements == d_buckets.capacity())
  {
    resize();
    h = hash(d->d_left, d->d_right);
  }
  assert(d->next == nullptr);
  d->next      = d_buckets[h];
  d_buckets[h] = d;

  ++d_num_elements;
  return std::make_pair(true, d);
}

void
AigNodeUniqueTable::erase(const AigNodeData* d)
{
  size_t h          = hash(d->d_left, d->d_right);
  AigNodeData* cur  = d_buckets[h];
  AigNodeData* prev = nullptr;
  assert(cur != nullptr);

  // Should not happen
  if (cur == nullptr)
  {
    return;
  }

  // Find data in collision chain.
  int64_t left_id  = d->d_left.get_id();
  int64_t right_id = d->d_right.get_id();
  while (cur)
  {
    if (cur->d_left.get_id() == left_id && cur->d_right.get_id() == right_id)
    {
      break;
    }
    prev = cur;
    cur  = cur->next;
  }
  assert(cur);

  // Update collision chain.
  if (prev == nullptr)
  {
    d_buckets[h] = cur->next;
  }
  else
  {
    prev->next = cur->next;
  }
  --d_num_elements;
}

size_t
AigNodeUniqueTable::hash(const AigNode& left, const AigNode& right)
{
  size_t lhs = static_cast<size_t>(std::abs(left.get_id()));
  size_t rhs = static_cast<size_t>(std::abs(right.get_id()));
  size_t h   = 547789289u * lhs + 786695309u * rhs;
  return h & (d_buckets.capacity() - 1);
}

void
AigNodeUniqueTable::resize()
{
  auto buckets = d_buckets;

  d_buckets.clear();
  d_buckets.resize(d_buckets.capacity() * 2, nullptr);

  // Rehash elements.
  for (auto cur : buckets)
  {
    while (cur)
    {
      size_t h     = hash(cur->d_left, cur->d_right);
      auto next    = cur->next;
      cur->next    = d_buckets[h];
      d_buckets[h] = cur;
      cur          = next;
    }
  }
}

// AigNode

AigNode::AigNode(AigNodeData* data, bool negated)
    : d_data(data), d_negated(negated)
{
  d_data->inc_refs();
}

AigNode::~AigNode()
{
  if (!is_null())
  {
    d_data->dec_refs();
  }
}

AigNode::AigNode(const AigNode& other)
    : d_data(other.d_data), d_negated(other.d_negated)
{
  assert(!other.is_null());
  d_data->inc_refs();
}

AigNode&
AigNode::operator=(const AigNode& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data    = other.d_data;
  d_negated = other.d_negated;
  d_data->inc_refs();
  return *this;
}

AigNode::AigNode(AigNode&& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data       = other.d_data;
  d_negated    = other.d_negated;
  other.d_data = nullptr;
}

AigNode&
AigNode::operator=(AigNode&& other)
{
  if (d_data)
  {
    d_data->dec_refs();
  }
  d_data       = other.d_data;
  d_negated    = other.d_negated;
  other.d_data = nullptr;
  return *this;
}

bool
AigNode::is_true() const
{
  return d_data->d_id == AigNode::s_true_id && !is_negated();
}

bool
AigNode::is_false() const
{
  return d_data->d_id == AigNode::s_true_id && is_negated();
}

bool
AigNode::is_and() const
{
  return !d_data->d_left.is_null();
}

bool
AigNode::is_const() const
{
  return !is_and() && !is_true() && !is_false();
}

bool
AigNode::is_negated() const
{
  return d_negated;
}

const AigNode&
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

int64_t
AigNode::get_id() const
{
  // only  happens if constructed with default constructor
  if (is_null())
  {
    return 0;
  }
  return is_negated() ? -d_data->d_id : d_data->d_id;
}

bool
AigNode::is_null() const
{
  return d_data == nullptr;
}

uint64_t
AigNode::get_refs() const
{
  assert(!is_null());
  return d_data->d_refs;
}

// BitNodeInterface<AigNode>

AigManager::BitInterface()
    : d_true(new_data(), false), d_false(d_true.d_data, true)
{
  assert(d_true.get_id() == AigNode::s_true_id);
  assert(d_false.get_id() == -AigNode::s_true_id);
}

AigManager::~BitInterface() {}

AigNode
AigManager::mk_false()
{
  return d_false;
}

AigNode
AigManager::mk_true()
{
  return d_true;
}

AigNode
AigManager::mk_bit()
{
  ++d_statistics.num_consts;
  return AigNode(new_data());
}

AigNode
AigManager::mk_not(const AigNode& a)
{
  return AigNode(a.d_data, !a.is_negated());
}

AigNode
AigManager::mk_and(const AigNode& a, const AigNode& b)
{
  return rewrite_and(a, b);
}

AigNode
AigManager::mk_or(const AigNode& a, const AigNode& b)
{
  return mk_not(mk_and(mk_not(a), mk_not(b)));
}

AigNode
AigManager::mk_iff(const AigNode& a, const AigNode& b)
{
  return mk_and(mk_not(mk_and(a, mk_not(b))), mk_not(mk_and(mk_not(a), b)));
}

AigNode
AigManager::mk_ite(const AigNode& c, const AigNode& a, const AigNode& b)
{
  return mk_or(mk_and(c, a), mk_and(mk_not(c), b));
}

const AigManager::Statistics&
AigManager::statistics() const
{
  return d_statistics;
}

void
AigManager::init_id(AigNodeData* d)
{
  assert(d_aig_id_counter < INT64_MAX);
  assert(d != nullptr);
  assert(d->d_id == 0);
  d_node_data.emplace_back(d);
  assert(d_node_data.size() == static_cast<size_t>(d_aig_id_counter));
  d->d_id = d_aig_id_counter++;
}

AigNodeData*
AigManager::find_or_create_and(const AigNode& left, const AigNode& right)
{
  assert(std::abs(left.get_id()) < std::abs(right.get_id()));
  AigNodeData* d          = new AigNodeData(this, left, right);
  auto [inserted, lookup] = d_unique_table.insert(d);
  if (!inserted)
  {
    ++d_statistics.num_shared;
    delete d;
    return lookup;
  }

  init_id(d);
  ++d_statistics.num_ands;
  return d;
}

AigNode
AigManager::rewrite_and(const AigNode& l, const AigNode& r)
{
  AigNode left  = l;
  AigNode right = r;
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
    if (left.is_true() || left == right)
    {
      return right;
    }
    if (right.is_true())
    {
      return left;
    }
    // Boundedness rule
    //   shape:  a /\ 0
    //   result: 0
    //
    // Contradiction rule
    //   shape:     a /\ ~b
    //   condition: a = b
    //   result:    0
    if (left.is_false() || right.is_false() || left.get_id() == -right.get_id())
    {
      return d_false;
    }

    /** Optimization level 2 */

    // Contradiction rule (asymmetric)
    //   shape:     (a /\ b) /\ c
    //   condition: (a = ~c) \/ (b = ~c)
    //   result:    0
    if (left.is_and() && !left.is_negated()
        && (left[0].get_id() == -right.get_id()
            || left[1].get_id() == -right.get_id()))
    {
      return d_false;
    }
    if (right.is_and() && !right.is_negated()
        && (right[0].get_id() == -left.get_id()
            || right[1].get_id() == -left.get_id()))
    {
      return d_false;
    }

    // Contradiction rule (symmetric)
    //   shape:     (a /\ b) /\ (c /\ d)
    //   condition: (a = ~c) \/ (a = ~d) \/ (b = ~c) \/ (b = ~d)
    //   result:    0
    if (left.is_and() && !left.is_negated() && right.is_and()
        && !right.is_negated()
        && (left[0].get_id() == -right[0].get_id()
            || left[0].get_id() == -right[1].get_id()
            || left[1].get_id() == -right[0].get_id()
            || left[1].get_id() == -right[1].get_id()))
    {
      return d_false;
    }

    // Subsumption rule (asymmetric)
    //   shape:     ~(a /\ b) /\ c
    //   condition: (a = ~c) \/ (b = ~c)
    //   result:    c
    if (left.is_and() && left.is_negated()
        && (left[0].get_id() == -right.get_id()
            || left[1].get_id() == -right.get_id()))
    {
      return right;
    }
    if (right.is_and() && right.is_negated()
        && (right[0].get_id() == -left.get_id()
            || right[1].get_id() == -left.get_id()))
    {
      return left;
    }

    // Subsumption rule (symmetric)
    //   shape:     ~(a /\ b) /\ (c /\ d)
    //   condition: (a = ~c) \/ (a = ~d) \/ (b = ~c) \/ (b = ~d)
    //   result:    c /\ d
    if (left.is_and() && left.is_negated() && right.is_and()
        && !right.is_negated()
        && (left[0].get_id() == -right[0].get_id()
            || left[0].get_id() == -right[1].get_id()
            || left[1].get_id() == -right[0].get_id()
            || left[1].get_id() == -right[1].get_id()))
    {
      return right;
    }
    if (right.is_and() && right.is_negated() && left.is_and()
        && !left.is_negated()
        && (right[0].get_id() == -left[0].get_id()
            || right[0].get_id() == -left[1].get_id()
            || right[1].get_id() == -left[0].get_id()
            || right[1].get_id() == -left[1].get_id()))
    {
      return left;
    }

    // Idempotence rule
    //   shape:     (a /\ b) /\ c
    //   condition: (a = c) \/ (b = c)
    //   result:    (a /\ b)
    if (left.is_and() && !left.is_negated()
        && (left[0] == right || left[1] == right))
    {
      return left;
    }
    if (right.is_and() && !right.is_negated()
        && (right[0] == left || right[1] == left))
    {
      return right;
    }

    // Resolution rule
    //   shape:     ~(a /\ b) /\ ~(c /\ d)
    //   condition: (a = d) /\ (b = ~c)
    //   result:    ~a
    if (left.is_negated() && left.is_and() && right.is_negated()
        && right.is_and())
    {
      if ((left[0] == right[0] && left[1].get_id() == -right[1].get_id())
          || (left[0] == right[1] && left[1].get_id() == -right[0].get_id()))
      {
        return mk_not(left[0]);
      }
      if ((right[1] == left[1] && right[0].get_id() == -left[0].get_id())
          || (right[1] == left[0] && right[0].get_id() == -left[1].get_id()))
      {
        return mk_not(right[1]);
      }
    }

    /** Optimization level 3 **/

    // Substitution rule (asymmetric)
    //   shape:     ~(a /\ b) /\ c
    //   condition: b = c
    //   result:    ~a /\ c
    if (left.is_and() && left.is_negated())
    {
      // (a = c) -> ~b /\ c
      if (left[0] == right)
      {
        left = mk_not(left[1]);
        continue;
      }
      // (b = c) -> ~a /\ c
      if (left[1] == right)
      {
        left = mk_not(left[0]);
        continue;
      }
    }
    if (right.is_and() && right.is_negated())
    {
      if (right[0] == left)
      {
        right = mk_not(right[1]);
        continue;
      }
      else if (right[1] == left)
      {
        right = mk_not(right[0]);
        continue;
      }
    }

    // Substitution rule (symmetric)
    //   shape:     ~(a /\ b) /\ (c /\ d)
    //   condition: b = c
    //   result:    ~a /\ (c /\ d)
    if (left.is_and() && left.is_negated() && right.is_and()
        && !right.is_negated())
    {
      // (a = c) \/ (a = d) -> ~b /\ (c /\ d)
      if (left[0] == right[0] || left[0] == right[1])
      {
        left = mk_not(left[1]);
        continue;
      }
      // (b = c) \/ (b = d) -> ~a /\ (c /\ d)
      if (left[1] == right[0] || left[1] == right[1])
      {
        left = mk_not(left[0]);
        continue;
      }
    }
    if (right.is_and() && right.is_negated() && left.is_and()
        && !left.is_negated())
    {
      // (a = c) \/ (a = d) -> ~b /\ (c /\ d)
      if (right[0] == left[0] || right[0] == left[1])
      {
        right = mk_not(right[1]);
        continue;
      }
      // (b = c) \/ (b = d) -> ~a /\ (c /\ d)
      if (right[1] == left[0] || right[1] == left[1])
      {
        right = mk_not(right[0]);
        continue;
      }
    }

    /** Optimization level 4 */

    // Idempotence rule
    //   shape: (a /\ b) /\ (c /\ d)
    if (left.is_and() && !left.is_negated() && right.is_and()
        && !right.is_negated())
    {
      // (a = c) \/ (b = c)
      if (left[0] == right[0] || left[1] == right[0])
      {
        right = right[1];
        continue;
      }
      // (a = d) \/ (b = d)
      if (left[0] == right[1] || left[1] == right[1])
      {
        right = right[0];
        continue;
      }
    }

    break;
  } while (true);

  // Normalize ANDs
  if (std::abs(left.get_id()) > std::abs(right.get_id()))
  {
    std::swap(left, right);
  }

  // create AND with left, right
  AigNodeData* d = find_or_create_and(left, right);
  return AigNode(d);
}

AigNodeData*
AigManager::new_data()
{
  AigNodeData* d = new AigNodeData(this);
  init_id(d);
  return d;
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
    if (!cur->d_left.is_null())
    {
      assert(!cur->d_right.is_null());

      // Erase node data from unique table before we modify children.
      d_unique_table.erase(cur);

      data = cur->d_left.d_data;
      --data->d_refs;
      cur->d_left.d_data = nullptr;
      if (data->d_refs == 0)
      {
        visit.push_back(data);
      }

      data = cur->d_right.d_data;
      --data->d_refs;
      cur->d_right.d_data = nullptr;
      if (data->d_refs == 0)
      {
        visit.push_back(data);
      }
      --d_statistics.num_ands;
    }
    else
    {
      --d_statistics.num_consts;
    }

    // Delete node data
    assert(cur->d_id > 0);
    assert(d_node_data[static_cast<size_t>(cur->d_id) - 1]->d_id == cur->d_id);
    d_node_data[static_cast<size_t>(cur->d_id) - 1].reset(nullptr);
  } while (!visit.empty());

  d_gc_mode = false;
}

}  // namespace bzla::bb
