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

namespace bzla::bitblast {

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

// BitNodeInterface<AigNode>

AigManager::AigManager()
    : d_true(new_data(), false), d_false(d_true.d_data, true)
{
  assert(d_true.get_id() == AigNode::s_true_id);
  assert(d_false.get_id() == -AigNode::s_true_id);
}

AigManager::~AigManager() {}

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
  if (!d->d_left.is_null())
  {
    ++d->d_left.d_data->d_parents;
    ++d->d_right.d_data->d_parents;
  }
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
  AigNodeData* d = find_or_create_and(get_node(left), get_node(right));
  return AigNode(d);
}

AigNode
AigManager::get_node(int64_t id)
{
  assert(static_cast<size_t>(std::abs(id)) <= d_node_data.size());
  return AigNode(d_node_data[std::abs(id) - 1].get(), id < 0);
}

std::pair<int64_t, int64_t>
AigManager::get_children(int64_t id) const
{
  assert(static_cast<size_t>(std::abs(id)) <= d_node_data.size());
  const auto& d = d_node_data[std::abs(id) - 1];
  return {d->d_left.get_id(), d->d_right.get_id()};
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
      --data->d_parents;
      cur->d_left.d_data = nullptr;
      if (data->d_refs == 0)
      {
        visit.push_back(data);
      }

      data = cur->d_right.d_data;
      --data->d_refs;
      --data->d_parents;
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

}  // namespace bzla::bitblast
