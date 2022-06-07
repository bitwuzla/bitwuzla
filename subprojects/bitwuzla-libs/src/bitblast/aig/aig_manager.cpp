#include "bitblast/aig/aig_manager.h"

namespace bzla::bb {

/**
 * AigNodeData storing all node data.
 */
class AigNodeData
{
  friend AigManager;
  friend class AigNode;

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
};

size_t
AigManager::AigNodeDataHash::operator()(const AigNodeData* d) const
{
  size_t lhs = static_cast<size_t>(std::abs(d->d_left.get_id()));
  size_t rhs = static_cast<size_t>(std::abs(d->d_right.get_id()));
  return 547789289u * lhs + 786695309u * rhs;
}

bool
AigManager::AigNodeDataKeyEqual::operator()(const AigNodeData* d0,
                                            const AigNodeData* d1) const
{
  return d0->d_left == d1->d_left && d0->d_right == d1->d_right;
}

// AigNode

AigNode::AigNode(AigNodeData* data, bool negated)
    : d_data(data), d_negated(negated)
{
  d_data->inc_refs();
};

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

bool
AigNode::operator==(const AigNode& other) const
{
  return get_id() == other.get_id();
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
  bool swap = std::abs(a.get_id()) > std::abs(b.get_id());

  // Normalize ANDs
  const AigNode& left  = swap ? b : a;
  const AigNode& right = swap ? a : b;

  AigNode rw = rewrite_and(left, right);

  if (!rw.is_null())
  {
    return rw;
  }

  AigNodeData* d = find_or_create_and(left, right);
  assert(!d->d_left.is_null());
  assert(!d->d_right.is_null());
  return AigNode(d);
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
  AigNodeData* d = new AigNodeData(this, left, right);

  auto [it, inserted] = d_unique_ands.insert(d);
  if (inserted)
  {
    init_id(d);
    ++d_statistics.num_ands;
    return d;
  }
  delete d;
  return *it;
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
    assert(!right.is_true());

    /** Optimization level 2 */

    // Contradiction rule (assymetric)
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

    // Subsumption rule (assymetric)
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
    //   condition: (a = d) \/ (b = ~c)
    //   result:    ~a
    if (left.is_negated() && left.is_and() && right.is_negated()
        && right.is_and()
        && (left[0] == right[1] || left[1].get_id() == -right[0].get_id()))
    {
      return mk_not(left[0]);
    }
    if (right.is_negated() && right.is_and() && left.is_negated()
        && left.is_and()
        && (right[0] == left[1] || right[1].get_id() == -left[0].get_id()))
    {
      return mk_not(right[0]);
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

  // create AND with left, right

  return AigNode();
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

    // Erase node data before we modify children.
    d_unique_ands.erase(cur);

    // Decrement reference counts for children of AND nodes
    if (!cur->d_left.is_null())
    {
      assert(!cur->d_right.is_null());

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
    }

    // Delete node data
    assert(d_node_data[cur->d_id - 1]->d_id == cur->d_id);
    d_node_data[cur->d_id - 1].reset(nullptr);
  } while (!visit.empty());

  d_gc_mode = false;
}

}  // namespace bzla::bb
