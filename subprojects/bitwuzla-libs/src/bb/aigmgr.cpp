#include "bb/aigmgr.h"

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
      d_mgr->delete_data(this);
    }
  }

 private:
  AigNodeData(AigManager* mgr, int64_t id) : d_mgr(mgr), d_id(id) {}
  AigNodeData(AigManager* mgr,
              int64_t id,
              const AigNode& left,
              const AigNode& right)
      : d_mgr(mgr), d_id(id), d_left(left), d_right(right)
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
  return static_cast<size_t>(d->d_left.get_id())
         + static_cast<size_t>(d->d_right.get_id());
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
  return get_id() == other.get_id() && is_negated() == other.is_negated();
}

const AigNode& AigNode::operator[](int index) const
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

  // TODO: two-level AIG rewriting

  AigNodeData* d = find_and(left, right);
  if (!d)
  {
    d = new_data(left, right);
    d_unique_ands.emplace(d);
    ++d_statistics.num_ands;
  }
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

int64_t
AigManager::next_id()
{
  assert(d_aig_id_counter < INT64_MAX);
  return d_aig_id_counter++;
}

AigNodeData*
AigManager::find_and(const AigNode& left, const AigNode& right)
{
  AigNodeData aig(this, 0, left, right);
  auto it = d_unique_ands.find(&aig);
  if (it != d_unique_ands.end())
  {
    return *it;
  }
  return nullptr;
}

AigNodeData*
AigManager::new_data()
{
  auto id        = next_id();
  AigNodeData* d = new AigNodeData(this, id);
  d_node_data.emplace(id, d);
  return d;
}

AigNodeData*
AigManager::new_data(const AigNode& left, const AigNode& right)
{
  auto id        = next_id();
  AigNodeData* d = new AigNodeData(this, id, left, right);
  d_node_data.emplace(id, d);
  return d;
}

void
AigManager::delete_data(AigNodeData* d)
{
  d_unique_ands.erase(d);
  d_node_data.erase(d->d_id);
}

}  // namespace bzla::bb
