#include "node/node_unique_table.h"

#include "solver/fp/floating_point.h"

namespace bzla::node {

/* --- NodeUniqueTable public ----------------------------------------------- */

NodeUniqueTable::NodeUniqueTable() { d_buckets.resize(16, nullptr); }

NodeUniqueTable::~NodeUniqueTable()
{
  // Cleanup remaining node data.
  //
  // Note: Automatic reference counting of Node should actually prevent node
  //       data leaks. However, nodes that are stored in static memory do not
  //       get garbage collected. Hence, we have to make sure to invalidate all
  //       node data before destructing the unique table.
  for (size_t i = 0, size = d_buckets.size(); i < size; ++i)
  {
    NodeData* cur = d_buckets[i];
    while (cur != nullptr)
    {
      NodeData* next = cur->d_next;
      if (cur->has_children())
      {
        auto& payload = cur->payload_children();
        for (size_t j = 0; j < payload.d_num_children; ++j)
        {
          payload.d_children[j].d_data = nullptr;
        }
      }
      NodeData::dealloc(cur);
      cur = next;
    }
  }
}

std::pair<bool, NodeData*>
NodeUniqueTable::find_or_insert(Kind kind,
                                const Type& type,
                                const std::vector<Node>& children,
                                const std::vector<uint64_t>& indices)
{
  assert(kind != Kind::VALUE);

  size_t hd     = hash(kind, children, indices);
  size_t h      = bucket_hash(hd);
  NodeData* cur = d_buckets[h];

  // Check collision chain.
  while (cur)
  {
    // Found existing node
    if (equals(*cur, kind, type, children, indices))
    {
      return std::make_pair(false, cur);
    }
    cur = cur->d_next;
  }

  // Create new node and insert
  NodeData* d = NodeData::alloc(kind, children, indices);
  if (needs_resize())
  {
    resize();
    h = bucket_hash(hd);
  }
  assert(d->d_next == nullptr);
  d->d_next    = d_buckets[h];
  d_buckets[h] = d;

  ++d_num_elements;
  return std::make_pair(true, d);
}

void
NodeUniqueTable::erase(const NodeData* d)
{
  size_t h       = bucket_hash(hash(d));
  NodeData* cur  = d_buckets[h];
  NodeData* prev = nullptr;
  assert(cur != nullptr);

  // Find data in collision chain.
  while (cur)
  {
    // Note: No need to use equals() here, we can safely compare the pointers.
    if (cur == d)
    {
      break;
    }
    prev = cur;
    cur  = cur->d_next;
  }
  assert(cur);

  // Update collision chain.
  if (prev == nullptr)
  {
    d_buckets[h] = cur->d_next;
  }
  else
  {
    prev->d_next = cur->d_next;
  }
  --d_num_elements;
}

/* --- NodeUniqueTable private ---------------------------------------------- */

void
NodeUniqueTable::resize()
{
  size_t new_size = d_buckets.capacity() * 2;
  std::vector<NodeData*> buckets(new_size, nullptr);

  // Rehash elements.
  size_t mask = new_size - 1;
  for (auto cur : d_buckets)
  {
    while (cur)
    {
      size_t h     = bucket_hash(hash(cur), mask);
      auto next    = cur->d_next;
      cur->d_next  = buckets[h];
      buckets[h]   = cur;
      cur          = next;
    }
  }

  d_buckets = std::move(buckets);
}

size_t
NodeUniqueTable::hash(const NodeData* d) const
{
  size_t hash = static_cast<size_t>(d->get_kind());

  if (d->get_kind() == Kind::VALUE)
  {
    const Type& t = d->get_type();
    if (t.is_bool())
    {
      const auto& payload = d->payload_value<bool>();
      hash += std::hash<bool>{}(payload.d_value);
    }
    else if (t.is_bv())
    {
      const auto& payload = d->payload_value<BitVector>();
      hash += std::hash<BitVector>{}(payload.d_value);
    }
    else if (t.is_rm())
    {
      const auto& payload = d->payload_value<RoundingMode>();
      hash += std::hash<RoundingMode>{}(payload.d_value);
    }
    else
    {
      assert(t.is_fp());
      const auto& payload = d->payload_value<FloatingPoint>();
      hash += std::hash<FloatingPoint>{}(payload.d_value);
    }
  }
  else
  {
    assert(d->has_children());
    const auto& payload = d->payload_children();
    hash = hash_children(hash, payload.d_num_children, payload.d_children);

    if (d->is_indexed())
    {
      const auto& payload = d->payload_indexed();
      hash = hash_indices(hash, payload.d_num_indices, payload.d_indices);
    }
  }

  return hash;
}

size_t
NodeUniqueTable::hash(Kind kind,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices) const
{
  assert(!children.empty());

  size_t hash = static_cast<size_t>(kind);

  hash = hash_children(hash, children.size(), children.data());
  if (!indices.empty())
  {
    hash = hash_indices(hash, indices.size(), indices.data());
  }

  return hash;
}

bool
NodeUniqueTable::equals(const NodeData& data,
                        Kind kind,
                        const Type& type,
                        const std::vector<Node>& children,
                        const std::vector<uint64_t>& indices) const
{
  assert(kind != Kind::VALUE);

  if (data.d_kind != kind)
  {
    return false;
  }

  if (!children.empty())
  {
    assert(data.has_children());
    const auto& payload = data.payload_children();

    size_t num_children = payload.d_num_children;
    if (num_children != children.size())
    {
      return false;
    }

    for (size_t i = 0; i < num_children; ++i)
    {
      if (payload.d_children[i] != children[i])
      {
        return false;
      }
    }

    // Constant arrays are a special case since they require the type info.
    if (kind == Kind::CONST_ARRAY)
    {
      assert(!data.get_type().is_null());
      assert(!type.is_null());
      return data.get_type() == type;
    }
  }

  if (!indices.empty())
  {
    assert(data.is_indexed());
    const auto& payload = data.payload_indexed();

    size_t num_indices = payload.d_num_indices;
    if (num_indices != indices.size())
    {
      return false;
    }

    for (size_t i = 0; i < num_indices; ++i)
    {
      if (payload.d_indices[i] != indices[i])
      {
        return false;
      }
    }
  }

  return true;
}

}  // namespace bzla::node
