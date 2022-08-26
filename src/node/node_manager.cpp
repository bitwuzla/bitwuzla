#include "node/node_manager.h"

namespace bzla::node {

/* --- NodeManager public -------------------------------------------------- */

Node
NodeManager::mk_const(const type::Type& type, const std::string& symbol)
{
  // TODO: handle symbol
  NodeData* data = new NodeData(this, Kind::CONSTANT);
  data->d_type   = type;
  init_id(data);
  return Node(data);
}

Node
NodeManager::mk_var(const type::Type& type, const std::string& symbol)
{
  // TODO: handle symbol
  NodeData* data = new NodeData(this, Kind::VARIABLE);
  data->d_type   = type;
  init_id(data);
  return Node(data);
}

Node
NodeManager::mk_node(Kind kind,
                     const std::vector<Node>& children,
                     const std::vector<uint64_t>& indices)
{
  return Node(find_or_create_node(kind, children, indices));
}

type::Type
NodeManager::mk_bool_type()
{
  return d_tm.mk_bool_type();
}

type::Type
NodeManager::mk_bv_type(uint64_t size)
{
  return d_tm.mk_bv_type(size);
}

type::Type
NodeManager::mk_fp_type(uint64_t exp_size, uint64_t sig_size)
{
  return d_tm.mk_fp_type(exp_size, sig_size);
}

type::Type
NodeManager::mk_rm_type()
{
  return d_tm.mk_rm_type();
}

type::Type
NodeManager::mk_array_type(const type::Type& index, const type::Type& elem)
{
  return d_tm.mk_array_type(index, elem);
}

type::Type
NodeManager::mk_fun_type(const std::vector<type::Type>& types)
{
  return d_tm.mk_fun_type(types);
}

/* --- NodeManager private ------------------------------------------------- */

void
NodeManager::init_id(NodeData* data)
{
  assert(d_node_id_counter < UINT64_MAX);
  assert(data != nullptr);
  assert(data->d_id == 0);
  d_node_data.emplace_back(data);
  assert(d_node_data.size() == static_cast<size_t>(d_node_id_counter));
  data->d_id = d_node_id_counter++;
}

NodeData*
NodeManager::new_data(Kind kind,
                      const std::vector<Node>& children,
                      const std::vector<uint64_t>& indices)
{
  assert(children.size() > 0);

  NodeData* data;
  if (indices.size() > 0)
  {
    data = new NodeDataIndexed(this, kind, children, indices);
  }
  else if (s_node_kind_info[kind].is_nary())
  {
    data = new NodeDataNary(this, kind, children);
  }
  else
  {
    data = new NodeDataChildren(this, kind, children);
  }
  return data;
}

NodeData*
NodeManager::find_or_create_node(Kind kind,
                                 const std::vector<Node>& children,
                                 const std::vector<uint64_t>& indices)
{
  NodeData* data      = new_data(kind, children, indices);
  auto [it, inserted] = d_unique_nodes.insert(data);

  if (!inserted)  // Node already exists
  {
    delete data;
    return *it;
  }

  // Node is new, initialize
  init_id(data);
  // TODO: compute type of node
  return data;
}

void
NodeManager::garbage_collect(NodeData* data)
{
  assert(data->d_refs == 0);
  assert(!d_in_gc_mode);

  d_in_gc_mode = true;

  std::vector<NodeData*> visit{data};

  NodeData* cur;
  do
  {
    cur = visit.back();
    visit.pop_back();

    // Erase node data before we modify children.
    d_unique_nodes.erase(cur);

    for (size_t i = 0, size = cur->get_num_children(); i < size; ++i)
    {
      Node& child = cur->get_child(i);
      auto d      = child.d_data;

      // Manually decrement reference count to not trigger decrement of
      // NodeData reference. This will avoid recursive call to
      // garbage_collect().
      --d->d_refs;
      child.d_data = nullptr;
      if (d->d_refs == 0)
      {
        visit.push_back(d);
      }
    }

    assert(d_node_data[cur->d_id - 1]->d_id == cur->d_id);
    d_node_data[cur->d_id - 1].reset(nullptr);
  } while (!visit.empty());

  d_in_gc_mode = false;
}

}  // namespace bzla::node
