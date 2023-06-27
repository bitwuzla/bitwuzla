/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "type/type_manager.h"

#include <cassert>
#include <utility>

#include "type/type.h"

namespace bzla::type {

/* --- TypeManager public -------------------------------------------------- */

TypeManager::~TypeManager()
{
  // Cleanup remaining types without triggering garbage_collect().
  //
  // Note: Automatic reference counting of Type should actually prevent type
  //       leaks. However, types that are stored in static memory and are
  //       destructed after the TypeManager do not get garbage collected before
  //       destructing the NodeManager (the owner of TypeManager). Hence, we
  //       have to make sure to invalidate all types before destructing the
  //       type manager.
  for (std::unique_ptr<TypeData>& data : d_node_data)
  {
    if (data == nullptr) continue;
    if (data->d_kind == TypeData::Kind::ARRAY
        || data->d_kind == TypeData::Kind::FUN)
    {
      auto& types = std::get<std::vector<Type>>(data->d_data);
      for (auto& type : types)
      {
        type.d_data = nullptr;
      }
    }
  }
}

Type
TypeManager::mk_bool_type()
{
  return Type(find_or_create_type(TypeData::Kind::BOOL));
}

Type
TypeManager::mk_bv_type(uint64_t size)
{
  return Type(find_or_create_bv_type(size));
}

Type
TypeManager::mk_fp_type(uint64_t exp_size, uint64_t sig_size)
{
  return Type(find_or_create_fp_type(exp_size, sig_size));
}

Type
TypeManager::mk_rm_type()
{
  return Type(find_or_create_type(TypeData::Kind::RM));
}

Type
TypeManager::mk_array_type(const Type& index, const Type& elem)
{
  return Type(find_or_create_type(TypeData::Kind::ARRAY, {index, elem}));
}

Type
TypeManager::mk_fun_type(const std::vector<Type>& types)
{
  return Type(find_or_create_type(TypeData::Kind::FUN, types));
}

Type
TypeManager::mk_uninterpreted_type(const std::optional<std::string>& symbol)
{
  TypeData* data = new TypeData(this, symbol);
  init_id(data);
  return data;
}

/* --- TypeManager private ------------------------------------------------- */

void
TypeManager::init_id(TypeData* data)
{
  assert(d_type_id_counter < UINT64_MAX);
  assert(data != nullptr);
  assert(data->d_id == 0);
  d_node_data.emplace_back(data);
  assert(d_node_data.size() == static_cast<size_t>(d_type_id_counter));
  data->d_id = d_type_id_counter++;
}

TypeData*
TypeManager::find_or_create(TypeData* data)
{
  auto [it, inserted] = d_unique_types.insert(data);

  if (!inserted)  // Type already exists
  {
    delete data;
    return *it;
  }

  // Type is new, initialize
  init_id(data);
  return data;
}

TypeData*
TypeManager::find_or_create_type(TypeData::Kind kind,
                                 const std::vector<Type>& types)
{
  TypeData* data = new TypeData(this, kind, types);
  return find_or_create(data);
}

TypeData*
TypeManager::find_or_create_bv_type(uint64_t size)
{
  TypeData* data = new TypeData(this, size);
  return find_or_create(data);
}

TypeData*
TypeManager::find_or_create_fp_type(uint64_t exp_size, uint64_t sig_size)
{
  TypeData* data = new TypeData(this, exp_size, sig_size);
  return find_or_create(data);
}

void
TypeManager::garbage_collect(TypeData* data)
{
  assert(data->d_refs == 0);
  assert(!d_in_gc_mode);

  d_in_gc_mode = true;

  std::vector<TypeData*> visit{data};

  TypeData* cur;
  do
  {
    cur = visit.back();
    visit.pop_back();

    // Erase type data before we modify children.
    d_unique_types.erase(cur);

    auto kind = cur->get_kind();
    if (kind == TypeData::Kind::ARRAY || kind == TypeData::Kind::FUN)
    {
      auto& types = std::get<std::vector<Type>>(cur->d_data);
      for (size_t i = 0, size = types.size(); i < size; ++i)
      {
        Type& t = types[i];
        auto d  = t.d_data;

        // Manually decrement reference count to not trigger decrement of
        // TypeData reference. This will avoid recursive call to
        // garbage_collect().
        --d->d_refs;
        t.d_data = nullptr;
        if (d->d_refs == 0)
        {
          visit.push_back(d);
        }
      }
    }

    assert(d_node_data[cur->d_id - 1]->d_id == cur->d_id);
    d_node_data[cur->d_id - 1].reset(nullptr);
  } while (!visit.empty());

  d_in_gc_mode = false;
}

}  // namespace bzla::type
