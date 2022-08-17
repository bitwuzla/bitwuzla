#include "type/type.h"

#include <cassert>

#include "type/type_data.h"

namespace bzla::type {

/* --- Type public --------------------------------------------------------- */

Type::~Type()
{
  if (d_data != nullptr)
  {
    d_data->dec_ref();
  }
}

Type::Type(const Type& other) : d_data(other.d_data)
{
  if (d_data)
  {
    d_data->inc_ref();
  }
}

Type&
Type::operator=(const Type& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  if (other.d_data)
  {
    d_data = other.d_data;
    d_data->inc_ref();
  }
  return *this;
}

Type::Type(Type&& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  d_data       = other.d_data;
  other.d_data = nullptr;
}

Type&
Type::operator=(Type&& other)
{
  if (d_data)
  {
    d_data->dec_ref();
  }
  d_data       = other.d_data;
  other.d_data = nullptr;
  return *this;
}

bool
Type::is_bool() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::BOOL;
}

bool
Type::is_bv() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::BV;
}

bool
Type::is_fp() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::FP;
}
bool
Type::is_rm() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::RM;
}
bool
Type::is_array() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::ARRAY;
}
bool
Type::is_fun() const
{
  assert(d_data != nullptr);
  return d_data->get_kind() == TypeData::Kind::FUN;
}

uint64_t
Type::get_bv_size() const
{
  assert(is_bv());
  return d_data->get_bv_size();
}

uint64_t
Type::get_fp_exp_size() const
{
  assert(is_fp());
  return d_data->get_fp_exp_size();
}

uint64_t
Type::get_fp_sig_size() const
{
  assert(is_fp());
  return d_data->get_fp_sig_size();
}

const Type&
Type::get_array_index() const
{
  assert(is_array());
  return d_data->get_types()[0];
}

const Type&
Type::get_array_element() const
{
  assert(is_array());
  return d_data->get_types()[1];
}

const std::vector<Type>&
Type::get_fun_types() const
{
  assert(is_fun());
  return d_data->get_types();
}

uint64_t
Type::get_id() const
{
  assert(d_data != nullptr);
  return d_data->get_id();
}

bool
Type::operator==(const Type& other) const
{
  return d_data == other.d_data;
}

bool
Type::operator!=(const Type& other) const
{
  return d_data != other.d_data;
}

/* --- Type private -------------------------------------------------------- */

Type::Type(TypeData* data) : d_data(data)
{
  assert(data != nullptr);
  d_data->inc_ref();
}

}  // namespace bzla::type
