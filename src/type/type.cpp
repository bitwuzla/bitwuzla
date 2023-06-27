/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "type/type.h"

#include <cassert>

#include "printer/printer.h"
#include "type/type_data.h"

namespace bzla {

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
  if (other.d_data)
  {
    other.d_data->inc_ref();
  }
  if (d_data)
  {
    d_data->dec_ref();
  }
  d_data = other.d_data;
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
  return d_data && d_data->get_kind() == type::TypeData::Kind::BOOL;
}

bool
Type::is_bv() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::BV;
}

bool
Type::is_fp() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::FP;
}

bool
Type::is_rm() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::RM;
}

bool
Type::is_array() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::ARRAY;
}

bool
Type::is_fun() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::FUN;
}

bool
Type::is_uninterpreted() const
{
  return d_data && d_data->get_kind() == type::TypeData::Kind::UNINTERPRETED;
}

uint64_t
Type::bv_size() const
{
  assert(is_bv());
  return d_data->get_bv_size();
}

uint64_t
Type::fp_exp_size() const
{
  assert(is_fp());
  return d_data->get_fp_exp_size();
}

uint64_t
Type::fp_sig_size() const
{
  assert(is_fp());
  return d_data->get_fp_sig_size();
}

uint64_t
Type::fp_ieee_bv_size() const
{
  return d_data->get_fp_exp_size() + d_data->get_fp_sig_size();
}

const Type&
Type::array_index() const
{
  assert(is_array());
  return d_data->get_types()[0];
}

const Type&
Type::array_element() const
{
  assert(is_array());
  return d_data->get_types()[1];
}

size_t
Type::fun_arity() const
{
  return fun_types().size() - 1;
}

const std::vector<Type>&
Type::fun_types() const
{
  assert(is_fun());
  return d_data->get_types();
}

const std::optional<std::string>&
Type::uninterpreted_symbol() const
{
  return d_data->get_symbol();
}

uint64_t
Type::id() const
{
  assert(d_data != nullptr);
  return d_data->get_id();
}

bool
Type::is_null() const
{
  return d_data == nullptr;
}

std::string
Type::str() const
{
  std::stringstream ss;
  ss << *this;
  return ss.str();
}

/* --- Type private -------------------------------------------------------- */

Type::Type(type::TypeData* data) : d_data(data)
{
  assert(data != nullptr);
  d_data->inc_ref();
}

/* --- Other --------------------------------------------------------------- */

bool
operator==(const Type& a, const Type& b)
{
  return a.d_data == b.d_data;
}

bool
operator!=(const Type& a, const Type& b)
{
  return a.d_data != b.d_data;
}

std::ostream&
operator<<(std::ostream& out, const Type& type)
{
  Printer::print(out, type);
  return out;
}

}  // namespace bzla

namespace std {

size_t
hash<bzla::Type>::operator()(const bzla::Type& type) const
{
  return type.id();
}

size_t
hash<bzla::Type*>::operator()(const bzla::Type* type) const
{
  return type->id();
}

}  // namespace std
