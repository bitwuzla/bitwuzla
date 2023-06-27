/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "type/type_data.h"

#include <cassert>
#include <iostream>

#include "type/type.h"
#include "type/type_manager.h"
namespace bzla::type {

size_t
TypeDataHash::operator()(const TypeData* d) const
{
  size_t hash = static_cast<size_t>(d->get_kind());
  auto kind   = d->get_kind();
  if (kind == TypeData::Kind::BV)
  {
    hash += d->get_bv_size() * s_primes[0];
  }
  else if (kind == TypeData::Kind::FP)
  {
    hash += d->get_fp_exp_size() * s_primes[0];
    hash += d->get_fp_sig_size() * s_primes[1];
  }
  else if (kind == TypeData::Kind::ARRAY || kind == TypeData::Kind::FUN)
  {
    const auto& types = d->get_types();
    for (size_t i = 0, size = types.size(); i < size; ++i)
    {
      hash += s_primes[i % s_primes.size()] * types[i].id();
    }
  }
  return hash;
}

bool
TypeDataKeyEqual::operator()(const TypeData* d0, const TypeData* d1) const
{
  if (d0->get_kind() != d1->get_kind())
  {
    return false;
  }

  auto kind = d0->get_kind();
  if (kind == TypeData::Kind::BV)
  {
    return d0->get_bv_size() == d1->get_bv_size();
  }
  else if (kind == TypeData::Kind::FP)
  {
    return d0->get_fp_exp_size() == d1->get_fp_exp_size()
           && d0->get_fp_sig_size() == d1->get_fp_sig_size();
  }
  else if (kind == TypeData::Kind::ARRAY || kind == TypeData::Kind::FUN)
  {
    const auto& types0 = d0->get_types();
    const auto& types1 = d1->get_types();
    if (types0.size() != types1.size())
    {
      return false;
    }
    for (size_t i = 0, size = types0.size(); i < size; ++i)
    {
      if (types0[i].id() != types1[i].id())
      {
        return false;
      }
    }
  }
  else if (kind == TypeData::Kind::UNINTERPRETED)
  {
    return false;
  }

  return true;
}

/* --- TypeData public ------------------------------------------------------*/

TypeData::TypeData(TypeManager* mgr, Kind kind, const std::vector<Type>& types)
    : d_mgr(mgr), d_kind(kind), d_data(types)
{
}

TypeData::TypeData(TypeManager* mgr, uint64_t size)
    : d_mgr(mgr), d_kind(Kind::BV), d_data(size)
{
  assert(size);
}

TypeData::TypeData(TypeManager* mgr, uint64_t exp_size, uint64_t sig_size)
    : d_mgr(mgr), d_kind(Kind::FP), d_data(std::make_pair(exp_size, sig_size))

{
  assert(exp_size);
  assert(sig_size);
}

TypeData::TypeData(TypeManager* mgr, const std::optional<std::string>& symbol)
    : d_mgr(mgr), d_kind(Kind::UNINTERPRETED), d_data(symbol)
{
}

TypeData::~TypeData() {}

uint64_t
TypeData::get_id() const
{
  return d_id;
}

TypeData::Kind
TypeData::get_kind() const
{
  return d_kind;
}

const std::vector<Type>&
TypeData::get_types() const
{
  assert(d_kind == Kind::ARRAY || d_kind == Kind::FUN);
  return std::get<std::vector<Type>>(d_data);
}

const std::optional<std::string>&
TypeData::get_symbol() const
{
  assert(d_kind == Kind::UNINTERPRETED);
  return std::get<std::optional<std::string>>(d_data);
}

uint64_t
TypeData::get_bv_size() const
{
  assert(d_kind == Kind::BV);
  return std::get<uint64_t>(d_data);
}

uint64_t
TypeData::get_fp_exp_size() const
{
  assert(d_kind == Kind::FP);
  return std::get<std::pair<uint64_t, uint64_t>>(d_data).first;
}

uint64_t
TypeData::get_fp_sig_size() const
{
  assert(d_kind == Kind::FP);
  return std::get<std::pair<uint64_t, uint64_t>>(d_data).second;
}

void
TypeData::inc_ref()
{
  ++d_refs;
}

void
TypeData::dec_ref()
{
  assert(d_refs > 0);
  --d_refs;
  if (d_refs == 0)
  {
    d_mgr->garbage_collect(this);
  }
}

}  // namespace bzla::type
