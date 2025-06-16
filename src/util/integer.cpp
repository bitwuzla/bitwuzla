/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/integer.h"

#include <cassert>
#include <sstream>

#include "util/gmp_utils.h"

namespace bzla::util {

Integer::Integer() { mpz_init_set_ui(d_val_gmp, 0); }

Integer::Integer(int val) { mpz_init_set_si(d_val_gmp, val); }

Integer::Integer(unsigned int val) { mpz_init_set_ui(d_val_gmp, val); }

Integer::Integer(int64_t val) { mpz_init_set_sll(d_val_gmp, val); }

Integer::Integer(uint64_t val) { mpz_init_set_ull(d_val_gmp, val); }

Integer::Integer(const char* val)
{
  mpz_init_set_str(d_val_gmp, val, 10);
}

Integer::Integer(const std::string& val)
{
  mpz_init_set_str(d_val_gmp, val.c_str(), 10);
}

Integer Integer::from_mpz_t(const mpz_t val)
{
  Integer res;
  mpz_set(res.d_val_gmp, val);
  return res;
}

Integer::Integer(const Integer& other)
{
  mpz_init_set(d_val_gmp, other.d_val_gmp);
}

Integer::Integer(Integer&& other) { mpz_init_set(d_val_gmp, other.d_val_gmp); }

Integer::~Integer()
{
  mpz_clear(d_val_gmp);
}

Integer&
Integer::operator=(const Integer& other)
{
  if (&other != this)
  {
    mpz_set(d_val_gmp, other.d_val_gmp);
  }
  return *this;
}

Integer&
Integer::operator=(Integer&& other)
{
  if (&other != this)
  {
    mpz_set(d_val_gmp, other.d_val_gmp);
  }
  return *this;
}

bool
Integer::operator==(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) == 0;
}

bool
Integer::operator!=(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) != 0;
}

bool
Integer::operator<(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) < 0;
}

bool
Integer::operator<=(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) <= 0;
}

bool
Integer::operator>(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) > 0;
}

bool
Integer::operator>=(const Integer& other) const
{
  return mpz_cmp(d_val_gmp, other.d_val_gmp) >= 0;
}

Integer
Integer::operator+(const Integer& other) const
{
  Integer res = from_mpz_t(d_val_gmp);
  res += other;
  return res;
}

Integer
Integer::operator-() const
{
  Integer res = from_mpz_t(d_val_gmp);
  mpz_neg(res.d_val_gmp, res.d_val_gmp);
  return res;
}

Integer
Integer::operator-(const Integer& other) const
{
  Integer res = from_mpz_t(d_val_gmp);
  res -= other;
  return res;
}

Integer
Integer::operator*(const Integer& other) const
{
  Integer res = from_mpz_t(d_val_gmp);
  res *= other;
  return res;
}

Integer
Integer::operator/(const Integer& other) const
{
  Integer res = from_mpz_t(d_val_gmp);
  res /= other;
  return res;
}

Integer
Integer::operator++(int)
{
  Integer res = from_mpz_t(d_val_gmp);
  operator++();
  return res;
}

Integer
Integer::operator--(int)
{
  Integer res = from_mpz_t(d_val_gmp);
  operator--();
  return res;
}

Integer&
Integer::operator+=(const Integer& other)
{
  mpz_add(d_val_gmp, d_val_gmp, other.d_val_gmp);
  return *this;
}

Integer&
Integer::operator-=(const Integer& other)
{
  mpz_sub(d_val_gmp, d_val_gmp, other.d_val_gmp);
  return *this;
}

Integer&
Integer::operator*=(const Integer& other)
{
  mpz_mul(d_val_gmp, d_val_gmp, other.d_val_gmp);
  return *this;
}

Integer&
Integer::operator/=(const Integer& other)
{
  mpz_fdiv_q(d_val_gmp, d_val_gmp, other.d_val_gmp);
  return *this;
}

Integer&
Integer::operator++()
{
  mpz_add_ui(d_val_gmp, d_val_gmp, 1);
  return *this;
}

Integer&
Integer::operator--()
{
  mpz_sub_ui(d_val_gmp, d_val_gmp, 1);
  return *this;
}

Integer&
Integer::ipow(uint32_t exp)
{
  mpz_pow_ui(d_val_gmp, d_val_gmp, exp);
  return *this;
}

bool
Integer::is_odd() const
{
  return mpz_odd_p(d_val_gmp) != 0;
}

size_t
Integer::hash() const
{
  return mpz_hash(d_val_gmp);
}

std::string
Integer::str() const
{
  std::stringstream ss;
  char* tmp = mpz_get_str(0, 10, d_val_gmp);
  ss << tmp;
  free(tmp);
  return ss.str();
}

uint64_t
Integer::to_uint64() const
{
  assert(64 >= mpz_sizeinbase(d_val_gmp, 2));
  assert(mpz_sgn(d_val_gmp) >= 0);
  return mpz_get_ull(d_val_gmp);
}

int64_t
Integer::to_int64() const
{
  assert(64 >= mpz_sizeinbase(d_val_gmp, 2));
  uint64_t value = mpz_get_ull(d_val_gmp);
  if (mpz_sgn(d_val_gmp) < 0)
  {
    assert(value <= static_cast<uint64_t>(
               std::abs(std::numeric_limits<int64_t>::min())));
    return -value;
  }
  assert(value <= std::numeric_limits<int64_t>::max());
  return value;
}

std::ostream&
operator<<(std::ostream& os, const Integer& i)
{
  os << i.str();
  return os;
}

}  // namespace bzla::util

namespace std {

size_t
hash<bzla::util::Integer>::operator()(const bzla::util::Integer& i) const
{
  return i.hash();
}

}  // namespace std
