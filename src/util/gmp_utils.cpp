/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/gmp_utils.h"

#include <cassert>
#include <cstddef>
#include <cstdint>

#include "util/hash.h"

namespace bzla::util {

void
mpz_set_ull(mpz_t rop, uint64_t op)
{
  if constexpr (sizeof(uint64_t) != sizeof(unsigned long))
  {
    uint32_t hi = static_cast<uint32_t>(op >> 32);
    uint32_t lo = static_cast<uint32_t>(op);
    mpz_set_ui(rop, hi);
    mpz_mul_2exp(rop, rop, 32);
    mpz_add_ui(rop, rop, lo);
  }
  else
  {
    mpz_set_ui(rop, op);
  }
}

uint64_t
mpz_get_ull(const mpz_t op)
{
  if (mp_bits_per_limb == 64)
  {
    mp_limb_t limb = mpz_getlimbn(op, 0);
    return limb;
  }
  assert(mp_bits_per_limb == 32);
  assert(mpz_size(op) >= 1);
  uint64_t limb_lo = static_cast<uint64_t>(mpz_getlimbn(op, 0));
  uint64_t limb_hi = 0;
  if (mpz_size(op) >= 2)
  {
    limb_hi = static_cast<uint64_t>(mpz_getlimbn(op, 1));
  }
  return (limb_hi << 32) | limb_lo;
}

void
mpz_init_set_ull(mpz_t rop, uint64_t op)
{
  if (sizeof(mp_bitcnt_t) == 4)  // 32 bit
  {
    uint32_t hi = static_cast<uint32_t>(op >> 32);
    uint32_t lo = static_cast<uint32_t>(op);
    mpz_init_set_ui(rop, hi);
    mpz_mul_2exp(rop, rop, 32);
    mpz_add_ui(rop, rop, lo);
  }
  else
  {
    mpz_init_set_ui(rop, op);
  }
}

mpz_class
uint64_to_mpz_class(uint64_t op)
{
  uint32_t hi = static_cast<uint32_t>(op >> 32);
  uint32_t lo = static_cast<uint32_t>(op);
  mpz_class res(hi);
  res = (res << 32) + lo;
  return res;
}

void
mpz_init_set_sll(mpz_t rop, int64_t op)
{
  if (sizeof(mp_bitcnt_t) == 4)  // 32 bit
  {
    int32_t hi = static_cast<int32_t>(op >> 32);
    int32_t lo = static_cast<int32_t>(op);
    mpz_init_set_si(rop, hi);
    mpz_mul_2exp(rop, rop, 32);
    mpz_add_ui(rop, rop, lo);
  }
  else
  {
    mpz_init_set_si(rop, op);
  }
}

size_t
mpz_hash(const mpz_t op)
{
  uint64_t i, j = 0, n, res = 0;
  uint64_t x, p0, p1;

  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size(op); i < n; ++i)
  {
    p0 = s_hash_primes[j++];
    if (j == s_n_primes) j = 0;
    p1 = s_hash_primes[j++];
    if (j == s_n_primes) j = 0;
    limb = mpz_getlimbn(op, i);
    if (mp_bits_per_limb == 64)
    {
      uint64_t lo = limb;
      uint64_t hi = (limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = s_hash_primes[j++];
      if (j == s_n_primes) j = 0;
      p1 = s_hash_primes[j++];
      if (j == s_n_primes) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert(mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
  return res;
}

// These functions only guard their *_ui counterparts with an assertion for the
// Windows 32-bit case. In the cases where these functions are used we should
// never use values that require more than 32 bit.
void
mpz_fdiv_q_2exp_ull(mpz_t q, const mpz_t n, uint64_t b)
{
  assert(sizeof(mp_bitcnt_t) == 8 || b <= UINT32_MAX);
  mpz_fdiv_q_2exp(q, n, b);
}

void
mpz_fdiv_r_2exp_ull(mpz_t r, const mpz_t n, uint64_t b)
{
  assert(sizeof(mp_bitcnt_t) == 8 || b <= UINT32_MAX);
  mpz_fdiv_r_2exp(r, n, b);
}

void
mpz_mul_2exp_ull(mpz_t rop, const mpz_t op1, uint64_t op2)
{
  assert(sizeof(mp_bitcnt_t) == 8 || op2 <= UINT32_MAX);
  mpz_mul_2exp(rop, op1, op2);
}

}  // namespace bzla::util
