#include "bitvector.h"

#include <cassert>
#include <iostream>
#include <sstream>
#include <unordered_set>
#include <utility>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "rng.h"

namespace bzla {

namespace {
#ifndef NDEBUG
/** Return true if given string is a valid binary string. */
bool
is_valid_bin_str(const std::string& str)
{
  for (const char& c : str)
  {
    if (c != '0' && c != '1') return false;
  }
  return true;
}
/** Return true if given string is a valid decimal string. */
bool
is_valid_dec_str(const std::string& str)
{
  std::unordered_set<char> digits{
      '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};
  for (size_t i = str[0] == '-' ? 1 : 0, n = str.size(); i < n; ++i)
  {
    if (digits.find(str[i]) == digits.end()) return false;
  }
  return true;
}
/** Return true if given string is a valid hexadecimal string. */
bool
is_valid_hex_str(const std::string& str)
{
  std::unordered_set<char> digits{'0',
                                  '1',
                                  '2',
                                  '3',
                                  '4',
                                  '5',
                                  '6',
                                  '7',
                                  '8',
                                  '9',
                                  'a',
                                  'b',
                                  'c',
                                  'd',
                                  'e',
                                  'f'};
  for (size_t i = 0, n = str.size(); i < n; ++i)
  {
    if (digits.find(str[i]) == digits.end()) return false;
  }
  return true;
}
#endif

#if !defined(__GNUC__) && !defined(__clang__)
static uint32_t
clz_limb(uint32_t nbits_per_limb, mp_limb_t limb)
{
  uint32_t w;
  mp_limb_t mask;
  mp_limb_t one = 1u;
  for (w = 0, mask = 0; w < nbits_per_limb; ++w)
  {
    mask += (one << w);
    if ((limb & ~mask) == 0) break;
  }
  return nbits_per_limb - 1 - w;
}
#endif
}  // namespace

bool
BitVector::fits_in_size(uint32_t size, const std::string& str, uint32_t base)
{
  bool is_neg = str[0] == '-';

  GMPMpz tmp;
  mpz_set_str(tmp.d_mpz, str.c_str(), base);

  if (is_neg)
  {
    BitVector min = BitVector::mk_min_signed(size);
    mpz_abs(tmp.d_mpz, tmp.d_mpz);
    return mpz_cmp(tmp.d_mpz, min.d_val->d_mpz) <= 0;
  }
  else
  {
    BitVector max = BitVector::mk_ones(size);
    return mpz_cmp(tmp.d_mpz, max.d_val->d_mpz) <= 0;
  }
}

bool
BitVector::fits_in_size(uint32_t size, uint64_t value, bool sign)
{
  if (sign)
  {
    return fits_in_size(size, std::to_string((int64_t) value), 10);
  }

  GMPMpz tmp;
  mpz_set_ui(tmp.d_mpz, value);
  return size >= mpz_sizeinbase(tmp.d_mpz, 2);
}

BitVector
BitVector::mk_true()
{
  return mk_one(1);
}

BitVector
BitVector::mk_false()
{
  return mk_zero(1);
}

BitVector
BitVector::mk_zero(uint32_t size)
{
  return BitVector(size);
}

BitVector
BitVector::mk_one(uint32_t size)
{
  return BitVector(size, 1);
}

BitVector
BitVector::mk_ones(uint32_t size)
{
  BitVector res = BitVector::mk_one(size);
  mpz_mul_2exp(res.d_val->d_mpz, res.d_val->d_mpz, size);
  mpz_sub_ui(res.d_val->d_mpz, res.d_val->d_mpz, 1);
  return res;
}

BitVector
BitVector::mk_min_signed(uint32_t size)
{
  BitVector res = BitVector::mk_zero(size);
  res.set_bit(size - 1, true);
  return res;
}

BitVector
BitVector::mk_max_signed(uint32_t size)
{
  BitVector res = BitVector::mk_ones(size);
  res.set_bit(size - 1, false);
  return res;
}

BitVector
BitVector::bvite(const BitVector& c, const BitVector& t, const BitVector& e)
{
  assert(!c.is_null());
  assert(!t.is_null());
  assert(!e.is_null());
  assert(c.d_size == 1);
  assert(t.d_size == e.d_size);
  return c.is_true() ? t : e;
}

BitVector::BitVector() : d_size(0), d_val(nullptr) {}

BitVector::BitVector(uint32_t size) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new GMPMpz());
}

BitVector::BitVector(uint32_t size, const RNG& rng) : BitVector(size)
{
  mpz_urandomb(d_val->d_mpz, rng.get_gmp_state()->d_gmp_randstate, size);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, size);
}

BitVector::BitVector(uint32_t size,
                     const RNG& rng,
                     const BitVector& from,
                     const BitVector& to,
                     bool sign)
    : BitVector(size)
{
  iset(rng, from, to, sign);
}

BitVector::BitVector(uint32_t size,
                     const RNG& rng,
                     uint32_t idx_hi,
                     uint32_t idx_lo)
    : BitVector(size, rng)
{
  for (uint32_t i = 0; i < idx_lo; ++i)
  {
    set_bit(i, false);
  }
  for (uint32_t i = idx_hi; i < d_size; ++i)
  {
    set_bit(i, false);
  }
}

BitVector::BitVector(uint32_t size, const std::string& value, uint32_t base)
    : d_size(size)
{
  assert(!value.empty());
  assert(base != 2 || is_valid_bin_str(value));
  assert(base != 10 || is_valid_dec_str(value));
  assert(base != 16 || is_valid_hex_str(value));
  assert(fits_in_size(size, value, base));
  d_val.reset(new GMPMpz(size, value, base));
}

BitVector::BitVector(uint32_t size, uint64_t value, bool sign) : d_size(size)
{
  assert(size > 0);
  assert(sign || fits_in_size(size, value));
  assert(!sign || fits_in_size(size, value, true));

  d_val.reset(new GMPMpz(size, value, sign));
}

BitVector::BitVector(const BitVector& other)
{
  if (other.is_null())
  {
    d_size = 0;
    d_val.reset(nullptr);
  }
  else
  {
    if (d_size != other.d_size)
    {
      d_size = other.d_size;
      d_val.reset(new GMPMpz());
    }
    mpz_set(d_val->d_mpz, other.d_val->d_mpz);
  }
}

BitVector::BitVector(BitVector&& other)
    : d_size(std::exchange(other.d_size, 0)), d_val(std::move(other.d_val))
{
}

BitVector::~BitVector() {}

BitVector&
BitVector::operator=(const BitVector& other)
{
  if (&other == this) return *this;
  if (other.is_null())
  {
    d_size = 0;
    d_val.reset(nullptr);
  }
  else
  {
    if (d_size != other.d_size)
    {
      d_size = other.d_size;
      d_val.reset(new GMPMpz());
    }
    mpz_set(d_val->d_mpz, other.d_val->d_mpz);
  }
  return *this;
}

size_t
BitVector::hash() const
{
  uint32_t i, j = 0, n, res = 0;
  uint32_t x, p0, p1;

  res = d_size * s_hash_primes[j++];

  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size(d_val->d_mpz); i < n; ++i)
  {
    p0 = s_hash_primes[j++];
    if (j == s_n_primes) j = 0;
    p1 = s_hash_primes[j++];
    if (j == s_n_primes) j = 0;
    limb = mpz_getlimbn(d_val->d_mpz, i);
    if (mp_bits_per_limb == 64)
    {
      uint32_t lo = (uint32_t) limb;
      uint32_t hi = (uint32_t) (limb >> 32);
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

void
BitVector::iset(uint64_t value)
{
  assert(!is_null());
  assert(d_size);
  mpz_set_ui(d_val->d_mpz, value);
}

void
BitVector::iset(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  mpz_set(d_val->d_mpz, bv.d_val->d_mpz);
}

void
BitVector::iset(const RNG& rng,
                const BitVector& from,
                const BitVector& to,
                bool is_signed)
{
  assert(!is_null());
  assert(!from.is_null());
  assert(!to.is_null());
  assert(d_size == from.d_size);
  assert(d_size == to.d_size);
  assert(is_signed || from.compare(to) <= 0);
  assert(!is_signed || from.signed_compare(to) <= 0);
  mpz_t _to;
  if (is_signed)
  {
    BitVector sto   = to.bvsub(from);
    BitVector sfrom = mk_zero(d_size);
    mpz_init_set(_to, sto.d_val->d_mpz);
    mpz_sub(_to, _to, sfrom.d_val->d_mpz);
  }
  else
  {
    mpz_init_set(_to, to.d_val->d_mpz);
    mpz_sub(_to, _to, from.d_val->d_mpz);
  }
  mpz_add_ui(_to, _to, 1);
  mpz_urandomm(d_val->d_mpz, rng.get_gmp_state()->d_gmp_randstate, _to);
  if (is_signed)
  {
    // add from to picked value
    mpz_add(d_val->d_mpz, d_val->d_mpz, from.d_val->d_mpz);
    mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  }
  else
  {
    mpz_add(d_val->d_mpz, d_val->d_mpz, from.d_val->d_mpz);
  }
  mpz_clear(_to);
}

bool
BitVector::operator==(const BitVector& bv)
{
  return compare(bv) == 0;
}

bool
BitVector::operator!=(const BitVector& bv)
{
  return compare(bv) != 0;
}

std::string
BitVector::to_string(uint32_t base) const
{
  assert(!is_null());
  std::stringstream res;
  char* tmp = mpz_get_str(0, base, d_val->d_mpz);
  assert(tmp[0] != '-');  // may not be negative
  if (base == 2)
  {
    /* Pad with leading zeros for binary representation. */
    uint32_t n    = strlen(tmp);
    uint32_t diff = d_size - n;
    assert(n <= d_size);
    res << std::string(diff, '0');
  }
  res << tmp;
  assert(base != 2 || res.str().size() == d_size);
  free(tmp);
  return res.str();
}

uint64_t
BitVector::to_uint64() const
{
  assert(!is_null());
  assert(d_size <= 64);
  return mpz_get_ui(d_val->d_mpz);
}

int32_t
BitVector::compare(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz);
}

int32_t
BitVector::signed_compare(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);

  uint32_t msb_a = get_msb();
  uint32_t msb_b = bv.get_msb();

  if (msb_a && !msb_b)
  {
    return -1;
  }
  if (!msb_a && msb_b)
  {
    return 1;
  }
  return compare(bv);
}

bool
BitVector::get_bit(uint32_t idx) const
{
  assert(!is_null());
  assert(idx < size());
  return mpz_tstbit(d_val->d_mpz, idx);
}

void
BitVector::set_bit(uint32_t idx, bool value)
{
  assert(!is_null());
  if (value)
  {
    mpz_setbit(d_val->d_mpz, idx);
  }
  else
  {
    mpz_clrbit(d_val->d_mpz, idx);
  }
}

void
BitVector::flip_bit(uint32_t idx)
{
  assert(!is_null());
  mpz_combit(d_val->d_mpz, idx);
}

bool
BitVector::get_lsb() const
{
  assert(!is_null());
  return get_bit(0);
}

bool
BitVector::get_msb() const
{
  assert(!is_null());
  return get_bit(d_size - 1);
}

bool
BitVector::is_true() const
{
  assert(!is_null());
  if (d_size > 1) return false;
  return get_bit(0);
}

bool
BitVector::is_false() const
{
  assert(!is_null());
  if (d_size > 1) return false;
  return !get_bit(0);
}

bool
BitVector::is_zero() const
{
  assert(!is_null());
  return mpz_cmp_ui(d_val->d_mpz, 0) == 0;
}

bool
BitVector::is_ones() const
{
  assert(!is_null());
  uint32_t n = mpz_size(d_val->d_mpz);
  if (n == 0) return false;  // zero
  uint64_t m = d_size / mp_bits_per_limb;
  if (d_size % mp_bits_per_limb) m += 1;
  if (m != n) return false;  // less limbs used than expected, not ones
  uint64_t max = mp_bits_per_limb == 64 ? UINT64_MAX : UINT32_MAX;
  for (uint32_t i = 0; i < n - 1; ++i)
  {
    mp_limb_t limb = mpz_getlimbn(d_val->d_mpz, i);
    if (((uint64_t) limb) != max) return false;
  }
  mp_limb_t limb = mpz_getlimbn(d_val->d_mpz, n - 1);
  if (d_size == (uint32_t) mp_bits_per_limb) return ((uint64_t) limb) == max;
  m = mp_bits_per_limb - d_size % mp_bits_per_limb;
  return ((uint64_t) limb) == (max >> m);
}

bool
BitVector::is_one() const
{
  assert(!is_null());
  return mpz_cmp_ui(d_val->d_mpz, 1) == 0;
}

bool
BitVector::is_min_signed() const
{
  assert(!is_null());
  if (mpz_scan1(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_max_signed() const
{
  assert(!is_null());
  if (mpz_scan0(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_power_of_two() const
{
  assert(!is_null());
  return !is_zero() && bvdec().ibvand(*this).is_zero();
}

bool
BitVector::is_uadd_overflow(const BitVector& bv) const
{
  assert(!is_null());
  assert(d_size == bv.d_size);
  mpz_t add;
  mpz_init(add);
  mpz_add(add, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_q_2exp(add, add, d_size);
  bool res = mpz_cmp_ui(add, 0) != 0;
  mpz_clear(add);
  return res;
}

bool
BitVector::is_umul_overflow(const BitVector& bv) const
{
  assert(!is_null());
  assert(d_size == bv.d_size);
  if (d_size > 1)
  {
    mpz_t mul;
    mpz_init(mul);
    mpz_mul(mul, d_val->d_mpz, bv.d_val->d_mpz);
    mpz_fdiv_q_2exp(mul, mul, d_size);
    bool res = mpz_cmp_ui(mul, 0) != 0;
    mpz_clear(mul);
    return res;
  }
  return false;
}

uint32_t
BitVector::count_trailing_zeros() const
{
  assert(!is_null());
  uint32_t res = mpz_scan1(d_val->d_mpz, 0);
  if (res > d_size) res = d_size;
  return res;
}

uint32_t
BitVector::count_leading_zeros() const
{
  assert(!is_null());
  return count_leading(true);
}

uint32_t
BitVector::count_leading_ones() const
{
  assert(!is_null());
  return count_leading(false);
}

/* -------------------------------------------------------------------------- */
/* Bit-vector operations.                                                     */
/* -------------------------------------------------------------------------- */

BitVector
BitVector::bvneg() const
{
  assert(!is_null());
  BitVector res = bvnot();
  mpz_add_ui(res.d_val->d_mpz, res.d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvnot() const
{
  assert(!is_null());
  BitVector res(d_size);
  mpz_com(res.d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvinc() const
{
  assert(!is_null());
  BitVector res(d_size);
  mpz_add_ui(res.d_val->d_mpz, d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvdec() const
{
  assert(!is_null());
  BitVector res(d_size);
  mpz_sub_ui(res.d_val->d_mpz, d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvredand() const
{
  assert(!is_null());
  return is_ones() ? mk_true() : mk_false();
}

BitVector
BitVector::bvredor() const
{
  assert(!is_null());
  mp_limb_t limb;
  for (size_t i = 0, n = mpz_size(d_val->d_mpz); i < n; ++i)
  {
    limb = mpz_getlimbn(d_val->d_mpz, i);
    if (((uint64_t) limb) != 0) return mk_true();
  }
  return mk_false();
}

BitVector
BitVector::bvadd(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_add(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvsub(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_sub(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvand(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_and(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvimplies(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == 1);
  assert(d_size == bv.d_size);
  return is_false() || bv.is_true() ? mk_true() : mk_false();
}

BitVector
BitVector::bvnand(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_and(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvnor(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_ior(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvor(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_ior(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvxnor(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_xor(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_com(res.d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvxor(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_xor(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bveq(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) == 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvne(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) != 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvult(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) < 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvule(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) <= 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvugt(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) > 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvuge(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  return mpz_cmp(d_val->d_mpz, bv.d_val->d_mpz) >= 0 ? mk_true() : mk_false();
}

BitVector
BitVector::bvslt(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool msb       = get_msb();
  bool msb_other = bv.get_msb();
  if (msb && !msb_other)
  {
    return mk_true();
  }
  if (!msb && msb_other)
  {
    return mk_false();
  }
  return bvult(bv);
}

BitVector
BitVector::bvsle(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool msb       = get_msb();
  bool msb_other = bv.get_msb();
  if (msb && !msb_other)
  {
    return mk_true();
  }
  if (!msb && msb_other)
  {
    return mk_false();
  }
  return bvule(bv);
}

BitVector
BitVector::bvsgt(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool msb       = get_msb();
  bool msb_other = bv.get_msb();
  if (msb && !msb_other)
  {
    return mk_false();
  }
  if (!msb && msb_other)
  {
    return mk_true();
  }
  return bvugt(bv);
}

BitVector
BitVector::bvsge(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool msb       = get_msb();
  bool msb_other = bv.get_msb();
  if (msb && !msb_other)
  {
    return mk_false();
  }
  if (!msb && msb_other)
  {
    return mk_true();
  }
  return bvuge(bv);
}

BitVector
BitVector::bvshl(uint32_t shift) const
{
  assert(!is_null());
  BitVector res(d_size);
  if (shift >= d_size) return res;
  mpz_mul_2exp(res.d_val->d_mpz, d_val->d_mpz, shift);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvshl(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  uint32_t shift;
  if (bv.shift_is_uint64(&shift))
  {
    return bvshl(shift);
  }
  return BitVector(d_size);
}

BitVector
BitVector::bvshr(uint32_t shift) const
{
  assert(!is_null());
  BitVector res(d_size);
  if (shift >= d_size) return res;
  mpz_fdiv_q_2exp(res.d_val->d_mpz, d_val->d_mpz, shift);
  return res;
}

BitVector
BitVector::bvshr(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  uint32_t shift;
  if (bv.shift_is_uint64(&shift))
  {
    return bvshr(shift);
  }
  return BitVector(d_size);
}

BitVector
BitVector::bvashr(uint32_t shift) const
{
  assert(!is_null());
  if (shift >= d_size)
  {
    return get_msb() ? mk_ones(d_size) : mk_zero(d_size);
  }
  if (get_msb())
  {
    return bvnot().bvshr(shift).bvnot();
  }
  return bvshr(shift);
}

BitVector
BitVector::bvashr(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (get_msb())
  {
    return bvnot().bvshr(bv).bvnot();
  }
  return bvshr(bv);
}

BitVector
BitVector::bvmul(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  BitVector res(d_size);
  mpz_mul(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvudiv(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (bv.is_zero()) return mk_ones(d_size);
  BitVector res(d_size);
  mpz_fdiv_q(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvurem(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (bv.is_zero()) return *this;
  BitVector res(d_size);
  mpz_fdiv_r(res.d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
  return res;
}

BitVector
BitVector::bvsdiv(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool is_signed       = get_msb();
  bool is_signed_other = bv.get_msb();

  if (is_signed && !is_signed_other)
  {
    return bvneg().bvudiv(bv).bvneg();
  }
  if (!is_signed && is_signed_other)
  {
    return bvudiv(bv.bvneg()).bvneg();
  }
  if (is_signed && is_signed_other)
  {
    return bvneg().bvudiv(bv.bvneg());
  }
  return bvudiv(bv);
}

BitVector
BitVector::bvsrem(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  bool is_signed       = get_msb();
  bool is_signed_other = bv.get_msb();

  if (is_signed && !is_signed_other)
  {
    return bvneg().bvurem(bv).bvneg();
  }
  if (!is_signed && is_signed_other)
  {
    return bvurem(bv.bvneg());
  }
  if (is_signed && is_signed_other)
  {
    return bvneg().bvurem(bv.bvneg()).bvneg();
  }
  return bvurem(bv);
}

BitVector
BitVector::bvconcat(const BitVector& bv) const
{
  assert(!is_null());
  assert(!bv.is_null());
  uint32_t size = d_size + bv.d_size;
  BitVector res(size);
  mpz_mul_2exp(res.d_val->d_mpz, d_val->d_mpz, bv.d_size);
  mpz_add(res.d_val->d_mpz, res.d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, size);
  return res;
}

BitVector
BitVector::bvextract(uint32_t idx_hi, uint32_t idx_lo) const
{
  assert(!is_null());
  assert(idx_hi >= idx_lo);
  uint32_t size = idx_hi - idx_lo + 1;
  BitVector res(size);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, d_val->d_mpz, idx_hi + 1);
  mpz_fdiv_q_2exp(res.d_val->d_mpz, res.d_val->d_mpz, idx_lo);
  return res;
}

BitVector
BitVector::bvzext(uint32_t n) const
{
  assert(!is_null());
  if (n == 0) return *this;
  uint32_t size = d_size + n;
  BitVector res(size);
  mpz_set(res.d_val->d_mpz, d_val->d_mpz);
  return res;
}

BitVector
BitVector::bvsext(uint32_t n) const
{
  assert(!is_null());
  if (n == 0) return *this;
  if (get_msb())
  {
    return mk_ones(n).bvconcat(*this);
  }
  return bvzext(n);
}

BitVector
BitVector::bvmodinv() const
{
  assert(!is_null());
  assert(get_lsb()); /* must be odd */
  BitVector res(d_size);
  if (d_size == 1)
  {
    mpz_set_ui(res.d_val->d_mpz, 1);
  }
  else
  {
    mpz_t two;
    mpz_init(two);
    mpz_setbit(two, d_size);
    mpz_invert(res.d_val->d_mpz, d_val->d_mpz, two);
    mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, d_size);
    mpz_clear(two);
  }

#ifndef NDEBUG
  mpz_t ty;
  assert(res.d_size == d_size);
  mpz_init(ty);
  mpz_mul(ty, d_val->d_mpz, res.d_val->d_mpz);
  mpz_fdiv_r_2exp(ty, ty, d_size);
  assert(!mpz_cmp_ui(ty, 1));
  mpz_clear(ty);
#endif
  return res;
}

/* -------------------------------------------------------------------------- */
/* Bit-vector operations, in-place, requires all operands as arguments.       */
/* -------------------------------------------------------------------------- */

BitVector&
BitVector::ibvneg(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  ibvnot(bv);
  mpz_add_ui(d_val->d_mpz, d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvnot(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  mpz_com(d_val->d_mpz, bv.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvinc(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  mpz_add_ui(d_val->d_mpz, bv.d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvdec(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  mpz_sub_ui(d_val->d_mpz, bv.d_val->d_mpz, 1);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvredand(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  if (bv.is_ones())
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvredor(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  mp_limb_t limb;
  uint32_t val = 0;
  for (size_t i = 0, n = mpz_size(bv.d_val->d_mpz); i < n; ++i)
  {
    limb = mpz_getlimbn(bv.d_val->d_mpz, i);
    if (((uint64_t) limb) != 0)
    {
      val = 1;
      break;
    }
  }
  mpz_set_ui(d_val->d_mpz, val);
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvadd(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_add(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvsub(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_sub(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvand(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_and(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvimplies(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == 1);
  assert(bv1.d_size == 1);
  if (bv0.is_false() || bv1.is_true())
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvnand(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_and(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_com(d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvnor(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_ior(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_com(d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvor(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_ior(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvxnor(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_xor(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_com(d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvxor(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_xor(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibveq(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) == 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvne(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) != 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvult(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) < 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvule(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) <= 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvugt(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) > 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvuge(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  if (mpz_cmp(bv0.d_val->d_mpz, bv1.d_val->d_mpz) >= 0)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvslt(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  bool msb_bv0 = bv0.get_msb();
  bool msb_bv1 = bv1.get_msb();
  if (msb_bv0 && !msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else if (!msb_bv0 && msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  else
  {
    ibvult(bv0, bv1);
  }
  d_size = 1;
  return *this;
}

BitVector&
BitVector::ibvsle(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  bool msb_bv0 = bv0.get_msb();
  bool msb_bv1 = bv1.get_msb();
  if (msb_bv0 && !msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 1);
    d_size = 1;
  }
  else if (!msb_bv0 && msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 0);
    d_size = 1;
  }
  else
  {
    ibvule(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvsgt(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  bool msb_bv0 = bv0.get_msb();
  bool msb_bv1 = bv1.get_msb();
  if (msb_bv0 && !msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 0);
    d_size = 1;
  }
  else if (!msb_bv0 && msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 1);
    d_size = 1;
  }
  else
  {
    ibvugt(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvsge(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(bv0.d_size == bv1.d_size);
  bool msb_bv0 = bv0.get_msb();
  bool msb_bv1 = bv1.get_msb();
  if (msb_bv0 && !msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 0);
    d_size = 1;
  }
  else if (!msb_bv0 && msb_bv1)
  {
    mpz_set_ui(d_val->d_mpz, 1);
    d_size = 1;
  }
  else
  {
    ibvuge(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvshl(const BitVector& bv, uint32_t shift)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (shift >= d_size)
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  else
  {
    mpz_mul_2exp(d_val->d_mpz, bv.d_val->d_mpz, shift);
    mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  }
  return *this;
}

BitVector&
BitVector::ibvshl(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  uint32_t shift;
  if (bv1.shift_is_uint64(&shift))
  {
    ibvshl(bv0, shift);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  return *this;
}

BitVector&
BitVector::ibvshr(const BitVector& bv, uint32_t shift)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (shift >= d_size)
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  else
  {
    mpz_fdiv_q_2exp(d_val->d_mpz, bv.d_val->d_mpz, shift);
  }
  return *this;
}

BitVector&
BitVector::ibvshr(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  uint32_t shift;
  if (bv1.shift_is_uint64(&shift))
  {
    ibvshr(bv0, shift);
  }
  else
  {
    mpz_set_ui(d_val->d_mpz, 0);
  }
  return *this;
}

BitVector&
BitVector::ibvashr(const BitVector& bv, uint32_t shift)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  if (bv.get_msb())
  {
    ibvnot(bv).ibvshr(shift).ibvnot();
  }
  else
  {
    ibvshr(bv, shift);
  }
  return *this;
}

BitVector&
BitVector::ibvashr(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  if (bv0.get_msb())
  {
    if (&bv1 == this)
    {
      BitVector b1(bv1); /* copy to guard against the case when bv1 == *this */
      ibvnot(bv0).ibvshr(b1);
    }
    else
    {
      ibvnot(bv0).ibvshr(bv1);
    }
    ibvnot();
  }
  else
  {
    ibvshr(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvmul(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  mpz_mul(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvudiv(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  if (bv1.is_zero())
  {
    mpz_set_ui(d_val->d_mpz, 1);
    mpz_mul_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
    mpz_sub_ui(d_val->d_mpz, d_val->d_mpz, 1);
  }
  else
  {
    mpz_fdiv_q(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
    mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  }
  return *this;
}

BitVector&
BitVector::ibvurem(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  if (!bv1.is_zero())
  {
    mpz_fdiv_r(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_val->d_mpz);
    mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  }
  else
  {
    mpz_set(d_val->d_mpz, bv0.d_val->d_mpz);
  }
  return *this;
}

BitVector&
BitVector::ibvsdiv(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  bool is_signed_bv0 = bv0.get_msb();
  bool is_signed_bv1 = bv1.get_msb();

  if (is_signed_bv0 && !is_signed_bv1)
  {
    if (&bv1 == this)
    {
      BitVector b1(bv1); /* copy to guard against the case when bv1 == *this */
      ibvneg(bv0).ibvudiv(b1);
    }
    else
    {
      ibvneg(bv0).ibvudiv(bv1);
    }
    ibvneg(*this);
  }
  else if (!is_signed_bv0 && is_signed_bv1)
  {
    if (&bv0 == this)
    {
      BitVector b0(bv0); /* copy to guard against the case when bv0 == *this */
      ibvneg(bv1).ibvudiv(b0, *this);
    }
    else
    {
      ibvneg(bv1).ibvudiv(bv0, *this);
    }
    ibvneg(*this);
  }
  else if (is_signed_bv0 && is_signed_bv1)
  {
    BitVector b1neg(bv1.bvneg());
    ibvneg(bv0).ibvudiv(b1neg);
  }
  else
  {
    ibvudiv(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvsrem(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  assert(d_size == bv0.d_size);
  assert(d_size == bv1.d_size);
  bool is_signed_bv0 = bv0.get_msb();
  bool is_signed_bv1 = bv1.get_msb();

  if (is_signed_bv0 && !is_signed_bv1)
  {
    if (&bv1 == this)
    {
      BitVector b1(bv1); /* copy to guard against the case when bv1 == *this */
      ibvneg(bv0).ibvurem(b1);
    }
    else
    {
      ibvneg(bv0).ibvurem(bv1);
    }
    ibvneg(*this);
  }
  else if (!is_signed_bv0 && is_signed_bv1)
  {
    if (&bv0 == this)
    {
      BitVector b0(bv0); /* copy to guard against the case when bv0 == *this */
      ibvneg(bv1).ibvurem(b0, *this);
    }
    else
    {
      ibvneg(bv1).ibvurem(bv0, *this);
    }
  }
  else if (is_signed_bv0 && is_signed_bv1)
  {
    BitVector b1neg(bv1.bvneg());
    ibvneg(bv0).ibvurem(b1neg).ibvneg();
  }
  else
  {
    ibvurem(bv0, bv1);
  }
  return *this;
}

BitVector&
BitVector::ibvconcat(const BitVector& bv0, const BitVector& bv1)
{
  assert(!is_null());
  assert(!bv0.is_null());
  assert(!bv1.is_null());
  if (&bv1 == this)
  {
    BitVector b1(bv1); /* copy to guard against the case when bv1 == *this */
    mpz_mul_2exp(d_val->d_mpz, bv0.d_val->d_mpz, b1.d_size);
    mpz_add(d_val->d_mpz, d_val->d_mpz, b1.d_val->d_mpz);
  }
  else
  {
    mpz_mul_2exp(d_val->d_mpz, bv0.d_val->d_mpz, bv1.d_size);
    mpz_add(d_val->d_mpz, d_val->d_mpz, bv1.d_val->d_mpz);
  }
  d_size = bv0.d_size + bv1.d_size;
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
  return *this;
}

BitVector&
BitVector::ibvextract(const BitVector& bv, uint32_t idx_hi, uint32_t idx_lo)
{
  assert(!is_null());
  assert(!bv.is_null());
  mpz_fdiv_r_2exp(d_val->d_mpz, bv.d_val->d_mpz, idx_hi + 1);
  mpz_fdiv_q_2exp(d_val->d_mpz, d_val->d_mpz, idx_lo);
  d_size = idx_hi - idx_lo + 1;
  return *this;
}

BitVector&
BitVector::ibvzext(const BitVector& bv, uint32_t n)
{
  assert(!is_null());
  assert(!bv.is_null());
  mpz_set(d_val->d_mpz, bv.d_val->d_mpz);
  d_size = bv.d_size + n;
  return *this;
}

BitVector&
BitVector::ibvsext(const BitVector& bv, uint32_t n)
{
  assert(!is_null());
  assert(!bv.is_null());
  if (n > 0)
  {
    if (bv.get_msb())
    {
      uint32_t size = bv.d_size;
      if (&bv == this)
      {
        BitVector b(bv); /* copy to guard against the case when bv == *this */
        mpz_set_ui(d_val->d_mpz, 1);
        mpz_mul_2exp(d_val->d_mpz, d_val->d_mpz, n);
        mpz_sub_ui(d_val->d_mpz, d_val->d_mpz, 1);
        mpz_mul_2exp(d_val->d_mpz, d_val->d_mpz, size);
        mpz_add(d_val->d_mpz, d_val->d_mpz, b.d_val->d_mpz);
      }
      else
      {
        mpz_set_ui(d_val->d_mpz, 1);
        mpz_mul_2exp(d_val->d_mpz, d_val->d_mpz, n);
        mpz_sub_ui(d_val->d_mpz, d_val->d_mpz, 1);
        mpz_mul_2exp(d_val->d_mpz, d_val->d_mpz, size);
        mpz_add(d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
      }
      d_size = size + n;
      mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
    }
    else
    {
      ibvzext(bv, n);
    }
  }
  else
  {
    mpz_set(d_val->d_mpz, bv.d_val->d_mpz);
  }
  return *this;
}

BitVector&
BitVector::ibvite(const BitVector& c, const BitVector& t, const BitVector& e)
{
  assert(!is_null());
  assert(!c.is_null());
  assert(!t.is_null());
  assert(!e.is_null());
  assert(c.d_size == 1);
  assert(e.d_size == t.d_size);
  if (c.is_true())
  {
    mpz_set(d_val->d_mpz, t.d_val->d_mpz);
  }
  else
  {
    mpz_set(d_val->d_mpz, e.d_val->d_mpz);
  }
  d_size = t.d_size;
  return *this;
}

BitVector&
BitVector::ibvmodinv(const BitVector& bv)
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);
  assert(bv.get_lsb()); /* must be odd */
#ifndef NDEBUG
  BitVector b(bv); /* copy to guard against the case when bv == *this */
#endif
  if (d_size == 1)
  {
    mpz_set_ui(d_val->d_mpz, 1);
  }
  else
  {
    mpz_t two;
    mpz_init(two);
    mpz_setbit(two, d_size);
    mpz_invert(d_val->d_mpz, bv.d_val->d_mpz, two);
    mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, d_size);
    mpz_clear(two);
  }
#ifndef NDEBUG
  mpz_t ty;
  assert(d_size == b.d_size);
  mpz_init(ty);
  mpz_mul(ty, b.d_val->d_mpz, d_val->d_mpz);
  mpz_fdiv_r_2exp(ty, ty, d_size);
  assert(!mpz_cmp_ui(ty, 1));
  mpz_clear(ty);
#endif
  return *this;
}

/* -------------------------------------------------------------------------- */
/* Bit-vector operations, in-place, 'this' is first argument.                 */
/* -------------------------------------------------------------------------- */

BitVector&
BitVector::ibvneg()
{
  ibvneg(*this);
  return *this;
}

BitVector&
BitVector::ibvnot()
{
  ibvnot(*this);
  return *this;
}

BitVector&
BitVector::ibvinc()
{
  ibvinc(*this);
  return *this;
}

BitVector&
BitVector::ibvdec()
{
  ibvdec(*this);
  return *this;
}

BitVector&
BitVector::ibvredand()
{
  ibvredand(*this);
  return *this;
}

BitVector&
BitVector::ibvredor()
{
  ibvredor(*this);
  return *this;
}

BitVector&
BitVector::ibvadd(const BitVector& bv)
{
  ibvadd(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvand(const BitVector& bv)
{
  ibvand(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvimplies(const BitVector& bv)
{
  ibvimplies(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvnand(const BitVector& bv)
{
  ibvnand(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvnor(const BitVector& bv)
{
  ibvnor(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvor(const BitVector& bv)
{
  ibvor(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsub(const BitVector& bv)
{
  ibvsub(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvxnor(const BitVector& bv)
{
  ibvxnor(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvxor(const BitVector& bv)
{
  ibvxor(*this, bv);
  return *this;
}

BitVector&
BitVector::ibveq(const BitVector& bv)
{
  ibveq(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvne(const BitVector& bv)
{
  ibvne(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvult(const BitVector& bv)
{
  ibvult(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvule(const BitVector& bv)
{
  ibvule(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvugt(const BitVector& bv)
{
  ibvugt(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvuge(const BitVector& bv)
{
  ibvuge(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvslt(const BitVector& bv)
{
  ibvslt(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsle(const BitVector& bv)
{
  ibvsle(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsgt(const BitVector& bv)
{
  ibvsgt(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsge(const BitVector& bv)
{
  ibvsge(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvshl(uint32_t shift)
{
  ibvshl(*this, shift);
  return *this;
}

BitVector&
BitVector::ibvshl(const BitVector& bv)
{
  ibvshl(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvshr(uint32_t shift)
{
  ibvshr(*this, shift);
  return *this;
}

BitVector&
BitVector::ibvshr(const BitVector& bv)
{
  ibvshr(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvashr(uint32_t shift)
{
  ibvashr(*this, shift);
  return *this;
}

BitVector&
BitVector::ibvashr(const BitVector& bv)
{
  ibvashr(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvmul(const BitVector& bv)
{
  ibvmul(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvudiv(const BitVector& bv)
{
  ibvudiv(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvurem(const BitVector& bv)
{
  ibvurem(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsdiv(const BitVector& bv)
{
  ibvsdiv(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvsrem(const BitVector& bv)
{
  ibvsrem(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvconcat(const BitVector& bv)
{
  ibvconcat(*this, bv);
  return *this;
}

BitVector&
BitVector::ibvextract(uint32_t idx_hi, uint32_t idx_lo)
{
  ibvextract(*this, idx_hi, idx_lo);
  return *this;
}

BitVector&
BitVector::ibvzext(uint32_t n)
{
  ibvzext(*this, n);
  return *this;
}

BitVector&
BitVector::ibvsext(uint32_t n)
{
  ibvsext(*this, n);
  return *this;
}

BitVector&
BitVector::ibvmodinv()
{
  ibvmodinv(*this);
  return *this;
}

/* -------------------------------------------------------------------------- */

void
BitVector::bvudivurem(const BitVector& bv,
                      BitVector* quot,
                      BitVector* rem) const
{
  assert(!is_null());
  assert(!bv.is_null());
  assert(d_size == bv.d_size);

  if (bv.is_zero())
  {
    *quot = mk_ones(d_size);
    *rem  = *this;
  }
  else
  {
    *quot = mk_zero(d_size);
    *rem  = mk_zero(d_size);
    mpz_fdiv_qr(
        quot->d_val->d_mpz, rem->d_val->d_mpz, d_val->d_mpz, bv.d_val->d_mpz);
    mpz_fdiv_r_2exp(quot->d_val->d_mpz, quot->d_val->d_mpz, d_size);
    mpz_fdiv_r_2exp(rem->d_val->d_mpz, rem->d_val->d_mpz, d_size);
  }
}

/* -------------------------------------------------------------------------- */

uint32_t
BitVector::count_leading(bool zeros) const
{
  assert(!is_null());
  uint32_t res = 0;
  mp_limb_t limb;

  uint32_t nbits_per_limb = mp_bits_per_limb;
  /* The number of bits that spill over into the most significant limb,
   * assuming that all bits are represented). Zero if the bit-width is a
   * multiple of n_bits_per_limb. */
  uint32_t nbits_rem = d_size % nbits_per_limb;
  /* The number of limbs required to represent the actual value.
   * Zero limbs are disregarded. */
  uint32_t n_limbs = get_limb(&limb, nbits_rem, zeros);
  if (n_limbs == 0) return d_size;
#if defined(__GNUC__) || defined(__clang__)
  res = nbits_per_limb == 64 ? __builtin_clzll(limb) : __builtin_clz(limb);
#else
  res = clz_limb(nbits_per_limb, limb);
#endif
  /* Number of limbs required when representing all bits. */
  uint32_t n_limbs_total = d_size / nbits_per_limb + 1;
  uint32_t nbits_pad     = nbits_per_limb - nbits_rem;
  res += (n_limbs_total - n_limbs) * nbits_per_limb - nbits_pad;
  return res;
}

uint32_t
BitVector::get_limb(void* limb, uint32_t nbits_rem, bool zeros) const
{
  assert(!is_null());
  mp_limb_t* gmp_limb = static_cast<mp_limb_t*>(limb);
  /* GMP normalizes the limbs, the left most (most significant) is never 0 */
  uint32_t i, n_limbs, n_limbs_total;
  mp_limb_t res = 0u, mask;

  n_limbs = mpz_size(d_val->d_mpz);

  /* for leading zeros */
  if (zeros)
  {
    *gmp_limb = n_limbs ? mpz_getlimbn(d_val->d_mpz, n_limbs - 1) : 0;
    return n_limbs;
  }

  /* for leading ones */
  n_limbs_total = d_size / mp_bits_per_limb + (nbits_rem ? 1 : 0);
  if (n_limbs != n_limbs_total)
  {
    /* no leading ones, simulate */
    *gmp_limb = nbits_rem ? ~(~((mp_limb_t) 0) << nbits_rem) : ~((mp_limb_t) 0);
    return n_limbs_total;
  }
  mask = ~((mp_limb_t) 0) << nbits_rem;
  for (i = 0; i < n_limbs; i++)
  {
    res = mpz_getlimbn(d_val->d_mpz, n_limbs - 1 - i);
    if (nbits_rem && i == 0)
    {
      res = res | mask;
    }
    res = ~res;
    if (res > 0) break;
  }
  *gmp_limb = res;
  return n_limbs - i;
}

bool
BitVector::shift_is_uint64(uint32_t* res) const
{
  if (d_size <= 64)
  {
    *res = to_uint64();
    return true;
  }

  uint32_t clz = count_leading_zeros();
  if (clz < d_size - 64) return false;

  BitVector shift = bvextract(clz < d_size ? d_size - 1 - clz : 0, 0);
  assert(shift.d_size <= 64);
  *res = shift.to_uint64();
  return true;
}

std::ostream&
operator<<(std::ostream& out, const BitVector& bv)
{
  out << bv.to_string();
  return out;
}

}  // namespace bzla

namespace std {

size_t
hash<bzla::BitVector>::operator()(const bzla::BitVector& bv) const
{
  return bv.hash();
}

}  // namespace std
