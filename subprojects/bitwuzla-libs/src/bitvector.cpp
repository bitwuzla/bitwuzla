#include "bitvector.h"

#include <cassert>
#include <sstream>

#include "gmpmpz.h"
#include "gmprandstate.h"
#include "rng.h"

namespace bzlals {

namespace {
bool
is_bin_str(std::string str)
{
  for (const char& c : str)
  {
    if (c != '0' && c != '1') return false;
  }
  return true;
}
}  // namespace

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
  // TODO
}

BitVector::BitVector() : d_size(0), d_val(nullptr) {}

BitVector::BitVector(uint32_t size) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new GMPMpz());
}

BitVector::BitVector(uint32_t size, const RNG& rng) : BitVector(size)
{
  mpz_urandomb(d_val->d_mpz, rng.d_gmp_state->d_gmp_randstate, size);
  mpz_fdiv_r_2exp(d_val->d_mpz, d_val->d_mpz, size);
}

// BitVector::BitVector(uint32_t size, RNG& rng, const BitVector& from, const
// BitVector& to, bool is_signed = false){} BitVector::BitVector(uint32_t size,
// RNG& rng, uint32_t idx_hi, uint32_t idx_lo){}

BitVector::BitVector(uint32_t size, const std::string& value) : d_size(size)
{
  assert(value.size() <= size);
  assert(is_bin_str(value));
  d_val.reset(new GMPMpz(value));
}

BitVector::BitVector(uint32_t size, uint64_t value) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new GMPMpz(size, value));
}

BitVector::BitVector(const BitVector& other)
{
  d_size = other.d_size;
  d_val.reset(new GMPMpz());
  mpz_set(d_val->d_mpz, other.d_val->d_mpz);
}

BitVector::~BitVector() {}

BitVector&
BitVector::operator=(const BitVector& other)
{
  if (&other == this) return *this;
  d_size = other.d_size;
  d_val.reset(new GMPMpz());
  mpz_set(d_val->d_mpz, other.d_val->d_mpz);
}

std::string
BitVector::to_string() const
{
  std::stringstream res;
  char* tmp     = mpz_get_str(0, 2, d_val->d_mpz);
  uint32_t n    = strlen(tmp);
  uint32_t diff = d_size - n;
  assert(n <= d_size);
  res << std::string(diff, '0') << tmp;
  assert(res.str().size() == d_size);
  free(tmp);
  return res.str();
}

uint64_t
BitVector::to_uint64() const
{
  assert(d_size <= 64);
  return mpz_get_ui(d_val->d_mpz);
}

int32_t
BitVector::compare(const BitVector& other) const
{
  assert(d_size == other.d_size);
  return mpz_cmp(d_val->d_mpz, other.d_val->d_mpz);
}

int32_t
BitVector::signed_compare(const BitVector& other) const
{
  assert(d_size == other.d_size);

  uint32_t msb_a = get_bit(d_size - 1);
  uint32_t msb_b = other.get_bit(d_size - 1);

  if (msb_a && !msb_b)
  {
    return -1;
  }
  if (!msb_a && msb_b)
  {
    return 1;
  }
  return compare(other);
}

bool
BitVector::get_bit(uint32_t idx) const
{
  return mpz_tstbit(d_val->d_mpz, idx);
}

void
BitVector::set_bit(uint32_t idx, bool value)
{
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
  mpz_combit(d_val->d_mpz, idx);
}

bool
BitVector::is_true() const
{
  // TODO
  return false;
}

bool
BitVector::is_false() const
{
  // TODO
  return false;
}

bool
BitVector::is_zero() const
{
  return mpz_cmp_ui(d_val->d_mpz, 0) == 0;
}

bool
BitVector::is_ones() const
{
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
  return mpz_cmp_ui(d_val->d_mpz, 1) == 0;
}

bool
BitVector::is_min_signed() const
{
  if (mpz_scan1(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_max_signed() const
{
  if (mpz_scan0(d_val->d_mpz, 0) != d_size - 1) return false;
  return true;
}

bool
BitVector::is_uadd_overflow(const BitVector& other) const
{
  // TODO
  return false;
}

bool
BitVector::is_umul_overflow(const BitVector& other) const
{
  // TODO
  return false;
}

uint32_t
BitVector::count_trailing_zeros() const
{
  // TODO
  return 0;
}

uint32_t
BitVector::count_leading_zeros() const
{
  // TODO
  return 0;
}

uint32_t
BitVector::count_leading_ones() const
{
  // TODO
  return 0;
}

BitVector
BitVector::bvneg() const
{
  // TODO
}

BitVector
BitVector::bvnot() const
{
  // TODO
}

BitVector
BitVector::bvinc() const
{
  // TODO
}

BitVector
BitVector::bvdec() const
{
  // TODO
}

BitVector
BitVector::bvredand() const
{
  // TODO
}

BitVector
BitVector::bvredor() const
{
  // TODO
}

BitVector
BitVector::bvadd(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsub(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvand(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvimplies(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvnand(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvnor(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvor(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvxnor(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvxor(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bveq(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvne(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvult(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvule(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvugt(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvuge(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvslt(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsle(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsgt(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsge(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvshl(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvshr(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvashr(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvmul(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvudiv(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvurem(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsdiv(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvsrem(const BitVector& other) const
{
  // TODO
}

BitVector
BitVector::bvconcat(const BitVector& other) const
{
  uint32_t size = d_size + other.d_size;
  BitVector res(size);
  mpz_mul_2exp(res.d_val->d_mpz, d_val->d_mpz, other.d_size);
  mpz_add(res.d_val->d_mpz, res.d_val->d_mpz, other.d_val->d_mpz);
  mpz_fdiv_r_2exp(res.d_val->d_mpz, res.d_val->d_mpz, size);
  return res;
}

BitVector
BitVector::bvextract(uint32_t idx_hi, uint32_t idx_lo) const
{
  // TODO
}

BitVector
BitVector::bvzext(uint32_t n) const
{
  // TODO
}

BitVector
BitVector::bvsext(uint32_t n) const
{
  // TODO
}

}  // namespace bzlals
