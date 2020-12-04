#include "bitvector.h"

#include <gmpxx.h>

#include <cassert>
#include <sstream>

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

struct BzlalsMPZ
{
  /** Construct a zero-initialized GMP value. */
  BzlalsMPZ() { mpz_init(d_mpz_t); }
  /** Construct a GMP value from given binary string. */
  BzlalsMPZ(const std::string& value)
  {
    mpz_init_set_str(d_mpz_t, value.c_str(), 2);
  }
  /** Construct a GMP value from given uint64 value. */
  BzlalsMPZ(uint64_t size, uint64_t value)
  {
    mpz_init_set_ui(d_mpz_t, value);
    mpz_fdiv_r_2exp(d_mpz_t, d_mpz_t, size);
  }

  /** Destructor. */
  ~BzlalsMPZ() { mpz_clear(d_mpz_t); }

  /** The GMP integer value. */
  mpz_t d_mpz_t;
};

BitVector
BitVector::mk_zero(uint32_t size)
{
  // TODO
}

BitVector
BitVector::mk_one(uint32_t size)
{
  // TODO
}

BitVector
BitVector::mk_ones(uint32_t size)
{
  // TODO
}

BitVector
BitVector::mk_min_signed(uint32_t size)
{
  // TODO
}

BitVector
BitVector::mk_max_signed(uint32_t size)
{
  // TODO
}

BitVector
BitVector::bvite(const BitVector& c, const BitVector& t, const BitVector& e)
{
  // TODO
}

BitVector::BitVector(uint32_t size) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new BzlalsMPZ());
}

// BitVector::BitVector(uint32_t size, RNG& rng){}
// BitVector::BitVector(uint32_t size, RNG& rng, const BitVector& from, const
// BitVector& to, bool is_signed = false){} BitVector::BitVector(uint32_t size,
// RNG& rng, uint32_t idx_hi, uint32_t idx_lo){}

BitVector::BitVector(uint32_t size, const std::string& str) : d_size(size)
{
  assert(str.size() <= size);
  assert(is_bin_str(str));
  d_val.reset(new BzlalsMPZ(str));
}

BitVector::BitVector(uint32_t size, uint64_t value) : d_size(size)
{
  assert(size > 0);
  d_val.reset(new BzlalsMPZ(size, value));
}

// should this deep copy by default? or do we need an extra copy for
// this?
BitVector::BitVector(BitVector& other)
{
  // TODO
}

BitVector::~BitVector()
{
  // TODO
}

std::string
BitVector::to_string() const
{
  std::stringstream res;
  char* tmp     = mpz_get_str(0, 2, d_val->d_mpz_t);
  uint32_t n    = strlen(tmp);
  uint32_t diff = d_size - n;
  assert(n <= d_size);
  res << std::string(diff, '0') << tmp;
  assert(res.str().size() == d_size);
  free(tmp);
  return res.str();
}

int32_t
BitVector::compare(const BitVector& other) const
{
  // TODO
  return 0;
}

int32_t
BitVector::signed_compare(const BitVector& other) const
{
  // TODO
  return 0;
}

bool
BitVector::get_bit(uint32_t idx) const
{
  // TODO
  return false;
}

void
BitVector::set_bit(uint32_t idx, bool value)
{
  // TODO
}

void
BitVector::flip_bit(uint32_t idx)
{
  // TODO
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
  // TODO
  return false;
}

bool
BitVector::is_ones() const
{
  // TODO
  return false;
}

bool
BitVector::is_one() const
{
  // TODO
  return false;
}

bool
BitVector::is_min_signed() const
{
  // TODO
  return false;
}

bool
BitVector::is_max_signed() const
{
  // TODO
  return false;
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
  // TODO
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
