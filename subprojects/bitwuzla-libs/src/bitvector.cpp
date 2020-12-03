#include "bitvector.h"

namespace bzlals {

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
  // TODO
}

// BitVector::BitVector(uint32_t size, RNG& rng){}
// BitVector::BitVector(uint32_t size, RNG& rng, const BitVector& from, const
// BitVector& to, bool is_signed = false){} BitVector::BitVector(uint32_t size,
// RNG& rng, uint32_t idx_hi, uint32_t idx_lo){}

BitVector::BitVector(uint32_t size, const std::string& bin_str) : d_size(size)
{
  // TODO
}

BitVector::BitVector(uint32_t size, uint64_t value) : d_size(size)
{
  // TODO
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
  // TODO
  return "";
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
