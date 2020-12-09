#include "bitvector_domain.h"

#include <algorithm>
#include <cassert>

#include "gmpmpz.h"

namespace bzlals {

BitVectorDomain::BitVectorDomain(uint32_t size)
    : d_lo(BitVector::mk_zero(size)), d_hi(BitVector::mk_ones(size))
{
}

BitVectorDomain::BitVectorDomain(const BitVector &lo, const BitVector &hi)
    : d_lo(lo), d_hi(hi)
{
  assert(lo.get_size() == hi.get_size());
}

BitVectorDomain::BitVectorDomain(const std::string &value)
{
  uint32_t size = value.size();
  assert(size > 0);
  std::string lo(value);
  std::string hi(value);
  std::replace(lo.begin(), lo.end(), 'x', '0');
  std::replace(hi.begin(), hi.end(), 'x', '1');
  d_lo = BitVector(size, lo);
  d_hi = BitVector(size, hi);
}

BitVectorDomain::BitVectorDomain(const BitVector &bv) : d_lo(bv), d_hi(bv) {}

BitVectorDomain::BitVectorDomain(uint32_t size, uint64_t value)
    : BitVectorDomain(BitVector(size, value))
{
}

BitVectorDomain::BitVectorDomain(const BitVectorDomain &other)
    : d_lo(other.d_lo), d_hi(other.d_hi)
{
}

BitVectorDomain::~BitVectorDomain()
{
}

uint32_t
BitVectorDomain::get_size() const
{
  assert(d_lo.get_size() == d_hi.get_size());
  return d_lo.get_size();
}

bool
BitVectorDomain::is_valid() const
{
  return d_lo.bvnot().bvor(d_hi).is_ones();
}

bool
BitVectorDomain::is_fixed() const
{
  return d_lo.compare(d_hi) == 0;
}

bool
BitVectorDomain::has_fixed_bits() const
{
  return d_lo.bvxnor(d_hi).bvredor().is_true();
}

bool
BitVectorDomain::is_fixed_bit(uint32_t idx)
{
  assert(idx < get_size());
  return d_lo.get_bit(idx) == d_hi.get_bit(idx);
}

bool
BitVectorDomain::is_fixed_bit_true(uint32_t idx)
{
  assert(idx < get_size());
  bool b = d_lo.get_bit(idx);
  if (!b) return false;
  return b == d_hi.get_bit(idx);
}

bool
BitVectorDomain::is_fixed_bit_false(uint32_t idx)
{
  assert(idx < get_size());
  bool b = d_lo.get_bit(idx);
  if (b) return false;
  return b == d_hi.get_bit(idx);
}

void
BitVectorDomain::fix_bit(uint32_t idx, bool value)
{
  assert(idx < get_size());
  d_lo.set_bit(idx, value);
  d_hi.set_bit(idx, value);
}

bool
BitVectorDomain::match_fixed_bits(const BitVector &bv) const
{
  // TODO
}

bool
BitVectorDomain::operator==(const BitVectorDomain &other) const
{
  return d_lo.compare(other.d_lo) == 0 && d_hi.compare(other.d_hi) == 0;
}

BitVectorDomain
BitVectorDomain::bvnot() const
{
  // TODO
}

BitVectorDomain
BitVectorDomain::bvshl(const BitVector &shift) const
{
  // TODO
}

BitVectorDomain
BitVectorDomain::bvextract(uint32_t idx_hi, uint32_t idx_lo) const
{
  // TODO
}

std::string
BitVectorDomain::to_string() const
{
  // TODO
}

}  // namespace bzlals
