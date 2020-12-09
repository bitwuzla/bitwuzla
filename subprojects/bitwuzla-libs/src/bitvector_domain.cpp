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
  // TODO
}

bool
BitVectorDomain::is_valid() const
{
  // TODO
}

bool
BitVectorDomain::is_fixed() const
{
  // TODO
}

bool
BitVectorDomain::has_fixed_bits() const
{
  // TODO
}

bool
BitVectorDomain::is_fixed_bit(uint32_t idx)
{
  // TODO
}

bool
BitVectorDomain::is_fixed_bit_true(uint32_t idx)
{
  // TODO
}

bool
BitVectorDomain::is_fixed_bit_false(uint32_t idx)
{
  // TODO
}

void
BitVectorDomain::fix_bit(uint32_t idx, bool value)
{
  // TODO
}

bool
BitVectorDomain::match_fixed_bits(const BitVector &bv) const
{
  // TODO
}

bool
BitVectorDomain::operator==(const BitVectorDomain &other) const
{
  // TODO
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
