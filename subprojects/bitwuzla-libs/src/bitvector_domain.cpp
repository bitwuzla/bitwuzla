#include "bitvector_domain.h"

#include "gmpmpz.h"

namespace bzlals {

BitVectorDomain::BitVectorDomain(uint32_t size)
{
  // TODO
}

BitVectorDomain::BitVectorDomain(const BitVector &lo, const BitVector &hi)
{
  // TODO
}

BitVectorDomain::BitVectorDomain(const std::string &value)
{
  // TODO
}

BitVectorDomain::BitVectorDomain(const BitVector &bv)
{
  // TODO
}

BitVectorDomain::BitVectorDomain(uint32_t size, uint64_t value)
{
  // TODO
}

BitVectorDomain::BitVectorDomain(const BitVectorDomain &other)
{
  // TODO
}

BitVectorDomain::~BitVectorDomain()
{
  // TODO
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
