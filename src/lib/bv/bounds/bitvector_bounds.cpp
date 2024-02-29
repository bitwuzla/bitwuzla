/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bv/bounds/bitvector_bounds.h"

#include <cassert>
#include <iostream>

namespace bzla {

/*----------------------------------------------------------------------------*/

BitVectorRange::BitVectorRange(const BitVector& min, const BitVector& max)
    : d_min(min), d_max(max)
{
  assert(!min.is_null());
  assert(!max.is_null());
  assert(d_min.size() == d_max.size());
  // Range may be invalid, we explicitly allow this.
}

BitVectorRange::BitVectorRange(const BitVectorDomain& d)
    : d_min(d.lo()), d_max(d.hi())
{
}

bool
BitVectorRange::empty() const
{
  return d_min.is_null() && d_max.is_null();
}

bool
BitVectorRange::valid() const
{
  if (d_min.is_null())
  {
    return d_max.is_null();
  }
  return d_min.compare(d_max) <= 0 || d_min.signed_compare(d_max) <= 0;
}

uint64_t
BitVectorRange::size() const
{
  return d_min.size();
}

void
BitVectorRange::set_empty()
{
  d_min = BitVector();
  d_max = BitVector();
}

std::string
BitVectorRange::str() const
{
  return "[" + d_min.str() + ", " + d_max.str() + "]";
}

bool
operator==(const BitVectorRange& a, const BitVectorRange& b)
{
  return a.d_min == b.d_min && a.d_max == b.d_max;
}

std::ostream&
operator<<(std::ostream& out, const BitVectorRange& r)
{
  out << r.str();
  return out;
}

/*----------------------------------------------------------------------------*/

BitVectorBounds::BitVectorBounds(const BitVectorRange& lo,
                                 const BitVectorRange& hi)
    : d_lo(lo), d_hi(hi)
{
  assert(empty() || valid());
}

bool
BitVectorBounds::empty() const
{
  return !has_lo() && !has_hi();
}

void
BitVectorBounds::set_lo_empty()
{
  d_lo = BitVectorRange();
}

void
BitVectorBounds::set_hi_empty()
{
  d_hi = BitVectorRange();
}

bool
BitVectorBounds::valid() const
{
  return (!has_lo() || (d_lo.valid() && !d_lo.d_min.msb() && !d_lo.d_max.msb()))
         && (!has_hi()
             || (d_hi.valid() && d_hi.d_min.msb() && d_hi.d_max.msb()));
}

bool
BitVectorBounds::has_lo() const
{
  return !d_lo.empty();
}

bool
BitVectorBounds::has_hi() const
{
  return !d_hi.empty();
}

bool
BitVectorBounds::lo_contains(const BitVector& bv) const
{
  return has_lo() && bv.compare(d_lo.d_min) >= 0 && bv.compare(d_lo.d_max) <= 0;
}

bool
BitVectorBounds::hi_contains(const BitVector& bv) const
{
  return has_hi() && bv.compare(d_hi.d_min) >= 0 && bv.compare(d_hi.d_max) <= 0;
}

bool
BitVectorBounds::contains(const BitVector& bv) const
{
  assert(valid());
  return lo_contains(bv) || hi_contains(bv);
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla
