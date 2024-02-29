/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__BV_BITVECTOR_BOUNDS_H
#define BZLA__BV_BITVECTOR_BOUNDS_H

#include "bv/bitvector.h"
#include "bv/domain/bitvector_domain.h"

namespace bzla {

/* -------------------------------------------------------------------------- */

struct BitVectorRange
{
  /**
   * Default constructor. Empty range.
   */
  BitVectorRange() {}
  /**
   * Constructor.
   * @param min The min value of the range.
   * @param max The max value of the range.
   * @note Range may be invalid, i.e., min > max, we explicitly allow this.
   */
  BitVectorRange(const BitVector& min, const BitVector& max);
  /**
   * Construct a bit-vector range from a domain.
   * @param d The domain.
   */
  BitVectorRange(const BitVectorDomain& d);

  /** @return True if range is empty. */
  bool empty() const;
  /**
   * @return True if this bounds range is valid.
   */
  bool valid() const;
  /** @return The bit-vector size of this range. */
  uint64_t size() const;

  /** Set range to empty. */
  void set_empty();

  /**
   * Get a string representation of this bit-vector range.
   */
  std::string str() const;

  /** The min value of the range. */
  BitVector d_min;
  /** The max value of the range. */
  BitVector d_max;
};

/**
 * Equality comparison operator.
 * @param a The first range.
 * @param b The second range.
 * @return True if the given ranges are equal.
 */
bool operator==(const BitVectorRange& a, const BitVectorRange& b);

/**
 * Serialize a bit-vector range to the given output stream.
 * @param out The output stream.
 * @param r   The bit-vector range.
 * @return The output stream.
 */
std::ostream& operator<<(std::ostream& out, const BitVectorRange& r);

/* -------------------------------------------------------------------------- */

/**
 * The representation of lower and upper range bounds. Null BitVectors for
 * both min/max in the lower and/or upper range if no values in that range
 * are covered.
 *
 * Lower range is given as `[d_lo.min, d_lo.max]` and is a range within
 * [0, max_signed]. Upper range is given as `[d_hi.max, d_hi.max]` and is a
 * range within [min_signed, ones]. Ranges must be valid, i.e., `d_lo.min <=
 * d_lo.max` and `d_hi.min<= d_hi.max`. Null bit-vectors for both values in a
 * range indicate an empty range, i.e., no values in that range are possible.
 *
 */
struct BitVectorBounds
{
  /**
   * Default constructor. Empty bounds.
   */
  BitVectorBounds() {}
  /**
   * Constructor.
   * @param lo The lower range (empty or msb must be fixed to 0).
   * @param hi The upper range (empty or msb must be fixed to 1).
   */
  BitVectorBounds(const BitVectorRange& lo, const BitVectorRange& hi);
  /**
   * @return True if this bounds range is empty.
   */
  bool empty() const;
  /** Set lower range to empty. */
  void set_lo_empty();
  /** Set upper range to empty. */
  void set_hi_empty();
  /**
   * @return True if this bounds range is valid.
   */
  bool valid() const;
  /**
   * @return True if these bounds contain values in the lower range.
   */
  bool has_lo() const;
  /**
   * @return True if these bounds contain values in the upper range.
   */
  bool has_hi() const;

  /**
   * Determine if given BitVector is within either the lower or upper range.
   *
   * @param bv     The bit-vector.
   * @return True if given bit-vector is within any of the ranges.
   */
  bool contains(const BitVector& bv) const;
  /**
   * @return True if given bit-vector is within the lower bounds range.
   */
  bool lo_contains(const BitVector& bv) const;
  /**
   * @return True if given bit-vector is within the upper bounds range.
   */
  bool hi_contains(const BitVector& bv) const;

  /**
   * The lower range (in [0, max_signed]).
   * Nullary if empty.
   */
  BitVectorRange d_lo;
  /**
   * The upper range (in [min_signed, ones]).
   * Nullary if empty.
   */
  BitVectorRange d_hi;
};

/* -------------------------------------------------------------------------- */

}  // namespace bzla

#endif
