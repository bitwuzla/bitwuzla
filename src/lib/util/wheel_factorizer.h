/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__UTIL_WHEEL_FACTORIZER_H
#define BZLA__UTIL_WHEEL_FACTORIZER_H

#include <cstdint>

#include "bv/bitvector.h"

namespace bzla {
namespace ls {

/* Wheel factorization for s % x = t with base {2, 3, 5}. */
class WheelFactorizer
{
 public:
  /**
   * Constructor.
   * n    : The bit-vector value to factorize.
   * limit: The limit for max number of iterations.
   */
  WheelFactorizer(const BitVector& n, uint64_t limit);
  /**
   * Get next factor.
   * Returns nullptr when no next factor exists.
   */
  const BitVector* next();

 private:
  /**
   * The value to factorize.
   * Updated at each call to next() to d_num / d_fact if d_fact is a factor
   * of d_num, i.e., if d_num % d_fact = 0. */
  BitVector d_num;
  /** The current factor. */
  BitVector d_fact;
  /** Bit-vector value one. */
  BitVector d_one;
  /** Bit-vector value two. */
  BitVector d_two;
  /** Bit-vector value four. */
  BitVector d_four;
  /** Bit-vector value six. */
  BitVector d_six;

  /** The increments applied to d_fact for a {2, 3, 5} wheel. */
  BitVector* d_inc[11];

  bool d_done  = false;
  size_t d_pos = 0;
  uint64_t d_limit;
};
}  // namespace ls
}  // namespace bzla
#endif
