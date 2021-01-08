#ifndef BZLALS__WHEEL_FACTORIZER_H
#define BZLALS__WHEEL_FACTORIZER_H

#include <cstdint>

#include "bitvector.h"

namespace bzlals {

/* Wheel factorization for s % x = t with base {2, 3, 5}. */
class WheelFactorizer
{
 public:
  WheelFactorizer(const BitVector& n, uint64_t limit);
  BitVector* next();

 private:
  BitVector d_num;
  BitVector d_fact;
  BitVector d_one;
  BitVector d_two;
  BitVector d_four;
  BitVector d_six;

  BitVector* d_inc[11];

  bool d_done  = false;
  size_t d_pos = 0;
  uint64_t d_limit;
};
}  // namespace bzlals
#endif
