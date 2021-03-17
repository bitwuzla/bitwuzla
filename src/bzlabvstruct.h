#ifndef BZLABVSTRUCT_H_INCLUDED
#define BZLABVSTRUCT_H_INCLUDED

#include <stdint.h>

#ifdef BZLA_USE_GMP
#include <gmp.h>
#endif

#define BZLA_BV_TYPE uint32_t
#define BZLA_BV_TYPE_BW (sizeof(BZLA_BV_TYPE) * 8)

struct BzlaBitVector
{
  uint32_t width; /* length of bit vector */
#ifdef BZLA_USE_GMP
  mpz_t val;
#else
  uint32_t len; /* length of 'bits' array */

  /* 'bits' represents the bit vector in 32-bit chunks, first bit of 32-bit bv
   * in bits[0] is MSB, bit vector is 'filled' from LSB, hence spare bits (if
   * any) come in front of the MSB and are zeroed out.
   * E.g., for a bit vector of width 31, representing value 1:
   *
   *    bits[0] = 0 0000....1
   *              ^ ^--- MSB
   *              |--- spare bit
   * */
  BZLA_BV_TYPE bits[];
#endif
};

#endif
