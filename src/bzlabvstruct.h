#ifndef BZLABVSTRUCT_H_INCLUDED
#define BZLABVSTRUCT_H_INCLUDED

#include <stdint.h>
#include <gmp.h>

struct BzlaBitVector
{
  uint32_t width; /* length of bit vector */
  mpz_t val;
};

#endif
