/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
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
