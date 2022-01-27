/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlarng.h"

#include <assert.h>
#include <limits.h>

#include "bzlaopt.h"
#ifndef NDEBUG
#include <float.h>
#endif
#include <gmp.h>
#include <stdint.h>

BzlaRNG*
bzla_rng_new(BzlaMemMgr* mm, uint32_t seed)
{
  assert(mm);
  BzlaRNG* res;

  BZLA_CNEW(mm, res);
  res->mm   = mm;
  res->seed = seed;
  bzla_rng_init(res, seed);
  return res;
}

void
bzla_rng_init(BzlaRNG* rng, uint32_t seed)
{
  assert(rng);
  assert(rng->mm);

  rng->seed = seed;
  rng->w    = seed;
  rng->z    = ~rng->w;
  rng->w <<= 1;
  rng->z <<= 1;
  rng->w += 1;
  rng->z += 1;
  rng->w *= 2019164533u;
  rng->z *= 1000632769u;

  if (rng->is_init)
  {
    assert(rng->gmp_state);
    gmp_randclear(*((gmp_randstate_t*) rng->gmp_state));
  }
  else
  {
    rng->gmp_state = bzla_mem_malloc(rng->mm, sizeof(gmp_randstate_t));
  }
  rng->is_init = true;
  gmp_randinit_mt(*((gmp_randstate_t*) rng->gmp_state));
  gmp_randseed_ui(*((gmp_randstate_t*) rng->gmp_state), bzla_rng_rand(rng));
}

BzlaRNG*
bzla_rng_clone(BzlaRNG* rng, BzlaMemMgr* mm)
{
  assert(mm);
  BzlaRNG* res;
  res = bzla_rng_new(mm, rng->seed);
  return res;
}

void
bzla_rng_delete(BzlaRNG* rng)
{
  (void) rng;
  assert(rng->gmp_state);
  gmp_randclear(*((gmp_randstate_t*) rng->gmp_state));
  bzla_mem_free(rng->mm, rng->gmp_state, sizeof(gmp_randstate_t));
  rng->gmp_state = 0;
  rng->is_init   = false;
  BZLA_DELETE(rng->mm, rng);
}

uint32_t
bzla_rng_rand(BzlaRNG* rng)
{
  assert(rng);
  rng->z = 36969 * (rng->z & 65535) + (rng->z >> 16);
  rng->w = 18000 * (rng->w & 65535) + (rng->w >> 16);
  return (rng->z << 16) + rng->w; /* 32-bit result */
}

uint32_t
bzla_rng_pick_rand(BzlaRNG* rng, uint32_t from, uint32_t to)
{
  assert(rng);
  assert(from <= to);

  uint32_t res;

  from = from == UINT32_MAX ? UINT32_MAX - 1 : from;
  to   = to == UINT32_MAX ? UINT32_MAX - 1 : to;
  res  = bzla_rng_rand(rng);
  res %= to - from + 1;
  res += from;
  return res;
}

double
bzla_rng_pick_rand_dbl(BzlaRNG* rng, double from, double to)
{
  assert(rng);
  assert(from <= to && to < DBL_MAX);

  double res;

  res = (double) bzla_rng_rand(rng) / UINT32_MAX;
  res = from + res * (to - from);
  return res;
}

bool
bzla_rng_pick_with_prob(BzlaRNG* rng, uint32_t prob)
{
  assert(rng);
  assert(prob <= BZLA_PROB_100);

  uint32_t r;

  r = bzla_rng_pick_rand(rng, 0, BZLA_PROB_100 - 1);
  return r < prob;
}

bool
bzla_rng_flip_coin(BzlaRNG* rng)
{
  return bzla_rng_pick_with_prob(rng, BZLA_PROB_50);
}
