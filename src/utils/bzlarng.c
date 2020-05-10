/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/bzlarng.h"

#include <assert.h>
#include <limits.h>

#include "bzlaopt.h"
#ifndef NDEBUG
#include <float.h>
#endif
#ifdef BZLA_USE_GMP
#include <gmp.h>
#endif
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

#ifdef BZLA_USE_GMP
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
#endif
}

BzlaRNG*
bzla_rng_clone(BzlaRNG* rng, BzlaMemMgr* mm)
{
  assert(mm);
  BzlaRNG* res;
#ifndef BZLA_USE_GMP
  res = bzla_rng_new(mm, rng->seed);
#else
  assert(rng->gmp_state);
  BZLA_CNEW(mm, res);
  res->mm        = mm;
  res->seed      = rng->seed;
  res->gmp_state = bzla_mem_malloc(res->mm, sizeof(gmp_randstate_t));
  gmp_randinit_set(*((gmp_randstate_t*) res->gmp_state),
                   *((gmp_randstate_t*) rng->gmp_state));
  rng->is_init = true;
#endif
  return res;
}

void
bzla_rng_delete(BzlaRNG* rng)
{
  (void) rng;
#ifdef BZLA_USE_GMP
  assert(rng->gmp_state);
  gmp_randclear(*((gmp_randstate_t*) rng->gmp_state));
  bzla_mem_free(rng->mm, rng->gmp_state, sizeof(gmp_randstate_t));
  rng->gmp_state = 0;
  rng->is_init   = false;
#endif
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
