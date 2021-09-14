/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <cassert>
#include <memory>

#include "gmprandstate.h"
#include "rng.h"

extern "C" {
#include "bzlaopt.h"
#include "utils/bzlarng.h"
}

struct BzlaRNG
{
  BzlaMemMgr* mm;
  std::unique_ptr<bzla::RNG> d_rng;
};

BzlaRNG*
bzla_rng_new(BzlaMemMgr* mm, uint32_t seed)
{
  assert(mm);
  BzlaRNG* res;

  BZLA_CNEW(mm, res);
  res->mm = mm;
  res->d_rng.reset(new bzla::RNG(seed));
  return res;
}

void
bzla_rng_init(BzlaRNG* rng, uint32_t seed)
{
  assert(rng);
  rng->d_rng.reset(new bzla::RNG(seed));
}

BzlaRNG*
bzla_rng_clone(BzlaRNG* rng, BzlaMemMgr* mm)
{
  assert(rng);
  assert(mm);
  BzlaRNG* res;
  BZLA_CNEW(mm, res);
  res->mm = mm;
  res->d_rng.reset(new bzla::RNG(*rng->d_rng.get()));
  return res;
}

void*
bzla_rng_get_gmp_state(BzlaRNG* rng)
{
  assert(rng);
  return rng->d_rng->get_gmp_state();
}

void
bzla_rng_delete(BzlaRNG* rng)
{
  assert(rng);
  rng->d_rng.reset(nullptr);
  BzlaMemMgr* mm = rng->mm;
  BZLA_DELETE(mm, rng);
}

uint32_t
bzla_rng_rand(BzlaRNG* rng)
{
  assert(rng);
  return rng->d_rng->pick<uint32_t>();
}

uint32_t
bzla_rng_pick_rand(BzlaRNG* rng, uint32_t from, uint32_t to)
{
  assert(rng);
  return rng->d_rng->pick<uint32_t>(from, to);
}

double
bzla_rng_pick_rand_dbl(BzlaRNG* rng, double from, double to)
{
  assert(rng);
  return rng->d_rng->pick<double>(from, to);
}

bool
bzla_rng_pick_with_prob(BzlaRNG* rng, uint32_t prob)
{
  assert(rng);
  assert(prob <= BZLA_PROB_100);
  return rng->d_rng->pick_with_prob(prob);
}

bool
bzla_rng_flip_coin(BzlaRNG* rng)
{
  return bzla_rng_pick_with_prob(rng, BZLA_PROB_50);
}
