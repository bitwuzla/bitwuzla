/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "rng.h"

#include <cassert>

#define BZLALS_PROB_MAX 1000 /* Maximum probability 100% = 1000. */

namespace bzla {

RNG::RNG(uint32_t seed) : d_seed(seed), d_gmp_seeded(false)
{
  d_rng.seed(d_seed);
  gmp_randinit_mt(d_gmp_randstate);
  // Drawn eagerly, even though the randstate is only seeded on first use, so
  // that the Mersenne Twister stream does not depend on whether or when the
  // randstate is used.
  d_gmp_seed = pick<uint32_t>();
}

RNG::RNG(const RNG& other)
    : d_seed(other.d_seed),
      d_rng(other.d_rng),
      d_gmp_seed(other.d_gmp_seed),
      d_gmp_seeded(other.d_gmp_seeded)
{
  // gmp_randinit_set() duplicates the state of other as it is, seeded or not,
  // so d_gmp_seeded has to be copied along with it.
  gmp_randinit_set(d_gmp_randstate, other.d_gmp_randstate);
}

RNG&
RNG::operator=(const RNG& other)
{
  if (&other == this)
  {
    return *this;
  }
  d_seed       = other.d_seed;
  d_rng        = other.d_rng;
  d_gmp_seed   = other.d_gmp_seed;
  d_gmp_seeded = other.d_gmp_seeded;
  gmp_randclear(d_gmp_randstate);
  gmp_randinit_set(d_gmp_randstate, other.d_gmp_randstate);
  return *this;
}

RNG::~RNG() { gmp_randclear(d_gmp_randstate); }

void
RNG::seed_gmp_state()
{
  assert(!d_gmp_seeded);
  gmp_randseed_ui(d_gmp_randstate, d_gmp_seed);
  d_gmp_seeded = true;
}

bool
RNG::pick_with_prob(uint32_t prob)
{
  assert(prob <= BZLALS_PROB_MAX);
  uint32_t r = pick<uint32_t>(0, BZLALS_PROB_MAX - 1);
  return r < prob;
}

bool
RNG::flip_coin()
{
  return pick_with_prob(500);
}

RNG::Choice
RNG::pick_one_of_three()
{
  uint32_t r = pick<uint32_t>(0, 8);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  assert(r < 9);
  return Choice::THIRD;
}

RNG::Choice
RNG::pick_one_of_four()
{
  uint32_t r = pick<uint32_t>(0, 11);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  if (r < 9) return Choice::THIRD;
  assert(r < 12);
  return Choice::FOURTH;
}

RNG::Choice
RNG::pick_one_of_five()
{
  uint32_t r = pick<uint32_t>(0, 14);
  if (r < 3) return Choice::FIRST;
  if (r < 6) return Choice::SECOND;
  if (r < 9) return Choice::THIRD;
  if (r < 12) return Choice::FOURTH;
  assert(r < 15);
  return Choice::FIFTH;
}

}  // namespace bzla
