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

RNG::RNG(uint32_t seed) : d_seed(seed)
{
  d_rng.seed(d_seed);
  gmp_randinit_mt(d_gmp_randstate);
  gmp_randseed_ui(d_gmp_randstate, pick<uint32_t>());
}

RNG::RNG(const RNG& other) : d_rng(other.d_rng)
{
  gmp_randinit_set(d_gmp_randstate, other.d_gmp_randstate);
}

RNG::~RNG() { gmp_randclear(d_gmp_randstate); }

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
