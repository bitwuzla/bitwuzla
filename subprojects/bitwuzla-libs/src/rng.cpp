#include "rng.h"

#include <gmpxx.h>

#include <cassert>

#include "gmprandstate.h"

#define BZLALS_PROB_MAX 1000 /* Maximum probability 100% = 1000. */

namespace bzla {

RNG::RNG(uint32_t seed) : d_seed(seed)
{
  d_rng.seed(seed);
  d_gmp_state.reset(new GMPRandState(pick<uint32_t>()));
}

RNG::~RNG() {}

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
