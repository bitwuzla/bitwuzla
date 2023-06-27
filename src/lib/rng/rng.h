/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA__RNG_RNG_H
#define BZLA__RNG_RNG_H

#include <gmpxx.h>

#include <cassert>
#include <cstdint>
#include <memory>
#include <random>

namespace bzla {

class RNG
{
 public:
  /**
   * The values for the selected choice when picking from multiple choices,
   * see, e.g., pick_one_of_three().
   */
  enum Choice
  {
    FIRST,
    SECOND,
    THIRD,
    FOURTH,
    FIFTH,
  };

  /** Constructor. */
  explicit RNG(uint32_t seed = 0);
  RNG(const RNG& other);
  /** Destructor. */
  ~RNG();

  /** Pick an integral number with type T. */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_int_distribution<T> dist;
    return dist(d_rng);
  }

  /**
   * Pick an integral number with type T between 'from' and 'to' (inclusive).
   */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    std::uniform_int_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /** Pick a floating point number with type T. */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_real_distribution<T> dist;
    return dist(d_rng);
  }

  /** Pick a floating point number with type T between 'from' and 'to'
   * (inclusive). */
  template <
      typename T,
      typename std::enable_if<std::is_floating_point<T>::value, int>::type = 0>
  T pick(T from, T to)
  {
    std::uniform_real_distribution<T> dist(from, to);
    return dist(d_rng);
  }

  /** Pick with given probability, 100% = 1000. */
  bool pick_with_prob(uint32_t prob);
  /** Pick with probability of 50%. */
  bool flip_coin();
  /** Pick one out of three choices. */
  Choice pick_one_of_three();
  /** Pick one out of four choices. */
  Choice pick_one_of_four();
  /** Pick one out of five choices. */
  Choice pick_one_of_five();

  /** Pick random element from given set/vector. */
  template <typename TSet, typename TPicked>
  TPicked pick_from_set(const TSet& data);

  /** Get a pointer to the gmp_randstate_t. */
  gmp_randstate_t* get_gmp_state() { return &d_gmp_randstate; }

 private:
  /** The seed of the random number generator. */
  uint32_t d_seed;
  /** The underlying RNG Mersenne Twister engine. */
  std::mt19937 d_rng;
  /** The GMP randstate. */
  gmp_randstate_t d_gmp_randstate;
};

template <typename TSet, typename TPicked>
TPicked
RNG::pick_from_set(const TSet& set)
{
  assert(!set.empty());
  auto it = set.begin();
  std::advance(it, pick<uint32_t>() % set.size());
  return *it;
}

}  // namespace bzla

#endif
