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
  /** Copy constructor. */
  RNG(const RNG& other);
  /** Copy assignment. */
  RNG& operator=(const RNG& other);
  /** Destructor. */
  ~RNG();

  /**
   * Pick an integral number with type T.
   *
   * @note The sequence of produced values for a given seed is reproducible
   *       across standard library implementations for types that do not
   *       require narrowing an engine draw since the algorithm for doing so
   *       is unspecified in the standard.
   */
  template <typename T,
            typename std::enable_if<std::is_integral<T>::value, int>::type = 0>
  T pick()
  {
    std::uniform_int_distribution<T> dist;
    return dist(d_rng);
  }

  /**
   * Pick an integral number with type T between 'from' and 'to' (inclusive).
   *
   * @note The sequence of values this produces for a given seed is *not*
   *       reproducible across standard library implementations since the
   *       algorithm of the bounded std::uniform_int_distribution is
   *       unspecified and thus differs across implementations.
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
   * ([from, to), upper bound exclusive). */
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

  /**
   * Get a pointer to the gmp_randstate_t.
   *
   * Seeds the randstate if it has not been seeded yet, and is thus not safe to
   * call concurrently on a shared RNG. Note that this was never safe: the
   * returned randstate is advanced by GMP on every draw.
   */
  gmp_randstate_t* get_gmp_state()
  {
    if (!d_gmp_seeded) seed_gmp_state();
    return &d_gmp_randstate;
  }

 private:
  /**
   * Seed the GMP randstate.
   *
   * This is deferred until the randstate is first used to avoid seeding when
   * no GMP RNG engine draws are needed (GMP RNG seeding is costly).
   *
   * @note Lazy seeding is mainly required for unit tests where many
   *       (de)constructions of RNG happen but no GMP RNG draws are necessary.
   */
  void seed_gmp_state();

  /** The seed of the random number generator. */
  uint32_t d_seed;
  /** The underlying RNG Mersenne Twister engine. */
  std::mt19937 d_rng;
  /** The seed for the GMP randstate, applied on first use. */
  uint32_t d_gmp_seed;
  /** True if the GMP randstate has been seeded. */
  bool d_gmp_seeded;
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
