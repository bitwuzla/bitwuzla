#ifndef BZLALS__RNG_H
#define BZLALS__RNG_H

#include <cstdint>
#include <memory>
#include <random>

namespace bzlals {

struct GMPRandState;

class RNG
{
  friend class BitVector;

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

  /* Pick random element from given set/vector. */
  template <typename TSet, typename TPicked>
  TPicked pick_from_set(const TSet& data);

 private:
  /** The seed of the random number generator. */
  uint32_t d_seed;
  /** The underlying RNG Mersenne Twister engine. */
  std::mt19937 d_rng;
  /** The GMP randstate. */
  std::unique_ptr<GMPRandState> d_gmp_state;
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

}  // namespace bzlals

#endif
