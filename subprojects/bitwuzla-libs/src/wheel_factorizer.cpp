#include "wheel_factorizer.h"

#include "gmpmpz.h"

namespace bzlals {

WheelFactorizer::WheelFactorizer(const BitVector& n, uint64_t limit)
    : d_num(n), d_limit(limit)
{
  uint32_t bw = n.size();
  d_one       = BitVector(bw, 1);
  d_two       = BitVector(bw, 2);
  d_four      = BitVector(bw, 4);
  d_six       = BitVector(bw, 6);
  d_fact      = d_two;
  d_inc[0]    = &d_one;
  d_inc[1]    = &d_two;
  d_inc[2]    = &d_two;
  d_inc[3]    = &d_four;
  d_inc[4]    = &d_two;
  d_inc[5]    = &d_four;
  d_inc[6]    = &d_two;
  d_inc[7]    = &d_four;
  d_inc[8]    = &d_six;
  d_inc[9]    = &d_two;
  d_inc[10]   = &d_six;
}

BitVector*
WheelFactorizer::next()
{
  if (d_done) return nullptr;

  uint64_t num_iterations = 0;

  while (true)
  {
    ++num_iterations;
    if (d_limit && num_iterations > d_limit)
    {
      d_done = true;
      break;
    }

    /* sqrt(n) is the maximum factor. */
    if (d_fact.is_umul_overflow(d_fact)
        || d_fact.bvmul(d_fact).compare(d_num) > 0)
    {
      d_done = true;
      return &d_num;
    }

    BitVector quot, rem;
    d_num.bvudivurem(d_fact, &quot, &rem);
    if (rem.is_zero())
    {
      /* found factor */
      d_num.iset(quot);
      return &d_fact;
    }
    BitVector tmp = d_fact.bvadd(*d_inc[d_pos]);
    bool done     = tmp.compare(d_fact) <= 0;
    d_fact.iset(tmp);
    d_pos = d_pos == 10 ? 3 : d_pos + 1;
    if (done)
    {
      d_done = true;
      break;
    }
  }
  return nullptr;
}

}  // namespace bzlals
