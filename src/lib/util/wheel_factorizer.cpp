/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "wheel_factorizer.h"

namespace bzla {
namespace ls {

WheelFactorizer::WheelFactorizer(const BitVector& n, uint64_t limit)
    : d_num(n), d_limit(limit)
{
  uint64_t bw = n.size();

  // nothing to do for size 1
  d_done = bw == 1;

  // size 2 needs special handling and doesn't utilize the wheel
  if (bw > 2)
  {
    d_one     = BitVector::from_ui(bw, 1);
    d_two     = BitVector::from_ui(bw, 2);
    d_four    = BitVector::from_ui(bw, 4);
    d_six     = BitVector::from_ui(bw, 6);
    d_fact    = d_two;
    d_inc[0]  = &d_one;
    d_inc[1]  = &d_two;
    d_inc[2]  = &d_two;
    d_inc[3]  = &d_four;
    d_inc[4]  = &d_two;
    d_inc[5]  = &d_four;
    d_inc[6]  = &d_two;
    d_inc[7]  = &d_four;
    d_inc[8]  = &d_six;
    d_inc[9]  = &d_two;
    d_inc[10] = &d_six;
  }
}

const BitVector*
WheelFactorizer::next()
{
  if (d_done) return nullptr;

  if (d_num.size() == 2)
  {
    d_done = true;
    if (d_num.is_zero() || d_num.is_one())
    {
      return nullptr;
    }
    return &d_num;
  }

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

}  // namespace ls
}  // namespace bzla
