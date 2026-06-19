/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gmp.h>

#include "rng/rng.h"
#include "test_lib.h"

namespace bzla::test {

TEST(TestRng, copy_assignment)
{
  RNG a(42);
  // Advance a's state so it is non-trivial.
  for (int i = 0; i < 10; ++i)
  {
    (void) a.pick<uint32_t>();
  }

  RNG b(7);
  b = a;  // Copy assignment must deep-copy the GMP randstate.

  // After a correct copy, a and b have independent but identical GMP states,
  // so an independent draw from each yields the same value. The previous
  // implicit (shallow) copy assignment aliased the same GMP state, so the two
  // draws would advance a single shared state and differ.
  mpz_t ra, rb;
  mpz_init(ra);
  mpz_init(rb);
  mpz_urandomb(ra, *a.get_gmp_state(), 64);
  mpz_urandomb(rb, *b.get_gmp_state(), 64);
  ASSERT_EQ(mpz_cmp(ra, rb), 0);
  mpz_clear(ra);
  mpz_clear(rb);

  // The Mersenne-Twister engine state is copied too.
  ASSERT_EQ(a.pick<uint32_t>(), b.pick<uint32_t>());

  // a and b are destroyed independently here; a shallow copy would double free
  // the aliased GMP allocation.
}

TEST(TestRng, self_assignment)
{
  RNG a(123);
  RNG ref(123);  // identical, independent RNG (same seed)
  RNG* alias = &a;
  a          = *alias;  // self-assignment must be a no-op (and not double free)
  ASSERT_EQ(a.pick<uint32_t>(), ref.pick<uint32_t>());
}

}  // namespace bzla::test
