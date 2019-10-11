/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

class TestFp : public TestBoolector
{
};

TEST_F(TestFp, sort_fp)
{
  BoolectorSort f16, f32, f64, f128;

  f16 = boolector_fp_sort(d_bzla, 5, 11);
  assert(boolector_is_fp_sort(d_bzla, f16));

  f32 = boolector_fp_sort(d_bzla, 8, 24);
  assert(boolector_is_fp_sort(d_bzla, f32));

  f64 = boolector_fp_sort(d_bzla, 11, 53);
  assert(boolector_is_fp_sort(d_bzla, f64));

  f128 = boolector_fp_sort(d_bzla, 15, 113);
  assert(boolector_is_fp_sort(d_bzla, f128));

  boolector_release_sort(d_bzla, f16);
  boolector_release_sort(d_bzla, f32);
  boolector_release_sort(d_bzla, f64);
  boolector_release_sort(d_bzla, f128);
}

TEST_F(TestFp, sort_rm)
{
  BoolectorSort rm;

  rm = boolector_rm_sort(d_bzla);
  assert(boolector_is_rm_sort(d_bzla, rm));

  boolector_release_sort(d_bzla, rm);
}
