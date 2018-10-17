/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Mathias Preiner.
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlabvprop.h"
}

class TestBvProp : public TestMm
{
};

TEST_F(TestBvProp, valid_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;

  /* check valid */
  lo = bzla_bv_char_to_bv(d_mm, "0101011");
  hi = bzla_bv_char_to_bv(d_mm, "1101011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(bzla_bvprop_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  /* check invalid */
  lo = bzla_bv_char_to_bv(d_mm, "1101011");
  hi = bzla_bv_char_to_bv(d_mm, "0101011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(!bzla_bvprop_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);
}

TEST_F(TestBvProp, fixed_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;

  /* check fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001111");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(bzla_bvprop_is_fixed(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);

  /* check not fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001011");
  d  = bzla_bvprop_new(d_mm, lo, hi);

  assert(!bzla_bvprop_is_fixed(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvprop_free(d_mm, d);
}

TEST_F(TestBvProp, init_domain)
{
  BzlaBvDomain *d = bzla_bvprop_new_init(d_mm, 32);
  assert(bzla_bvprop_is_valid(d_mm, d));
  assert(!bzla_bvprop_is_fixed(d_mm, d));
  bzla_bvprop_free(d_mm, d);
}
