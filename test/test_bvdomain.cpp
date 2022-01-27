/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#include <bitset>

#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "bzlabvdomain.h"
}

class TestBvDomain : public TestBvDomainCommon
{
 protected:
  void test_check_fixed_bits(const char *d_val)
  {
    assert(strlen(d_val) == 3);
    BzlaBvDomain *d = bzla_bvdomain_new_from_char(d_mm, d_val);
    for (uint32_t i = 0; i < (1u << 3); ++i)
    {
      std::string bv_val = std::bitset<3>(i).to_string();
      BzlaBitVector *bv  = bzla_bv_char_to_bv(d_mm, bv_val.c_str());
      bool expected      = true;
      for (uint32_t j = 0; j < 3; ++j)
      {
        if ((bzla_bvdomain_is_fixed_bit_false(d, j) && bv_val[2 - j] != '0')
            || (bzla_bvdomain_is_fixed_bit_true(d, j) && bv_val[2 - j] != '1'))
        {
          expected = false;
        }
      }
      ASSERT_EQ(bzla_bvdomain_check_fixed_bits(d_mm, d, bv), expected);
      bzla_bv_free(d_mm, bv);
    }
    bzla_bvdomain_free(d_mm, d);
  }
};

TEST_F(TestBvDomain, valid_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;

  /* check valid */
  lo = bzla_bv_char_to_bv(d_mm, "0101011");
  hi = bzla_bv_char_to_bv(d_mm, "1101011");
  d  = bzla_bvdomain_new(d_mm, lo, hi);

  ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvdomain_free(d_mm, d);

  /* check invalid */
  lo = bzla_bv_char_to_bv(d_mm, "1101011");
  hi = bzla_bv_char_to_bv(d_mm, "0101011");
  d  = bzla_bvdomain_new(d_mm, lo, hi);

  ASSERT_FALSE(bzla_bvdomain_is_valid(d_mm, d));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvdomain_free(d_mm, d);
}

TEST_F(TestBvDomain, fixed_domain)
{
  BzlaBitVector *lo, *hi;
  BzlaBvDomain *d;
  uint32_t i;

  /* check fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001111");
  d  = bzla_bvdomain_new(d_mm, lo, hi);
  ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_TRUE(bzla_bvdomain_is_fixed_bit(d, i));
  }
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 6));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 5));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 4));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 3));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 2));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 1));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 0));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvdomain_free(d_mm, d);

  d = bzla_bvdomain_new_init(d_mm, 7);
  ASSERT_FALSE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_FALSE(bzla_bvdomain_is_fixed_bit(d, i));
  }
  bzla_bvdomain_fix_bit(d, 0, false);
  bzla_bvdomain_fix_bit(d, 1, false);
  bzla_bvdomain_fix_bit(d, 2, false);
  bzla_bvdomain_fix_bit(d, 3, true);
  bzla_bvdomain_fix_bit(d, 4, true);
  bzla_bvdomain_fix_bit(d, 5, true);
  bzla_bvdomain_fix_bit(d, 6, true);
  ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_TRUE(bzla_bvdomain_is_fixed_bit(d, i));
  }
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 0));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 1));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 2));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 3));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 4));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 5));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 6));
  bzla_bvdomain_free(d_mm, d);

  /* check not fixed */
  lo = bzla_bv_char_to_bv(d_mm, "0001111");
  hi = bzla_bv_char_to_bv(d_mm, "0001011");
  d  = bzla_bvdomain_new(d_mm, lo, hi);
  ASSERT_FALSE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_TRUE(i == 2 || bzla_bvdomain_is_fixed_bit(d, i));
  }
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 6));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 5));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 4));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 3));
  ASSERT_FALSE(bzla_bvdomain_is_fixed_bit(d, 2));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 1));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 0));
  bzla_bv_free(d_mm, lo);
  bzla_bv_free(d_mm, hi);
  bzla_bvdomain_free(d_mm, d);

  d = bzla_bvdomain_new_init(d_mm, 7);
  ASSERT_FALSE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_FALSE(bzla_bvdomain_is_fixed_bit(d, i));
  }
  bzla_bvdomain_fix_bit(d, 0, false);
  bzla_bvdomain_fix_bit(d, 1, false);
  bzla_bvdomain_fix_bit(d, 2, false);
  bzla_bvdomain_fix_bit(d, 3, true);
  bzla_bvdomain_fix_bit(d, 5, true);
  bzla_bvdomain_fix_bit(d, 6, true);
  ASSERT_FALSE(bzla_bvdomain_is_fixed(d_mm, d));
  for (i = 0; i < bzla_bvdomain_get_width(d); i++)
  {
    ASSERT_TRUE(i == 4 || bzla_bvdomain_is_fixed_bit(d, i));
  }
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 0));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 1));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_false(d, 2));
  ASSERT_FALSE(bzla_bvdomain_is_fixed_bit(d, 4));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 3));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 5));
  ASSERT_TRUE(bzla_bvdomain_is_fixed_bit_true(d, 6));
  bzla_bvdomain_free(d_mm, d);
}

TEST_F(TestBvDomain, new_init_domain)
{
  BzlaBvDomain *d = bzla_bvdomain_new_init(d_mm, 32);
  ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, d));
  ASSERT_FALSE(bzla_bvdomain_is_fixed(d_mm, d));
  bzla_bvdomain_free(d_mm, d);
}

TEST_F(TestBvDomain, new_fixed)
{
  BzlaBitVector *bv = bzla_bv_uint64_to_bv(d_mm, 128, 32);
  BzlaBvDomain *d   = bzla_bvdomain_new_fixed(d_mm, bv);
  ASSERT_TRUE(bzla_bvdomain_is_valid(d_mm, d));
  ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d));
  ASSERT_EQ(bzla_bv_compare(bv, d->lo), 0);
  ASSERT_EQ(bzla_bv_compare(bv, d->hi), 0);
  bzla_bvdomain_free(d_mm, d);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBvDomain, check_fixed_bits)
{
  for (uint32_t i = 0; i < 3; ++i)
  {
    for (uint32_t j = 0; j < 3; ++j)
    {
      for (uint32_t k = 0; k < 3; ++k)
      {
        std::stringstream ss;
        ss << (i == 0 ? '0' : (i == 1 ? '1' : 'x'))
           << (j == 0 ? '0' : (j == 1 ? '1' : 'x'))
           << (k == 0 ? '0' : (k == 1 ? '1' : 'x'));
        test_check_fixed_bits(ss.str().c_str());
      }
    }
  }
}

TEST_F(TestBvDomain, slice)
{
  std::vector<std::string> consts;

  TestPropCommon::gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BzlaBvDomain *d = bzla_bvdomain_new_from_char(d_mm, c.c_str());
        BzlaBvDomain *s = bzla_bvdomain_slice(d_mm, d, i, j);
        char *dlo       = bzla_bv_to_char(d_mm, d->lo);
        char *dhi       = bzla_bv_to_char(d_mm, d->hi);
        char *slo       = bzla_bv_to_char(d_mm, s->lo);
        char *shi       = bzla_bv_to_char(d_mm, s->hi);
        ASSERT_EQ(strncmp(dlo + 2 - i, slo, i - j + 1), 0);
        bzla_mem_freestr(d_mm, dlo);
        bzla_mem_freestr(d_mm, dhi);
        bzla_mem_freestr(d_mm, slo);
        bzla_mem_freestr(d_mm, shi);
        bzla_bvdomain_free(d_mm, d);
        bzla_bvdomain_free(d_mm, s);
      }
    }
  }
}
