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
 protected:
  static constexpr uint32_t TEST_BW         = 3;
  static constexpr uint32_t TEST_NUM_CONSTS = 27;
  static constexpr uint32_t TEST_CONST_LEN  = (TEST_BW + 1);

  void SetUp() override
  {
    TestMm::SetUp();
    /* Initialize all possible values for 3-valued constants of bit-width
     * TEST_BW. */
    char bit     = '0';
    size_t psize = TEST_NUM_CONSTS;
    for (size_t i = 0; i < TEST_BW; i++)
    {
      psize = psize / 3;
      for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
      {
        d_consts[j][i] = bit;
        if ((j + 1) % psize == 0)
        {
          bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
        }
      }
    }
  }

  /* Create 2-valued bit-vector from 3-valued bit-vector 'bv' by initializing
   * 'x' values to 'bit'. */
  BzlaBitVector *to_bv(const char *c, char bit)
  {
    size_t len = strlen(c);
    char buf[len + 1];
    buf[len] = '\0';
    for (size_t i = 0; i < len; i++)
    {
      buf[i] = (c[i] == 'x') ? bit : c[i];
    }
    return bzla_bv_char_to_bv(d_mm, buf);
  }

  /* Create hi for domain from 3-valued bit-vector 'bv'. */
  BzlaBitVector *to_hi(const char *bv) { return to_bv(bv, '1'); }

  /* Create lo for domain from 3-valued bit-vector 'bv'. */
  BzlaBitVector *to_lo(const char *bv) { return to_bv(bv, '0'); }

  /* Create domain from 3-valued bit-vector 'bv'. */
  BzlaBvDomain *create_domain(const char *bv)
  {
    BzlaBitVector *lo = to_lo(bv);
    BzlaBitVector *hi = to_hi(bv);
    BzlaBvDomain *res = bzla_bvprop_new(d_mm, lo, hi);
    bzla_bv_free(d_mm, lo);
    bzla_bv_free(d_mm, hi);
    return res;
  }

  /* Create 3-valued bit-vector from domain 'd'. */
  char *from_domain(BzlaMemMgr *mm, BzlaBvDomain *d)
  {
    assert(bzla_bvprop_is_valid(mm, d));
    char *lo = bzla_bv_to_char(mm, d->lo);
    char *hi = bzla_bv_to_char(mm, d->hi);

    size_t len = strlen(lo);
    for (size_t i = 0; i < len; i++)
    {
      if (lo[i] != hi[i])
      {
        /* lo[i] == '1' && hi[i] == '0' would be an invalid domain. */
        assert(lo[i] == '0');
        assert(hi[i] == '1');
        lo[i] = 'x';
      }
    }
    bzla_mem_freestr(mm, hi);
    return lo;
  }

  bool check_const_bits(BzlaBvDomain *d, const char *expected)
  {
    assert(bzla_bvprop_is_valid(d_mm, d));
    size_t len = strlen(expected);
    uint32_t bit_lo, bit_hi;
    bool res = true;

    for (size_t i = 0; i < len && res; i++)
    {
      bit_lo = bzla_bv_get_bit(d->lo, len - 1 - i);
      bit_hi = bzla_bv_get_bit(d->hi, len - 1 - i);
      if (expected[i] == 'x')
      {
        res &= bit_lo != bit_hi;
      }
      else
      {
        res &= bit_lo == bit_hi;
      }
    }
    return res;
  }

  char d_consts[TEST_NUM_CONSTS][TEST_CONST_LEN] = {{0}};
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

TEST_F(TestBvProp, eq)
{
  char *str_z;
  BzlaBvDomain *d_x, *d_y, *res_xy, *res_z;

  for (size_t i = 0; i < TEST_NUM_CONSTS; i++)
  {
    d_x = create_domain(d_consts[i]);
    for (size_t j = 0; j < TEST_NUM_CONSTS; j++)
    {
      d_y = create_domain(d_consts[j]);
      bzla_bvprop_eq(d_mm, d_x, d_y, &res_xy, &res_z);
      if (bzla_bvprop_is_fixed(d_mm, res_z))
      {
        str_z = from_domain(d_mm, res_z);
        assert(strlen(str_z) == 1);
        assert(str_z[0] == '0' || str_z[0] == '1');
        if (str_z[0] == '0')
        {
          assert(!bzla_bvprop_is_valid(d_mm, res_xy));
        }
        else
        {
          assert(str_z[0] == '1');
          assert(bzla_bvprop_is_valid(d_mm, res_xy));
          assert(bzla_bvprop_is_fixed(d_mm, res_xy));
        }
        bzla_mem_freestr(d_mm, str_z);
      }
      else
      {
        assert(bzla_bvprop_is_valid(d_mm, res_xy));
      }
      bzla_bvprop_free(d_mm, d_y);
      bzla_bvprop_free(d_mm, res_xy);
      bzla_bvprop_free(d_mm, res_z);
    }
    bzla_bvprop_free(d_mm, d_x);
  }
}
