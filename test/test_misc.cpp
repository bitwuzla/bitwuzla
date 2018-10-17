/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2018 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

class TestMisc : public TestMm
{
 protected:
  static constexpr uint32_t BZLA_TEST_MISC_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_MISC_HIGH = 4;
  static constexpr uint32_t UEXT                = 0;
  static constexpr uint32_t SEXT                = 1;

  char *int_to_str(int32_t x, int32_t num_bits)
  {
    assert(x >= 0);
    assert(num_bits > 0);
    char *result = nullptr;
    int32_t i    = 0;
    result = (char *) bzla_mem_malloc(d_mm, sizeof(char) * (num_bits + 1));
    for (i = num_bits - 1; i >= 0; i--)
    {
      result[i] = x % 2 ? '1' : '0';
      x >>= 1;
    }
    result[num_bits] = '\0';
    return result;
  }

  char *mk_slice(int32_t x, int32_t high, int32_t low, int32_t num_bits)
  {
    assert(high < num_bits);
    assert(low >= 0);
    assert(low <= high);
    char *temp      = nullptr;
    char *result    = nullptr;
    int32_t i       = 0;
    int32_t counter = 0;
    temp            = int_to_str(x, num_bits);
    assert(temp != nullptr);
    result  = int_to_str(0, high - low + 1);
    counter = high - low;
    for (i = low; i <= high; i++) result[counter--] = temp[num_bits - 1 - i];
    bzla_mem_freestr(d_mm, temp);
    return result;
  }

  void slice_test_misc(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    Bzla *bzla;
    int32_t i        = 0;
    int32_t j        = 0;
    char *result     = 0;
    int32_t num_bits = 0;
    const int32_t x  = 11;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      for (i = num_bits - 1; i >= 0; i--)
      {
        for (j = i; j >= 0; j--)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *slice, *eq;

          bzla = boolector_new();
          boolector_set_opt(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          result = mk_slice(x, i, j, num_bits);

          sort   = boolector_bv_sort(bzla, high);
          const1 = boolector_bv_unsigned_int(bzla, x, sort);
          slice  = boolector_bv_slice(bzla, const1, i, j);
          const2 = boolector_bv_const(bzla, result);
          eq     = boolector_eq(bzla, slice, const2);
          boolector_assert(bzla, eq);

          ASSERT_EQ(boolector_sat(bzla), BOOLECTOR_SAT);
          boolector_release_sort(bzla, sort);
          boolector_release(bzla, const1);
          boolector_release(bzla, const2);
          boolector_release(bzla, slice);
          boolector_release(bzla, eq);
          boolector_delete(bzla);
          bzla_mem_freestr(d_mm, result);
        }
      }
    }
  }

  char *uext(int32_t x, int32_t y, int32_t num_bits)
  {
    assert(x >= 0);
    assert(y >= 0);
    assert(num_bits >= 1);
    char *result = nullptr;
    result       = int_to_str(x, num_bits + y);
    return result;
  }

  char *sext(int32_t x, int32_t y, int32_t num_bits)
  {
    assert(x >= 0);
    assert(y >= 0);
    assert(num_bits >= 1);
    char *result = nullptr;
    int32_t i    = 0;
    result       = int_to_str(x, num_bits + y);
    if (result[y] == '1')
    {
      for (i = 0; i < y; i++) result[i] = '1';
    }
    return result;
  }

  void ext_test_misc(uint32_t ext_mode, int32_t low, int32_t high, uint32_t rwl)
  {
    assert(ext_mode == UEXT || ext_mode == SEXT);
    assert(low > 0);
    assert(low <= high);

    Bzla *bzla;
    BoolectorNode *(*bzla_fun)(Bzla *, BoolectorNode *, uint32_t);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    char *result     = 0;
    int32_t num_bits = 0;

    bzla_fun = ext_mode == UEXT ? boolector_bv_uext : boolector_bv_sext;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < num_bits; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *eq, *bfun;

          bzla = boolector_new();
          boolector_set_opt(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          result =
              ext_mode == UEXT ? uext(i, j, num_bits) : sext(i, j, num_bits);

          sort   = boolector_bv_sort(bzla, num_bits);
          const1 = boolector_bv_unsigned_int(bzla, i, sort);
          bfun   = bzla_fun(bzla, const1, j);
          const2 = boolector_bv_const(bzla, result);
          eq     = boolector_eq(bzla, bfun, const2);
          boolector_assert(bzla, eq);

          ASSERT_EQ(boolector_sat(bzla), BOOLECTOR_SAT);
          boolector_release_sort(bzla, sort);
          boolector_release(bzla, const1);
          boolector_release(bzla, const2);
          boolector_release(bzla, bfun);
          boolector_release(bzla, eq);
          boolector_delete(bzla);
          bzla_mem_freestr(d_mm, result);
        }
      }
    }
  }

  char *mk_concat(int32_t x, int32_t y, int32_t num_bits)
  {
    assert(x >= 0);
    assert(y >= 0);
    assert(num_bits > 0);
    assert(num_bits <= INT32_MAX / 2);

    char *x_string = nullptr;
    char *y_string = nullptr;
    char *result   = nullptr;

    x_string = int_to_str(x, num_bits);
    y_string = int_to_str(y, num_bits);
    result =
        (char *) bzla_mem_malloc(d_mm, sizeof(char) * ((num_bits << 1) + 1));
    strcpy(result, x_string);
    strcat(result, y_string);
    bzla_mem_freestr(d_mm, x_string);
    bzla_mem_freestr(d_mm, y_string);
    return result;
  }

  void concat_test_misc(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    Bzla *bzla;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    char *result     = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *const3, *eq, *concat;

          bzla = boolector_new();
          boolector_set_opt(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          result = mk_concat(i, j, num_bits);

          sort   = boolector_bv_sort(bzla, num_bits);
          const1 = boolector_bv_unsigned_int(bzla, i, sort);
          const2 = boolector_bv_unsigned_int(bzla, j, sort);
          concat = boolector_bv_concat(bzla, const1, const2);
          const3 = boolector_bv_const(bzla, result);
          eq     = boolector_eq(bzla, concat, const3);
          boolector_assert(bzla, eq);

          ASSERT_EQ(boolector_sat(bzla), BOOLECTOR_SAT);
          boolector_release_sort(bzla, sort);
          boolector_release(bzla, const1);
          boolector_release(bzla, const2);
          boolector_release(bzla, const3);
          boolector_release(bzla, concat);
          boolector_release(bzla, eq);
          boolector_delete(bzla);
          bzla_mem_freestr(d_mm, result);
        }
      }
    }
  }

  static void cond_test_misc(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    Bzla *bzla;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t k        = 0;
    int32_t max      = 0;
    int32_t result   = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          for (k = 0; k <= 1; k++)
          {
            BoolectorSort sort, sort1;
            BoolectorNode *const1, *const2, *const3, *const4, *eq, *cond;

            bzla = boolector_new();
            boolector_set_opt(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

            result = k ? i : j;

            sort   = boolector_bv_sort(bzla, num_bits);
            sort1  = boolector_bv_sort(bzla, 1);
            const1 = boolector_bv_unsigned_int(bzla, i, sort);
            const2 = boolector_bv_unsigned_int(bzla, j, sort);
            const3 = boolector_bv_unsigned_int(bzla, k, sort1);
            cond   = boolector_cond(bzla, const3, const1, const2);
            const4 = boolector_bv_unsigned_int(bzla, result, sort);
            eq     = boolector_eq(bzla, cond, const4);
            boolector_assert(bzla, eq);

            ASSERT_EQ(boolector_sat(bzla), BOOLECTOR_SAT);
            boolector_release_sort(bzla, sort);
            boolector_release_sort(bzla, sort1);
            boolector_release(bzla, const1);
            boolector_release(bzla, const2);
            boolector_release(bzla, const3);
            boolector_release(bzla, const4);
            boolector_release(bzla, cond);
            boolector_release(bzla, eq);
            boolector_delete(bzla);
          }
        }
      }
    }
  }

  void read_test_misc(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    Bzla *bzla;
    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          BoolectorSort elem_sort, index_sort, array_sort;
          BoolectorNode *const1, *const2, *const3, *const4;
          BoolectorNode *eq1, *eq2, *array, *read1, *read2;

          bzla = boolector_new();
          boolector_set_opt(bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          elem_sort  = boolector_bv_sort(bzla, num_bits);
          index_sort = boolector_bv_sort(bzla, 1);
          array_sort = boolector_array_sort(bzla, index_sort, elem_sort);
          array      = boolector_array(bzla, array_sort, "array");
          const1     = boolector_false(bzla);
          const2     = boolector_true(bzla);
          const3     = boolector_bv_unsigned_int(bzla, i, elem_sort);
          const4     = boolector_bv_unsigned_int(bzla, j, elem_sort);
          read1      = boolector_read(bzla, array, const1);
          read2      = boolector_read(bzla, array, const2);
          eq1        = boolector_eq(bzla, const3, read1);
          eq2        = boolector_eq(bzla, const4, read2);
          boolector_assert(bzla, eq1);
          boolector_assert(bzla, eq2);

          ASSERT_EQ(boolector_sat(bzla), BOOLECTOR_SAT);
          boolector_release_sort(bzla, elem_sort);
          boolector_release_sort(bzla, index_sort);
          boolector_release_sort(bzla, array_sort);
          boolector_release(bzla, eq1);
          boolector_release(bzla, eq2);
          boolector_release(bzla, read1);
          boolector_release(bzla, read2);
          boolector_release(bzla, const1);
          boolector_release(bzla, const2);
          boolector_release(bzla, const3);
          boolector_release(bzla, const4);
          boolector_release(bzla, array);
          boolector_delete(bzla);
        }
      }
    }
  }
};

TEST_F(TestMisc, slice)
{
  slice_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  slice_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}

TEST_F(TestMisc, uext)
{
  ext_test_misc(UEXT, BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  ext_test_misc(UEXT, BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}

TEST_F(TestMisc, sext)
{
  ext_test_misc(SEXT, BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  ext_test_misc(SEXT, BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}

TEST_F(TestMisc, concat)
{
  concat_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  concat_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}

TEST_F(TestMisc, cond)
{
  cond_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  cond_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}

TEST_F(TestMisc, read)
{
  read_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 1);
  read_test_misc(BZLA_TEST_MISC_LOW, BZLA_TEST_MISC_HIGH, 0);
}
