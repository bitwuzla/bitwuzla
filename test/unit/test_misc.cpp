/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlabv.h"
#include "bzlaexp.h"
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
    BzlaBitVector *resultbv;
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
          BzlaSortId sort;
          BzlaNode *const1, *const2, *slice, *eq;

          bzla = bzla_new();
          bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rwl);

          result   = mk_slice(x, i, j, num_bits);
          resultbv = bzla_bv_char_to_bv(d_mm, result);

          sort   = bzla_sort_bv(bzla, high);
          const1 = bzla_exp_bv_unsigned(bzla, x, sort);
          slice  = bzla_exp_bv_slice(bzla, const1, i, j);
          const2 = bzla_exp_bv_const(bzla, resultbv);
          eq     = bzla_exp_eq(bzla, slice, const2);
          bzla_assert_exp(bzla, eq);

          ASSERT_EQ(bzla_check_sat(bzla, -1, -1), BZLA_RESULT_SAT);
          bzla_bv_free(d_mm, resultbv);
          bzla_sort_release(bzla, sort);
          bzla_node_release(bzla, const1);
          bzla_node_release(bzla, const2);
          bzla_node_release(bzla, slice);
          bzla_node_release(bzla, eq);
          bzla_delete(bzla);
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
    BzlaNode *(*bzla_fun)(Bzla *, BzlaNode *, uint32_t);
    BzlaBitVector *resultbv;

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t max      = 0;
    char *result     = 0;
    int32_t num_bits = 0;

    bzla_fun = ext_mode == UEXT ? bzla_exp_bv_uext : bzla_exp_bv_sext;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < num_bits; j++)
        {
          BzlaSortId sort;
          BzlaNode *const1, *const2, *eq, *bfun;

          bzla = bzla_new();
          bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rwl);

          result =
              ext_mode == UEXT ? uext(i, j, num_bits) : sext(i, j, num_bits);
          resultbv = bzla_bv_char_to_bv(d_mm, result);

          sort   = bzla_sort_bv(bzla, num_bits);
          const1 = bzla_exp_bv_unsigned(bzla, i, sort);
          bfun   = bzla_fun(bzla, const1, j);
          const2 = bzla_exp_bv_const(bzla, resultbv);
          eq     = bzla_exp_eq(bzla, bfun, const2);
          bzla_assert_exp(bzla, eq);

          ASSERT_EQ(bzla_check_sat(bzla, -1, -1), BZLA_RESULT_SAT);
          bzla_bv_free(d_mm, resultbv);
          bzla_sort_release(bzla, sort);
          bzla_node_release(bzla, const1);
          bzla_node_release(bzla, const2);
          bzla_node_release(bzla, bfun);
          bzla_node_release(bzla, eq);
          bzla_delete(bzla);
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
    BzlaBitVector *resultbv;
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
          BzlaSortId sort;
          BzlaNode *const1, *const2, *const3, *eq, *concat;

          bzla = bzla_new();
          bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rwl);

          result   = mk_concat(i, j, num_bits);
          resultbv = bzla_bv_char_to_bv(d_mm, result);

          sort   = bzla_sort_bv(bzla, num_bits);
          const1 = bzla_exp_bv_unsigned(bzla, i, sort);
          const2 = bzla_exp_bv_unsigned(bzla, j, sort);
          concat = bzla_exp_bv_concat(bzla, const1, const2);
          const3 = bzla_exp_bv_const(bzla, resultbv);
          eq     = bzla_exp_eq(bzla, concat, const3);
          bzla_assert_exp(bzla, eq);

          ASSERT_EQ(bzla_check_sat(bzla, -1, -1), BZLA_RESULT_SAT);
          bzla_bv_free(d_mm, resultbv);
          bzla_sort_release(bzla, sort);
          bzla_node_release(bzla, const1);
          bzla_node_release(bzla, const2);
          bzla_node_release(bzla, const3);
          bzla_node_release(bzla, concat);
          bzla_node_release(bzla, eq);
          bzla_delete(bzla);
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
            BzlaSortId sort, sort1;
            BzlaNode *const1, *const2, *const3, *const4, *eq, *cond;

            bzla = bzla_new();
            bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rwl);

            result = k ? i : j;

            sort   = bzla_sort_bv(bzla, num_bits);
            sort1  = bzla_sort_bv(bzla, 1);
            const1 = bzla_exp_bv_unsigned(bzla, i, sort);
            const2 = bzla_exp_bv_unsigned(bzla, j, sort);
            const3 = bzla_exp_bv_unsigned(bzla, k, sort1);
            cond   = bzla_exp_cond(bzla, const3, const1, const2);
            const4 = bzla_exp_bv_unsigned(bzla, result, sort);
            eq     = bzla_exp_eq(bzla, cond, const4);
            bzla_assert_exp(bzla, eq);

            ASSERT_EQ(bzla_check_sat(bzla, -1, -1), BZLA_RESULT_SAT);
            bzla_sort_release(bzla, sort);
            bzla_sort_release(bzla, sort1);
            bzla_node_release(bzla, const1);
            bzla_node_release(bzla, const2);
            bzla_node_release(bzla, const3);
            bzla_node_release(bzla, const4);
            bzla_node_release(bzla, cond);
            bzla_node_release(bzla, eq);
            bzla_delete(bzla);
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
          BzlaSortId elem_sort, index_sort, array_sort;
          BzlaNode *const1, *const2, *const3, *const4;
          BzlaNode *eq1, *eq2, *array, *read1, *read2;

          bzla = bzla_new();
          bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rwl);

          elem_sort  = bzla_sort_bv(bzla, num_bits);
          index_sort = bzla_sort_bv(bzla, 1);
          array_sort = bzla_sort_array(bzla, index_sort, elem_sort);
          array      = bzla_exp_array(bzla, array_sort, "array");
          const1     = bzla_exp_false(bzla);
          const2     = bzla_exp_true(bzla);
          const3     = bzla_exp_bv_unsigned(bzla, i, elem_sort);
          const4     = bzla_exp_bv_unsigned(bzla, j, elem_sort);
          read1      = bzla_exp_read(bzla, array, const1);
          read2      = bzla_exp_read(bzla, array, const2);
          eq1        = bzla_exp_eq(bzla, const3, read1);
          eq2        = bzla_exp_eq(bzla, const4, read2);
          bzla_assert_exp(bzla, eq1);
          bzla_assert_exp(bzla, eq2);

          ASSERT_EQ(bzla_check_sat(bzla, -1, -1), BZLA_RESULT_SAT);
          bzla_sort_release(bzla, elem_sort);
          bzla_sort_release(bzla, index_sort);
          bzla_sort_release(bzla, array_sort);
          bzla_node_release(bzla, eq1);
          bzla_node_release(bzla, eq2);
          bzla_node_release(bzla, read1);
          bzla_node_release(bzla, read2);
          bzla_node_release(bzla, const1);
          bzla_node_release(bzla, const2);
          bzla_node_release(bzla, const3);
          bzla_node_release(bzla, const4);
          bzla_node_release(bzla, array);
          bzla_delete(bzla);
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
