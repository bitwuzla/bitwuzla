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
#include "bzlacore.h"
#include "bzlaexp.h"
#include "dumper/bzladumpbtor.h"
}

class TestExp : public TestBzla
{
 protected:
  void unary_exp_test(BzlaNode *(*func)(Bzla *, BzlaNode *) )
  {
    const uint32_t len = 8;
    BzlaNode *exp1, *exp2, *exp3;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, 8);
    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    exp2 = func(d_bzla, exp1);
    exp3 = func(d_bzla, exp1);

    ASSERT_EQ(exp2, exp3);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), len);
    if (func == bzla_exp_bv_not || func == bzla_exp_bv_neg)
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), len);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), len);
      if (func == bzla_exp_bv_neg)
      {
        ASSERT_TRUE(bzla_node_bv_is_neg(d_bzla, exp2, 0));
        ASSERT_TRUE(bzla_node_bv_is_neg(d_bzla, exp3, 0));
      }
      else
      {
        ASSERT_FALSE(bzla_node_bv_is_neg(d_bzla, exp2, 0));
        ASSERT_FALSE(bzla_node_bv_is_neg(d_bzla, exp3, 0));
      }
    }
    else
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 1u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 1u);
    }
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
    bzla_sort_release(d_bzla, sort);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
  }

  void ext_exp_test(BzlaNode *(*func)(Bzla *, BzlaNode *, uint32_t))
  {
    BzlaNode *exp1, *exp2, *exp3;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, 32);

    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    exp2 = func(d_bzla, exp1, 32);
    exp3 = func(d_bzla, exp1, 32);

    ASSERT_EQ(exp2, exp3);
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
    bzla_sort_release(d_bzla, sort);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
  }

  void binary_commutative_exp_test(BzlaNode *(*func)(Bzla *,
                                                     BzlaNode *,
                                                     BzlaNode *) )
  {
    BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, 8);

    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    exp2 = bzla_exp_var(d_bzla, sort, "v2");
    exp3 = func(d_bzla, exp1, exp2);
    exp4 = func(d_bzla, exp1, exp2);
    exp5 = func(d_bzla, exp2, exp1);

    ASSERT_EQ(exp3, exp4);
    ASSERT_EQ(exp4, exp5);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
    if (func == bzla_exp_eq || func == bzla_exp_ne || func == bzla_exp_bv_uaddo
        || func == bzla_exp_bv_saddo || func == bzla_exp_bv_umulo)
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 1u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 1u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 1u);
    }
    else
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 8u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 8u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 8u);
    }
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
    bzla_sort_release(d_bzla, sort);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
    bzla_node_release(d_bzla, exp4);
    bzla_node_release(d_bzla, exp5);
  }

  void binary_non_commutative_exp_test(BzlaNode *(*func)(Bzla *,
                                                         BzlaNode *,
                                                         BzlaNode *) )
  {
    BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, 32);
    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    exp2 = bzla_exp_var(d_bzla, sort, "v2");
    exp3 = func(d_bzla, exp1, exp2);
    exp4 = func(d_bzla, exp1, exp2);
    exp5 = func(d_bzla, exp2, exp1);

    ASSERT_EQ(exp3, exp4);
    ASSERT_NE(exp4, exp5);
    if (func == bzla_exp_bv_sub || func == bzla_exp_bv_udiv
        || func == bzla_exp_bv_sdiv || func == bzla_exp_bv_urem
        || func == bzla_exp_bv_srem || func == bzla_exp_bv_smod)
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 32u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 32u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 32u);
    }
    else if (func == bzla_exp_bv_concat)
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 64u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 64u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 64u);
    }
    else
    {
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 1u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 1u);
      ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 1u);
    }
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
    bzla_sort_release(d_bzla, sort);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
    bzla_node_release(d_bzla, exp4);
    bzla_node_release(d_bzla, exp5);
  }

  void mulo_exp_test(BzlaNode *(*func)(Bzla *, BzlaNode *, BzlaNode *) )
  {
    BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, 3);

    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    exp2 = bzla_exp_var(d_bzla, sort, "v2");
    exp3 = func(d_bzla, exp1, exp2);
    exp4 = func(d_bzla, exp1, exp2);
    exp5 = func(d_bzla, exp2, exp1);

    ASSERT_EQ(exp3, exp4);
    if (func == bzla_exp_bv_umulo)
      ASSERT_NE(exp4, exp5);
    else
      ASSERT_EQ(exp4, exp5);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 1u);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 1u);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 1u);
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
    bzla_node_release(d_bzla, exp4);
    bzla_node_release(d_bzla, exp5);
    bzla_sort_release(d_bzla, sort);
  }

  void shift_exp_test(uint32_t bw1,
                      uint32_t bw2,
                      BzlaNode *(*func)(Bzla *, BzlaNode *, BzlaNode *) )
  {
    BzlaNode *exp1, *exp2, *exp3, *exp4;
    BzlaSortId sort;

    sort = bzla_sort_bv(d_bzla, bw1);
    exp1 = bzla_exp_var(d_bzla, sort, "v1");
    bzla_sort_release(d_bzla, sort);
    sort = bzla_sort_bv(d_bzla, bw2);
    exp2 = bzla_exp_var(d_bzla, sort, "v2");
    bzla_sort_release(d_bzla, sort);
    exp3 = func(d_bzla, exp1, exp2);
    exp4 = func(d_bzla, exp1, exp2);

    ASSERT_EQ(exp3, exp4);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), bw1);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), bw2);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), bw1);
    ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), bw1);
    bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
    bzla_node_release(d_bzla, exp1);
    bzla_node_release(d_bzla, exp2);
    bzla_node_release(d_bzla, exp3);
    bzla_node_release(d_bzla, exp4);
  }
};

TEST_F(TestExp, new_delete_bzla) {}

TEST_F(TestExp, const)
{
  open_log_file("const_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaBitVector *bv1, *bv2, *bv3;

  bv1  = bzla_bv_char_to_bv(d_bzla->mm, "00010011");
  bv2  = bzla_bv_char_to_bv(d_bzla->mm, "00010011");
  bv3  = bzla_bv_char_to_bv(d_bzla->mm, "0000000000010011");
  exp1 = bzla_exp_bv_const(d_bzla, bv1);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  exp3 = bzla_exp_bv_const(d_bzla, bv3);
  ASSERT_EQ(exp1, exp2);
  ASSERT_NE(exp2, exp3);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 16u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp2);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_bv_free(d_bzla->mm, bv1);
  bzla_bv_free(d_bzla->mm, bv2);
  bzla_bv_free(d_bzla->mm, bv3);
}

TEST_F(TestExp, zero)
{
  open_log_file("zero_exp");

  BzlaNode *exp1, *exp2;
  BzlaBitVector *bv2;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_zero(d_bzla, sort);
  bzla_sort_release(d_bzla, sort);
  bv2  = bzla_bv_new(d_bzla->mm, 8);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_TRUE(bzla_node_is_bv_const_zero(d_bzla, exp1));
  ASSERT_TRUE(bzla_node_is_bv_const_zero(d_bzla, exp2));
  ASSERT_FALSE(bzla_node_is_bv_const_zero(d_bzla, bzla_node_invert(exp1)));
  ASSERT_FALSE(bzla_node_is_bv_const_zero(d_bzla, bzla_node_invert(exp2)));
  ASSERT_TRUE(bzla_node_is_bv_const_ones(d_bzla, bzla_node_invert(exp1)));
  ASSERT_TRUE(bzla_node_is_bv_const_ones(d_bzla, bzla_node_invert(exp2)));
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp1);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_bv_free(d_bzla->mm, bv2);
}

TEST_F(TestExp, ones)
{
  open_log_file("ones_exp");

  BzlaNode *exp1, *exp2;
  BzlaBitVector *bv2;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_ones(d_bzla, sort);
  bzla_sort_release(d_bzla, sort);
  bv2  = bzla_bv_ones(d_bzla->mm, 8);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_TRUE(bzla_node_is_bv_const_ones(d_bzla, exp1));
  ASSERT_TRUE(bzla_node_is_bv_const_ones(d_bzla, exp2));
  ASSERT_FALSE(bzla_node_is_bv_const_ones(d_bzla, bzla_node_invert(exp1)));
  ASSERT_FALSE(bzla_node_is_bv_const_ones(d_bzla, bzla_node_invert(exp2)));
  ASSERT_TRUE(bzla_node_is_bv_const_zero(d_bzla, bzla_node_invert(exp1)));
  ASSERT_TRUE(bzla_node_is_bv_const_zero(d_bzla, bzla_node_invert(exp2)));
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp1);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_bv_free(d_bzla->mm, bv2);
}

TEST_F(TestExp, one)
{
  open_log_file("one_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaBitVector *bv2, *bv3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_one(d_bzla, sort);
  bzla_sort_release(d_bzla, sort);
  bv2  = bzla_bv_one(d_bzla->mm, 8);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_TRUE(bzla_node_is_bv_const_one(d_bzla, exp1));
  ASSERT_TRUE(bzla_node_is_bv_const_one(d_bzla, exp2));
  ASSERT_FALSE(bzla_node_is_bv_const_one(d_bzla, bzla_node_invert(exp1)));
  ASSERT_FALSE(bzla_node_is_bv_const_one(d_bzla, bzla_node_invert(exp2)));
  bv3  = bzla_bv_char_to_bv(d_bzla->mm, "11111110");
  exp3 = bzla_exp_bv_const(d_bzla, bv3);
  ASSERT_FALSE(bzla_node_is_bv_const_one(d_bzla, exp3));
  ASSERT_TRUE(bzla_node_is_bv_const_one(d_bzla, bzla_node_invert(exp3)));
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp1);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_bv_free(d_bzla->mm, bv2);
  bzla_bv_free(d_bzla->mm, bv3);
}

TEST_F(TestExp, min_signed)
{
  open_log_file("min_signed_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaBitVector *bv2, *bv3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_min_signed(d_bzla, sort);
  bzla_sort_release(d_bzla, sort);
  bv2  = bzla_bv_min_signed(d_bzla->mm, 8);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_TRUE(bzla_node_is_bv_const_min_signed(d_bzla, exp1));
  ASSERT_TRUE(bzla_node_is_bv_const_min_signed(d_bzla, exp2));
  ASSERT_FALSE(
      bzla_node_is_bv_const_min_signed(d_bzla, bzla_node_invert(exp1)));
  ASSERT_FALSE(
      bzla_node_is_bv_const_min_signed(d_bzla, bzla_node_invert(exp2)));
  bv3  = bzla_bv_char_to_bv(d_bzla->mm, "01111111");
  exp3 = bzla_exp_bv_const(d_bzla, bv3);
  ASSERT_FALSE(bzla_node_is_bv_const_min_signed(d_bzla, exp3));
  ASSERT_TRUE(bzla_node_is_bv_const_min_signed(d_bzla, bzla_node_invert(exp3)));
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp1);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_bv_free(d_bzla->mm, bv2);
  bzla_bv_free(d_bzla->mm, bv3);
}

TEST_F(TestExp, max_signed)
{
  open_log_file("max_signed_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaBitVector *bv2, *bv3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_max_signed(d_bzla, sort);
  bzla_sort_release(d_bzla, sort);
  bv2  = bzla_bv_max_signed(d_bzla->mm, 8);
  exp2 = bzla_exp_bv_const(d_bzla, bv2);
  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_TRUE(bzla_node_is_bv_const_max_signed(d_bzla, exp1));
  ASSERT_TRUE(bzla_node_is_bv_const_max_signed(d_bzla, exp2));
  ASSERT_FALSE(
      bzla_node_is_bv_const_max_signed(d_bzla, bzla_node_invert(exp1)));
  ASSERT_FALSE(
      bzla_node_is_bv_const_max_signed(d_bzla, bzla_node_invert(exp2)));
  bv3  = bzla_bv_char_to_bv(d_bzla->mm, "10000000");
  exp3 = bzla_exp_bv_const(d_bzla, bv3);
  ASSERT_FALSE(bzla_node_is_bv_const_max_signed(d_bzla, exp3));
  ASSERT_TRUE(bzla_node_is_bv_const_max_signed(d_bzla, bzla_node_invert(exp3)));
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp1);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_bv_free(d_bzla->mm, bv2);
  bzla_bv_free(d_bzla->mm, bv3);
}

TEST_F(TestExp, unsigned_to)
{
  open_log_file("unsigned_to_exp");

  BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7, *exp8;
  BzlaBitVector *bv5, *bv6, *bv7, *bv8;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);
  exp1 = bzla_exp_bv_unsigned(d_bzla, 32u, sort);
  exp2 = bzla_exp_bv_unsigned(d_bzla, 49u, sort);
  exp3 = bzla_exp_bv_unsigned(d_bzla, 3u, sort);
  exp4 = bzla_exp_bv_unsigned(d_bzla, 57u, sort);
  bzla_sort_release(d_bzla, sort);
  bv5  = bzla_bv_char_to_bv(d_bzla->mm, "00100000");
  bv6  = bzla_bv_char_to_bv(d_bzla->mm, "00110001");
  bv7  = bzla_bv_char_to_bv(d_bzla->mm, "00000011");
  bv8  = bzla_bv_char_to_bv(d_bzla->mm, "00111001");
  exp5 = bzla_exp_bv_const(d_bzla, bv5);
  exp6 = bzla_exp_bv_const(d_bzla, bv6);
  exp7 = bzla_exp_bv_const(d_bzla, bv7);
  exp8 = bzla_exp_bv_const(d_bzla, bv8);

  ASSERT_EQ(exp1, exp5);
  ASSERT_EQ(exp2, exp6);
  ASSERT_EQ(exp3, exp7);
  ASSERT_EQ(exp4, exp8);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp6), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp7), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp8), 8u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_node_release(d_bzla, exp4);
  bzla_node_release(d_bzla, exp5);
  bzla_node_release(d_bzla, exp6);
  bzla_node_release(d_bzla, exp7);
  bzla_node_release(d_bzla, exp8);
  bzla_bv_free(d_bzla->mm, bv5);
  bzla_bv_free(d_bzla->mm, bv6);
  bzla_bv_free(d_bzla->mm, bv7);
  bzla_bv_free(d_bzla->mm, bv8);
}

TEST_F(TestExp, var)
{
  open_log_file("var_exp");

  BzlaNode *exp1, *exp2;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);

  exp1 = bzla_exp_var(d_bzla, sort, "v1");
  exp2 = bzla_node_copy(d_bzla, exp1);

  ASSERT_EQ(exp1, exp2);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp2);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
}

TEST_F(TestExp, array)
{
  open_log_file("array_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaSortId index_sort, elem_sort, array_sort;

  elem_sort  = bzla_sort_bv(d_bzla, 32);
  index_sort = bzla_sort_bv(d_bzla, 8);
  array_sort = bzla_sort_array(d_bzla, index_sort, elem_sort);
  exp1       = bzla_exp_array(d_bzla, array_sort, "array1");
  exp2       = bzla_node_copy(d_bzla, exp1);
  exp3       = bzla_exp_array(d_bzla, array_sort, "array2");
  bzla_sort_release(d_bzla, elem_sort);
  bzla_sort_release(d_bzla, index_sort);
  bzla_sort_release(d_bzla, array_sort);

  ASSERT_EQ(exp1, exp2);
  ASSERT_NE(exp1, exp3);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp1))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp2))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp3))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_array_get_element(
                                       d_bzla, bzla_node_get_sort_id(exp1))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_array_get_element(
                                       d_bzla, bzla_node_get_sort_id(exp2))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_array_get_element(
                                       d_bzla, bzla_node_get_sort_id(exp3))),
            32u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp2);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
}

TEST_F(TestExp, not )
{
  open_log_file("not_exp");
  unary_exp_test(bzla_exp_bv_not);
}

TEST_F(TestExp, neg)
{
  open_log_file("neg_exp");
  unary_exp_test(bzla_exp_bv_neg);
}

TEST_F(TestExp, redor)
{
  open_log_file("redor_exp");
  unary_exp_test(bzla_exp_bv_redor);
}

TEST_F(TestExp, redxor)
{
  open_log_file("redxor_exp");
  unary_exp_test(bzla_exp_bv_redxor);
}

TEST_F(TestExp, redand)
{
  open_log_file("redand_exp");
  unary_exp_test(bzla_exp_bv_redand);
}

TEST_F(TestExp, slice)
{
  open_log_file("slice_exp");
  BzlaNode *exp1, *exp2, *exp3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 32);

  exp1 = bzla_exp_var(d_bzla, sort, "v1");
  exp2 = bzla_exp_bv_slice(d_bzla, exp1, 31, 30);
  exp3 = bzla_exp_bv_slice(d_bzla, exp1, 31, 30);

  ASSERT_EQ(exp2, exp3);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
}

TEST_F(TestExp, uext)
{
  open_log_file("uext_exp");
  ext_exp_test(bzla_exp_bv_uext);
}

TEST_F(TestExp, sext)
{
  open_log_file("sext_exp");
  ext_exp_test(bzla_exp_bv_sext);
}

TEST_F(TestExp, or)
{
  open_log_file("or_exp");
  binary_commutative_exp_test(bzla_exp_bv_or);
}

TEST_F(TestExp, xor)
{
  open_log_file("xor_exp");
  binary_commutative_exp_test(bzla_exp_bv_xor);
}

TEST_F(TestExp, xnor)
{
  open_log_file("xnor_exp");
  binary_commutative_exp_test(bzla_exp_bv_xnor);
}

TEST_F(TestExp, and)
{
  open_log_file("and_exp");
  binary_commutative_exp_test(bzla_exp_bv_and);
}

TEST_F(TestExp, eq)
{
  open_log_file("eq_exp");
  binary_commutative_exp_test(bzla_exp_eq);
}

TEST_F(TestExp, ne)
{
  open_log_file("ne_exp");
  binary_commutative_exp_test(bzla_exp_ne);
}

TEST_F(TestExp, add)
{
  open_log_file("add_exp");
  binary_commutative_exp_test(bzla_exp_bv_add);
}

TEST_F(TestExp, uaddo)
{
  open_log_file("uaddo_exp");
  binary_commutative_exp_test(bzla_exp_bv_uaddo);
}

TEST_F(TestExp, saddo)
{
  open_log_file("saddo_exp");
  binary_commutative_exp_test(bzla_exp_bv_saddo);
}

TEST_F(TestExp, mul)
{
  open_log_file("mul_exp");
  binary_commutative_exp_test(bzla_exp_bv_mul);
}

TEST_F(TestExp, ult)
{
  open_log_file("ult_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_ult);
}

TEST_F(TestExp, slt)
{
  open_log_file("slt_exp");
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  binary_non_commutative_exp_test(bzla_exp_bv_slt);
}

TEST_F(TestExp, ulte)
{
  open_log_file("ulte_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_ulte);
}

TEST_F(TestExp, slte)
{
  open_log_file("slte_exp");
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  binary_non_commutative_exp_test(bzla_exp_bv_slte);
}

TEST_F(TestExp, ugt)
{
  open_log_file("ugt_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_ugt);
}

TEST_F(TestExp, sgt)
{
  open_log_file("sgt_exp");
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  binary_non_commutative_exp_test(bzla_exp_bv_sgt);
}

TEST_F(TestExp, ugte)
{
  open_log_file("ugte_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_ugte);
}

TEST_F(TestExp, sgte)
{
  open_log_file("sgte_exp");
  bzla_opt_set(d_bzla, BZLA_OPT_RW_SLT, 0);
  binary_non_commutative_exp_test(bzla_exp_bv_sgte);
}

TEST_F(TestExp, sub)
{
  open_log_file("sub_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_sub);
}

TEST_F(TestExp, usubo)
{
  open_log_file("usubo_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_usubo);
}

TEST_F(TestExp, ssubo)
{
  open_log_file("ssubo_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_ssubo);
}

TEST_F(TestExp, udiv)
{
  open_log_file("udiv_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_udiv);
}

TEST_F(TestExp, sdiv)
{
  open_log_file("sdiv_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_sdiv);
}

TEST_F(TestExp, sdivo)
{
  open_log_file("sdivo_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_sdivo);
}

TEST_F(TestExp, urem)
{
  open_log_file("urem_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_urem);
}

TEST_F(TestExp, srem)
{
  open_log_file("srem_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_srem);
}

TEST_F(TestExp, smod)
{
  open_log_file("smod_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_smod);
}

TEST_F(TestExp, concat)
{
  open_log_file("concat_exp");
  binary_non_commutative_exp_test(bzla_exp_bv_concat);
}

TEST_F(TestExp, umulo)
{
  open_log_file("umulo_exp");
  /* Implementation is not symmetric */
  mulo_exp_test(bzla_exp_bv_umulo);
}

TEST_F(TestExp, smulo)
{
  open_log_file("smulo_exp");
  mulo_exp_test(bzla_exp_bv_smulo);
}

TEST_F(TestExp, sll)
{
  open_log_file("sll_exp");
  shift_exp_test(5, 5, bzla_exp_bv_sll);
}

TEST_F(TestExp, srl)
{
  open_log_file("srl_exp");
  shift_exp_test(5, 5, bzla_exp_bv_srl);
}

TEST_F(TestExp, sra)
{
  open_log_file("sra_exp");
  shift_exp_test(5, 5, bzla_exp_bv_sra);
}

TEST_F(TestExp, rol)
{
  open_log_file("rol_exp");
  shift_exp_test(5, 5, bzla_exp_bv_rol);
}

TEST_F(TestExp, ror)
{
  open_log_file("ror_exp");
  shift_exp_test(5, 5, bzla_exp_bv_ror);
}

TEST_F(TestExp, read)
{
  open_log_file("read_exp");

  BzlaNode *exp1, *exp2, *exp3, *exp4;
  BzlaSortId elem_sort, index_sort, array_sort;

  elem_sort  = bzla_sort_bv(d_bzla, 32);
  index_sort = bzla_sort_bv(d_bzla, 8);
  array_sort = bzla_sort_array(d_bzla, index_sort, elem_sort);

  exp1 = bzla_exp_array(d_bzla, array_sort, "array1");
  exp2 = bzla_exp_var(d_bzla, index_sort, "v1");
  exp3 = bzla_exp_read(d_bzla, exp1, exp2);
  exp4 = bzla_exp_read(d_bzla, exp1, exp2);

  ASSERT_EQ(exp4, exp3);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp1))),
            32u);
  ASSERT_EQ(bzla_sort_bv_get_width(
                d_bzla,
                bzla_sort_array_get_index(d_bzla, bzla_node_get_sort_id(exp1))),
            8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 8u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 32u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 32u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
  bzla_sort_release(d_bzla, elem_sort);
  bzla_sort_release(d_bzla, index_sort);
  bzla_sort_release(d_bzla, array_sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_node_release(d_bzla, exp4);
}

TEST_F(TestExp, cond)
{
  open_log_file("cond_exp");

  BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6;
  BzlaBitVector *bv3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 1);
  exp1 = bzla_exp_var(d_bzla, sort, "v1");
  bzla_sort_release(d_bzla, sort);
  sort = bzla_sort_bv(d_bzla, 32);
  exp2 = bzla_exp_var(d_bzla, sort, "v2");
  bzla_sort_release(d_bzla, sort);
  bv3  = bzla_bv_char_to_bv(d_bzla->mm, "00110111001101010001010100110100");
  exp3 = bzla_exp_bv_const(d_bzla, bv3);
  exp4 = bzla_exp_cond(d_bzla, exp1, exp2, exp3);
  exp5 = bzla_exp_cond(d_bzla, exp1, exp2, exp3);
  exp6 = bzla_exp_cond(d_bzla, exp1, exp3, exp2);

  ASSERT_EQ(exp4, exp5);
  ASSERT_NE(exp4, exp6);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp1), 1u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 32u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 32u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp4), 32u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp5), 32u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp6), 32u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp4);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_node_release(d_bzla, exp4);
  bzla_node_release(d_bzla, exp5);
  bzla_node_release(d_bzla, exp6);
  bzla_bv_free(d_bzla->mm, bv3);
}

TEST_F(TestExp, write)
{
  open_log_file("write_exp");

  BzlaNode *exp1, *exp2, *exp3, *exp4, *exp5, *exp6, *exp7;
  BzlaSortId sort, array_sort;

  sort       = bzla_sort_bv(d_bzla, 1);
  array_sort = bzla_sort_array(d_bzla, sort, sort);

  exp1 = bzla_exp_array(d_bzla, array_sort, "array1");
  exp2 = bzla_exp_var(d_bzla, sort, "v1");
  exp3 = bzla_exp_var(d_bzla, sort, "v2");
  exp4 = bzla_exp_write(d_bzla, exp1, exp2, exp3);
  exp5 = bzla_exp_write(d_bzla, exp1, exp2, exp3);
  exp6 = bzla_exp_write(d_bzla, exp1, exp3, exp2);
  exp7 = bzla_exp_read(d_bzla, exp5, exp2);

  ASSERT_EQ(exp4, exp5);
  ASSERT_NE(exp4, exp6);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp1))),
            1u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp2), 1u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp3), 1u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp4))),
            1u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp5))),
            1u);
  ASSERT_EQ(bzla_sort_bv_get_width(d_bzla,
                                   bzla_sort_fun_get_codomain(
                                       d_bzla, bzla_node_get_sort_id(exp6))),
            1u);
  ASSERT_EQ(bzla_node_bv_get_width(d_bzla, exp7), 1u);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp7);
  bzla_sort_release(d_bzla, sort);
  bzla_sort_release(d_bzla, array_sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
  bzla_node_release(d_bzla, exp4);
  bzla_node_release(d_bzla, exp5);
  bzla_node_release(d_bzla, exp6);
  bzla_node_release(d_bzla, exp7);
}

TEST_F(TestExp, inc)
{
  open_log_file("inc_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);

  exp1 = bzla_exp_var(d_bzla, sort, "v1");
  exp2 = bzla_exp_bv_inc(d_bzla, exp1);
  exp3 = bzla_exp_bv_inc(d_bzla, exp1);

  ASSERT_EQ(exp2, exp3);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
}

TEST_F(TestExp, dec)
{
  open_log_file("dec_exp");

  BzlaNode *exp1, *exp2, *exp3;
  BzlaSortId sort;

  sort = bzla_sort_bv(d_bzla, 8);

  exp1 = bzla_exp_var(d_bzla, sort, "v1");
  exp2 = bzla_exp_bv_dec(d_bzla, exp1);
  exp3 = bzla_exp_bv_dec(d_bzla, exp1);

  ASSERT_EQ(exp2, exp3);
  bzla_dumpbtor_dump_node(d_bzla, d_log_file, exp3);
  bzla_sort_release(d_bzla, sort);
  bzla_node_release(d_bzla, exp1);
  bzla_node_release(d_bzla, exp2);
  bzla_node_release(d_bzla, exp3);
}
