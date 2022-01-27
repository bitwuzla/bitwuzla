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
#include "bzlaaigvec.h"
#include "bzlabv.h"
}

class TestAigvec : public TestBzla
{
};

TEST_F(TestAigvec, new_delete_aigvec_mgr)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, const)
{
  BzlaBitVector *bits  = bzla_bv_uint64_to_bv(d_bzla->mm, 11, 4);  // "1011"
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av       = bzla_aigvec_const(avmgr, bits);
  ASSERT_EQ(av->width, 4u);
  bzla_aigvec_release_delete(avmgr, av);
  bzla_aigvec_mgr_delete(avmgr);
  bzla_bv_free(d_bzla->mm, bits);
}

TEST_F(TestAigvec, zero)
{
  BzlaAIGVec *av1, *av2;
  BzlaBitVector *bits;
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);

  bits = bzla_bv_zero(d_bzla->mm, 4);
  av1  = bzla_aigvec_const(avmgr, bits);
  av2  = bzla_aigvec_zero(avmgr, 4);
  ASSERT_EQ(av1->width, 4u);
  ASSERT_EQ(av1->width, av2->width);
  ASSERT_EQ(memcmp(av1->aigs, av2->aigs, sizeof(BzlaAIG *) * av1->width), 0);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_bv_free(d_bzla->mm, bits);

  bits = bzla_bv_ones(d_bzla->mm, 4);
  av1  = bzla_aigvec_const(avmgr, bits);
  av2  = bzla_aigvec_zero(avmgr, 4);
  ASSERT_EQ(av1->width, 4u);
  ASSERT_EQ(av1->width, av2->width);
  ASSERT_GT(memcmp(av1->aigs, av2->aigs, sizeof(BzlaAIG *) * av1->width), 0);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_bv_free(d_bzla->mm, bits);

  bits = bzla_bv_one(d_bzla->mm, 4);
  av1  = bzla_aigvec_const(avmgr, bits);
  av2  = bzla_aigvec_zero(avmgr, 4);
  ASSERT_EQ(av1->width, 4u);
  ASSERT_EQ(av1->width, av2->width);
  ASSERT_GT(memcmp(av1->aigs, av2->aigs, sizeof(BzlaAIG *) * av1->width), 0);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_bv_free(d_bzla->mm, bits);

  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, var)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av       = bzla_aigvec_var(avmgr, 32);
  ASSERT_TRUE(av->width == 32);
  bzla_aigvec_release_delete(avmgr, av);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, invert)
{
  int32_t i            = 0;
  int32_t width        = 0;
  BzlaBitVector *bits  = bzla_bv_uint64_to_bv(d_bzla->mm, 11, 4);  // "1011"
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_const(avmgr, bits);
  width                = av1->width;
  ASSERT_TRUE(width == 32);
  for (i = 0; i < width; i++)
  {
    ASSERT_TRUE(!BZLA_IS_INVERTED_AIG(av1->aigs[i]));
    ASSERT_TRUE(bzla_aig_is_var(av1->aigs[i]));
  }
  bzla_aigvec_invert(avmgr, av1);
  for (i = 0; i < width; i++) ASSERT_TRUE(BZLA_IS_INVERTED_AIG(av1->aigs[i]));
  bzla_aigvec_invert(avmgr, av1);
  for (i = 0; i < width; i++)
  {
    ASSERT_TRUE(!BZLA_IS_INVERTED_AIG(av1->aigs[i]));
    ASSERT_TRUE(bzla_aig_is_var(av1->aigs[i]));
  }
  ASSERT_TRUE(av2->aigs[0] == BZLA_AIG_TRUE);
  ASSERT_TRUE(av2->aigs[1] == BZLA_AIG_FALSE);
  ASSERT_TRUE(av2->aigs[2] == BZLA_AIG_TRUE);
  ASSERT_TRUE(av2->aigs[3] == BZLA_AIG_TRUE);
  bzla_aigvec_invert(avmgr, av2);
  ASSERT_TRUE(av2->aigs[0] == BZLA_AIG_FALSE);
  ASSERT_TRUE(av2->aigs[1] == BZLA_AIG_TRUE);
  ASSERT_TRUE(av2->aigs[2] == BZLA_AIG_FALSE);
  ASSERT_TRUE(av2->aigs[3] == BZLA_AIG_FALSE);
  bzla_aigvec_invert(avmgr, av2);
  ASSERT_TRUE(av2->aigs[0] == BZLA_AIG_TRUE);
  ASSERT_TRUE(av2->aigs[1] == BZLA_AIG_FALSE);
  ASSERT_TRUE(av2->aigs[2] == BZLA_AIG_TRUE);
  ASSERT_TRUE(av2->aigs[3] == BZLA_AIG_TRUE);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_mgr_delete(avmgr);
  bzla_bv_free(d_bzla->mm, bits);
}

TEST_F(TestAigvec, not )
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_not(avmgr, av1);
  ASSERT_TRUE(av2->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, slice)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_slice(avmgr, av1, 17, 2);
  ASSERT_TRUE(av2->width == 16);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, and)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_and(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, ult)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_ult(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 1);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, eq)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_eq(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 1);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, add)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_add(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, sll)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_sll(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, srl)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_srl(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, mul)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_mul(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, udiv)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_udiv(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, urem)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_urem(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, concat)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 16);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_concat(avmgr, av1, av2);
  ASSERT_TRUE(av3->width == 48);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_mgr_delete(avmgr);
}

TEST_F(TestAigvec, cond)
{
  BzlaAIGVecMgr *avmgr = bzla_aigvec_mgr_new(d_bzla);
  BzlaAIGVec *av1      = bzla_aigvec_var(avmgr, 1);
  BzlaAIGVec *av2      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av3      = bzla_aigvec_var(avmgr, 32);
  BzlaAIGVec *av4      = bzla_aigvec_cond(avmgr, av1, av2, av3);
  ASSERT_TRUE(av4->width == 32);
  bzla_aigvec_release_delete(avmgr, av1);
  bzla_aigvec_release_delete(avmgr, av2);
  bzla_aigvec_release_delete(avmgr, av3);
  bzla_aigvec_release_delete(avmgr, av4);
  bzla_aigvec_mgr_delete(avmgr);
}
