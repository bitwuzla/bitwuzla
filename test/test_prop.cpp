/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#include "test.h"

extern "C" {
#include "bzlaexp.h"
#include "bzlaslvprop.h"
}

#include "bitvector.h"
#include "bitvector_domain.h"
#include "rng.h"

class TestProp : public TestPropCommon
{
 protected:
  static constexpr bool TEST_SLOW       = false;
  static constexpr uint32_t nmoves_slow = 35;
  static constexpr uint32_t nmoves_fast = 20;

  void SetUp() override
  {
    TestPropCommon::SetUp();
    d_test_bw = TEST_SLOW ? 4 : 3;
    d_rng.reset(new bzlals::RNG(54321));
  }

  BzlaNode* mk_op_binary(Bzla* bzla,
                         BzlaNodeKind kind,
                         BzlaNode* e0,
                         BzlaNode* e1);
  bzlals::BitVector eval_op_binary(BzlaNodeKind kind,
                                   const bzlals::BitVector& s0_val,
                                   const bzlals::BitVector& s1_val);

  void test_binary(BzlaNodeKind kind);
  // void test_ite();
  // void test_not();
  // void test_extract();
  // void test_sext();

  uint32_t d_test_bw;
  std::unique_ptr<bzlals::RNG> d_rng;
};

BzlaNode*
TestProp::mk_op_binary(Bzla* bzla,
                       BzlaNodeKind kind,
                       BzlaNode* e0,
                       BzlaNode* e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode* res;
  switch (kind)
  {
    case BZLA_BV_ADD_NODE: res = bzla_exp_bv_add(bzla, e0, e1); break;
    case BZLA_BV_AND_NODE: res = bzla_exp_bv_and(bzla, e0, e1); break;
    case BZLA_BV_CONCAT_NODE: res = bzla_exp_bv_concat(bzla, e0, e1); break;
    case BZLA_BV_EQ_NODE: res = bzla_exp_eq(bzla, e0, e1); break;
    case BZLA_BV_MUL_NODE: res = bzla_exp_bv_mul(bzla, e0, e1); break;
    case BZLA_BV_ULT_NODE: res = bzla_exp_bv_ult(bzla, e0, e1); break;
    case BZLA_BV_SLL_NODE: res = bzla_exp_bv_sll(bzla, e0, e1); break;
    case BZLA_BV_SLT_NODE: res = bzla_exp_bv_slt(bzla, e0, e1); break;
    case BZLA_BV_SRL_NODE: res = bzla_exp_bv_srl(bzla, e0, e1); break;
    case BZLA_BV_UDIV_NODE: res = bzla_exp_bv_udiv(bzla, e0, e1); break;
    case BZLA_BV_UREM_NODE: res = bzla_exp_bv_urem(bzla, e0, e1); break;
    default: assert(false);
  }
  return res;
}

bzlals::BitVector
TestProp::eval_op_binary(BzlaNodeKind kind,
                         const bzlals::BitVector& s0_val,
                         const bzlals::BitVector& s1_val)
{
  bzlals::BitVector res;
  switch (kind)
  {
    case BZLA_BV_ADD_NODE: res = s0_val.bvadd(s1_val); break;
    case BZLA_BV_AND_NODE: res = s0_val.bvand(s1_val); break;
    case BZLA_BV_CONCAT_NODE: res = s0_val.bvconcat(s1_val); break;
    case BZLA_BV_EQ_NODE: res = s0_val.bveq(s1_val); break;
    case BZLA_BV_MUL_NODE: res = s0_val.bvmul(s1_val); break;
    case BZLA_BV_SLL_NODE: res = s0_val.bvshl(s1_val); break;
    case BZLA_BV_SRL_NODE: res = s0_val.bvshr(s1_val); break;
    case BZLA_BV_SLT_NODE: res = s0_val.bvslt(s1_val); break;
    case BZLA_BV_UDIV_NODE: res = s0_val.bvudiv(s1_val); break;
    case BZLA_BV_ULT_NODE: res = s0_val.bvult(s1_val); break;
    case BZLA_BV_UREM_NODE: res = s0_val.bvurem(s1_val); break;
    default: assert(false);
  }
  return res;
}

void
TestProp::test_binary(BzlaNodeKind kind)
{
  std::vector<std::string> xvalues;
  gen_xvalues(d_test_bw, xvalues);

  for (const std::string& s0_domain_value : xvalues)
  {
    bzlals::BitVectorDomain s0(s0_domain_value);
    bzlals::BitVectorDomainGenerator gens0(s0);
    do
    {
      bzlals::BitVector s0_val = gens0.has_next() ? gens0.next() : s0.lo();
      for (const std::string& s1_domain_value : xvalues)
      {
        bzlals::BitVectorDomain s1(s1_domain_value);
        bzlals::BitVectorDomainGenerator gens1(s1);
        do
        {
          bzlals::BitVector s1_val = gens1.has_next() ? gens1.next() : s1.lo();
          bzlals::BitVector t_val  = eval_op_binary(kind, s0_val, s1_val);

          Bzla* bzla = bzla_new();
          bzla_opt_set(bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
          bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, 0);
          bzla_opt_set(bzla, BZLA_OPT_RW_SORT_EXP, 0);
          // bzla_opt_set(bzla, BZLA_OPT_LOGLEVEL, 2);
          BzlaSortId sort = bzla_sort_bv(bzla, d_test_bw);
          BzlaNode* var0  = bzla_exp_var(bzla, sort, 0);
          BzlaNode* var1  = bzla_exp_var(bzla, sort, 0);
          BzlaNode* op    = mk_op_binary(bzla, kind, var0, var1);

          BzlaBitVector* t_bv =
              bzla_bv_const(bzla->mm, t_val.to_string().c_str(), t_val.size());
          BzlaNode* t  = bzla_exp_bv_const(bzla, t_bv);
          BzlaNode* eq = bzla_exp_eq(bzla, op, t);
          bzla_assert_exp(bzla, eq);
          // synthesize expression
          // for (uint32_t i = 0, n = s0_val.size(); i < n; ++i)
          //{
          //}
          // for (uint32_t i = 0, n = s1_val.size(); i < n; ++i)
          //{
          //}

          bzla_check_sat(bzla, -1, -1);

          bzla_bv_free(bzla->mm, t_bv);
          bzla_node_release(bzla, eq);
          bzla_node_release(bzla, op);
          bzla_node_release(bzla, var0);
          bzla_node_release(bzla, var1);
          bzla_sort_release(bzla, sort);
        } while (gens1.has_next());
      }
    } while (gens0.has_next());
  }
}

TEST_F(TestProp, add) { test_binary(BZLA_BV_ADD_NODE); }

// TEST_F(TestProp, and)
//{
//  test_binary(BZLA_BV_AND_NODE);
//}
//
// TEST_F(TestProp, concat)
//{
//  test_binary(BZLA_BV_CONCAT_NODE);
//}
//
// TEST_F(TestProp, eq)
//{
//  test_binary(BZLA_BV_EQ_NODE);
//}
//
// TEST_F(TestProp, mul)
//{
//  test_binary(BZLA_BV_MUL_NODE);
//}
//
// TEST_F(TestProp, shl)
//{
//  test_binary(BZLA_BV_SLL_NODE);
//}
//
// TEST_F(TestProp, shr)
//{
//  test_binary(BZLA_BV_SRL_NODE);
//}
//
// TEST_F(TestProp, udiv)
//{
//  test_binary(BZLA_BV_UDIV_NODE);
//}
//
// TEST_F(TestProp, ult)
//{
//  test_binary(BZLA_BV_ULT_NODE);
//}
//
// TEST_F(TestProp, slt)
//{
//  test_binary(BZLA_BV_SLT_NODE);
//}
//
// TEST_F(TestProp, urem)
//{
//  test_binary(BZLA_BV_UREM_NODE);
//}

// TEST_F(TestProp, ite)
//{
//  test_ite(0);
//  test_ite(1);
//  test_ite(2);
//}

// TEST_F(TestProp, not ) { test_not(); }

// TEST_F(TestProp, extract) { test_extract(); }

// TEST_F(TestProp, sext) { test_sext(); }
