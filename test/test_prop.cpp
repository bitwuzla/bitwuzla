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
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlaslvprop.h"
}

#include "bzlabitvector.h"
#include "bitvector_domain.h"
#include "rng.h"

class TestProp : public TestPropCommon
{
 protected:
  static constexpr bool TEST_SLOW         = false;
  static constexpr uint32_t TEST_NPROPS   = TEST_SLOW ? 35 * 2 : 20 * 2;
  static constexpr uint32_t TEST_NUPDATES = TEST_SLOW ? 35 * 3 : 20 * 3;

  void SetUp() override
  {
    TestPropCommon::SetUp();
    d_test_bw = TEST_SLOW ? 4 : 3;
    d_rng.reset(new bzlals::RNG(54321));
  }

  Bzla* create_bzla();
  BzlaNode* mk_op_binary(Bzla* bzla,
                         BzlaNodeKind kind,
                         BzlaNode* e0,
                         BzlaNode* e1);
  bzlals::BitVector eval_op_binary(BzlaNodeKind kind,
                                   const bzlals::BitVector& s0_val,
                                   const bzlals::BitVector& s1_val);

  void test_prop_aux(BzlaNodeKind kind,
                     const bzlals::BitVectorDomain* s0,
                     const bzlals::BitVectorDomain* s1,
                     const bzlals::BitVectorDomain* s2,
                     const bzlals::BitVector* s0_val,
                     const bzlals::BitVector* s1_val,
                     const bzlals::BitVector* s2_val,
                     uint32_t idx0 = 0,
                     uint32_t idx1 = 0);

  void test_prop(BzlaNodeKind kind);

  uint32_t d_test_bw;
  std::unique_ptr<bzlals::RNG> d_rng;
};

Bzla*
TestProp::create_bzla()
{
  Bzla* bzla = bzla_new();
  bzla_opt_set(bzla, BZLA_OPT_ENGINE, BZLA_ENGINE_PROP);
  bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, 0);
  bzla_opt_set(bzla, BZLA_OPT_RW_SORT_EXP, 0);
  bzla_opt_set(bzla, BZLA_OPT_PROP_NPROPS, TEST_NPROPS);
  bzla_opt_set(bzla, BZLA_OPT_PROP_NUPDATES, TEST_NUPDATES);
  // bzla_opt_set(bzla, BZLA_OPT_VERBOSITY, 1);
  // bzla_opt_set(bzla, BZLA_OPT_LOGLEVEL, 2);
  return bzla;
}

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
TestProp::test_prop_aux(BzlaNodeKind kind,
                        const bzlals::BitVectorDomain* s0,
                        const bzlals::BitVectorDomain* s1,
                        const bzlals::BitVectorDomain* s2,
                        const bzlals::BitVector* s0_val,
                        const bzlals::BitVector* s1_val,
                        const bzlals::BitVector* s2_val,
                        uint32_t idx0,
                        uint32_t idx1)
{
  assert(s0_val);

  Bzla* bzla      = create_bzla();
  BzlaSortId sort = bzla_sort_bv(bzla, d_test_bw);
  BzlaSortId sort0 =
      s2_val ? bzla_sort_bv(bzla, 1) : bzla_sort_copy(bzla, sort);
  BzlaNode* var0 = bzla_exp_var(bzla, sort0, 0);
  BzlaNode *var1, *var2, *op;
  bzlals::BitVector t_val;

  if (s2_val)
  {
    /* ternary */
    assert(kind == BZLA_COND_NODE);
    assert(s1_val);
    var1  = bzla_exp_var(bzla, sort, 0);
    var2  = bzla_exp_var(bzla, sort, 0);
    op    = bzla_exp_cond(bzla, var0, var1, var2);
    t_val = bzlals::BitVector::bvite(*s0_val, *s1_val, *s2_val);
  }
  else if (s1_val)
  {
    /* binary */
    var1  = bzla_exp_var(bzla, sort, 0);
    op    = mk_op_binary(bzla, kind, var0, var1);
    t_val = eval_op_binary(kind, *s0_val, *s1_val);
  }
  else
  {
    /* unary */
    assert(kind == BZLA_BV_SLICE_NODE);
    op    = bzla_exp_bv_slice(bzla, var0, idx0, idx1);
    t_val = s0_val->bvextract(idx0, idx1);
  }

  BzlaBitVector* t_bv =
      bzla_bv_const(bzla->mm, t_val.to_string().c_str(), t_val.size());
  BzlaNode* t  = bzla_exp_bv_const(bzla, t_bv);
  BzlaNode* eq = bzla_exp_eq(bzla, op, t);

  bzla_assert_exp(bzla, eq);

  if (s0_val)
  {
    bzla_synthesize_exp(bzla, var0, nullptr);
    assert(!bzla_node_is_inverted(var0));
    for (uint32_t i = 0, n = s0->size(); i < n; ++i)
    {
      if (s0->is_fixed_bit(i))
      {
        uint32_t ai    = n - 1 - i;
        BzlaAIGVec* av = var0->av;
        assert(!bzla_aig_is_const(av->aigs[ai]));
        bzla_aig_release(bzla->avmgr->amgr, av->aigs[ai]);
        av->aigs[ai] =
            s0->is_fixed_bit_true(i) ? BZLA_AIG_TRUE : BZLA_AIG_FALSE;
      }
    }
  }

  if (s1_val)
  {
    bzla_synthesize_exp(bzla, var1, nullptr);
    assert(!bzla_node_is_inverted(var1));
    for (uint32_t i = 0, n = s1->size(); i < n; ++i)
    {
      if (s1->is_fixed_bit(i))
      {
        uint32_t ai    = n - 1 - i;
        BzlaAIGVec* av = var1->av;
        assert(!bzla_aig_is_const(av->aigs[ai]));
        bzla_aig_release(bzla->avmgr->amgr, av->aigs[ai]);
        av->aigs[ai] =
            s1->is_fixed_bit_true(i) ? BZLA_AIG_TRUE : BZLA_AIG_FALSE;
      }
    }
  }

  if (s2_val)
  {
    bzla_synthesize_exp(bzla, var2, nullptr);
    assert(!bzla_node_is_inverted(var2));
    for (uint32_t i = 0, n = s2->size(); i < n; ++i)
    {
      if (s2->is_fixed_bit(i))
      {
        uint32_t ai    = n - 1 - i;
        BzlaAIGVec* av = var2->av;
        assert(!bzla_aig_is_const(av->aigs[ai]));
        bzla_aig_release(bzla->avmgr->amgr, av->aigs[ai]);
        av->aigs[ai] =
            s2->is_fixed_bit_true(i) ? BZLA_AIG_TRUE : BZLA_AIG_FALSE;
      }
    }
  }

  int32_t res = bzla_check_sat(bzla, -1, -1);
  assert(res == BZLA_RESULT_SAT || res == BZLA_RESULT_UNSAT);

  bzla_bv_free(bzla->mm, t_bv);
  bzla_node_release(bzla, t);
  bzla_node_release(bzla, eq);
  bzla_node_release(bzla, op);
  bzla_node_release(bzla, var0);
  if (s1_val) bzla_node_release(bzla, var1);
  if (s2_val) bzla_node_release(bzla, var2);
  bzla_sort_release(bzla, sort0);
  bzla_sort_release(bzla, sort);
  bzla_delete(bzla);
}

void
TestProp::test_prop(BzlaNodeKind kind)
{
  std::vector<std::string> xvalues0 = {"x", "0", "1"};
  std::vector<std::string> xvalues;
  gen_xvalues(d_test_bw, xvalues);
  std::vector<std::string>& s0values =
      kind == BZLA_COND_NODE ? xvalues0 : xvalues;

  for (const std::string& s0_domain_value : s0values)
  {
    bzlals::BitVectorDomain s0(s0_domain_value);
    bzlals::BitVectorDomainGenerator gens0(s0);
    do
    {
      bzlals::BitVector s0_val = gens0.has_next() ? gens0.next() : s0.lo();
      if (kind == BZLA_BV_SLICE_NODE)
      {
        for (uint32_t lo = 0, bw_s0 = s0_val.size(); lo < bw_s0; ++lo)
        {
          for (uint32_t hi = lo; hi < bw_s0; ++hi)
          {
            uint32_t bw_t = hi - lo + 1;
            for (uint32_t i = 0, n = 1 << bw_t; i < n; ++i)
            {
              test_prop_aux(kind,
                            &s0,
                            nullptr,
                            nullptr,
                            &s0_val,
                            nullptr,
                            nullptr,
                            hi,
                            lo);
            }
          }
        }
      }
      else
      {
        for (const std::string& s1_domain_value : xvalues)
        {
          bzlals::BitVectorDomain s1(s1_domain_value);
          bzlals::BitVectorDomainGenerator gens1(s1);
          do
          {
            bzlals::BitVector s1_val =
                gens1.has_next() ? gens1.next() : s1.lo();
            if (kind == BZLA_COND_NODE)
            {
              for (const std::string& s2_domain_value : xvalues)
              {
                bzlals::BitVectorDomain s2(s2_domain_value);
                bzlals::BitVectorDomainGenerator gens2(s2);
                do
                {
                  bzlals::BitVector s2_val =
                      gens2.has_next() ? gens2.next() : s2.lo();
                  test_prop_aux(kind, &s0, &s1, &s2, &s0_val, &s1_val, &s2_val);
                } while (gens2.has_next());
              }
            }
            else
            {
              test_prop_aux(kind, &s0, &s1, nullptr, &s0_val, &s1_val, nullptr);
            }
          } while (gens1.has_next());
        }
      }
    } while (gens0.has_next());
  }
}

TEST_F(TestProp, add) { test_prop(BZLA_BV_ADD_NODE); }

TEST_F(TestProp, and) { test_prop(BZLA_BV_AND_NODE); }

TEST_F(TestProp, concat) { test_prop(BZLA_BV_CONCAT_NODE); }

TEST_F(TestProp, eq) { test_prop(BZLA_BV_EQ_NODE); }

TEST_F(TestProp, mul) { test_prop(BZLA_BV_MUL_NODE); }

TEST_F(TestProp, shl) { test_prop(BZLA_BV_SLL_NODE); }

TEST_F(TestProp, shr) { test_prop(BZLA_BV_SRL_NODE); }

TEST_F(TestProp, udiv) { test_prop(BZLA_BV_UDIV_NODE); }

TEST_F(TestProp, ult) { test_prop(BZLA_BV_ULT_NODE); }

TEST_F(TestProp, slt) { test_prop(BZLA_BV_SLT_NODE); }

TEST_F(TestProp, urem) { test_prop(BZLA_BV_UREM_NODE); }

TEST_F(TestProp, ite) { test_prop(BZLA_COND_NODE); }

TEST_F(TestProp, extract) { test_prop(BZLA_BV_SLICE_NODE); }
