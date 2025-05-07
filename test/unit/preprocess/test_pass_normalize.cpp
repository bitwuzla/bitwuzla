/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "preprocess/pass/normalize.h"
#include "rewrite/rewriter.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace bzla::node;
using namespace bzla::preprocess::pass;

/* -------------------------------------------------------------------------- */

class TestPassNormalize : public TestPreprocessingPass
{
 protected:
  TestPassNormalize()
  {
    d_env.reset(new Env(d_nm, d_options));
    d_pass.reset(new PassNormalize(*d_env, &d_bm));
  };

  Node neg(const Node& a)
  {
    return RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
               d_env->rewriter(), d_nm.mk_node(Kind::BV_NEG, {a}))
        .first;
  }

  Node inv(const Node& a) { return d_nm.mk_node(Kind::BV_NOT, {a}); }

  Node rw(const Node& n) { return d_env->rewriter().rewrite(n); }

  Node add(const Node& a, const Node& b)
  {
    return d_nm.mk_node(Kind::BV_ADD, {a, b});
  }

  Node mul(const Node& a, const Node& b)
  {
    return d_nm.mk_node(Kind::BV_MUL, {a, b});
  }

  Node aand(const Node& a, const Node& b)
  {
    return d_nm.mk_node(Kind::BV_AND, {a, b});
  }

  Node oor(const Node& a, const Node& b)
  {
    return RewriteRule<RewriteRuleKind::BV_OR_ELIM>::apply(
               d_env->rewriter(), d_nm.mk_node(Kind::BV_OR, {a, b}))
        .first;
  }

  Node equal(const Node& a, const Node& b)
  {
    return d_nm.mk_node(Kind::EQUAL, {a, b});
  }

  Node ult(const Node& a, const Node& b)
  {
    return d_nm.mk_node(Kind::BV_ULT, {a, b});
  }

  void test_compute_occurrences(
      const Node& node,
      const std::unordered_map<Node, int64_t>& expected,
      bool consider_neg)
  {
    PassNormalize::OccMap occs;
    if (node.kind() == Kind::BV_ADD)
    {
      d_pass->compute_occurrences_add(node, occs);
    }
    else
    {
      d_pass->compute_occurrences_mul(node, occs);
    }

    if (consider_neg)
    {
      if (node.kind() == Kind::BV_ADD)
      {
        auto value = d_pass->normalize_add(node, occs);
        if (!value.is_zero())
        {
          auto [it, inserted] = occs.emplace(d_nm.mk_value(value), 1);
          if (!inserted)
          {
            ++it->second;
          }
        }
      }
    }

    std::cout << node << std::endl;
    std::cout << "expected:" << std::endl;
    for (auto& p : expected)
    {
      std::cout << p.second << ": " << p.first << std::endl;
    }
    std::cout << "actual:" << std::endl;
    for (auto& p : occs)
    {
      std::cout << p.second << ": " << p.first << std::endl;
    }

    for (auto& p : expected)
    {
      auto it = occs.find(p.first);
      if (it == occs.end() && p.second != 0)
      {
        std::cout << "missing occurrence for: " << p.first << std::endl;
        std::cout << "occs:" << std::endl;
        for (const auto& f : occs)
        {
          std::cout << "  " << f.first << ": " << f.second << std::endl;
        }
      }
      ASSERT_TRUE(it != occs.end() || p.second == 0);
      if (it != occs.end())
      {
        if (it->second != p.second)
        {
          std::cout << it->first << " with " << it->second
                    << ", expected: " << p.second << std::endl;
          for (auto& f : occs)
          {
            std::cout << " - " << f.first << ": " << f.second << std::endl;
          }
        }
        ASSERT_EQ(it->second, p.second);
      }
    }

    for (auto& p : occs)
    {
      auto it = expected.find(p.first);
      if (it == expected.end())
      {
        std::cout << "computed occurrence for: " << p.first << std::endl;
        for (const auto& f : occs)
        {
          std::cout << "  " << f.first << ": " << f.second << std::endl;
        }
        std::cout << "but missing in expected:" << std::endl;
        for (const auto& f : expected)
        {
          std::cout << "  " << f.first << ": " << f.second << std::endl;
        }
      }
      ASSERT_TRUE(it != expected.end());
    }
  }

  void test_compute_occurrences(
      const Node& node,
      const std::unordered_map<Node, int64_t>& expected0,
      const std::unordered_map<Node, int64_t>& expected1,
      bool consider_neg)
  {
    PassNormalize::OccMap occs0, occs1;
    if (node[0].kind() == Kind::BV_ADD)
    {
      d_pass->compute_occurrences_add(node[0], occs0);
      d_pass->compute_occurrences_add(node[1], occs1);
    }
    else
    {
      d_pass->compute_occurrences_mul(node[0], occs0);
      d_pass->compute_occurrences_mul(node[1], occs1);
    }

    test_compute_occurrences(node[0], expected0, consider_neg);
    test_compute_occurrences(node[1], expected1, consider_neg);
  }

  void test_assertion(const Node& node, const Node& expected)
  {
    AssertionStack as;
    as.push_back(node);
    ASSERT_EQ(as.size(), 1);
    preprocess::AssertionVector assertions(as.view());
    d_pass->apply(assertions);
    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], rw(expected));
  }

  Type d_bv_type = d_nm.mk_bv_type(8);
  Node a         = d_nm.mk_const(d_bv_type, "a");
  Node b         = d_nm.mk_const(d_bv_type, "b");
  Node c         = d_nm.mk_const(d_bv_type, "c");
  Node d         = d_nm.mk_const(d_bv_type, "d");
  Node e         = d_nm.mk_const(d_bv_type, "e");
  Node one       = d_nm.mk_value(BitVector::mk_one(8));
  Node ones      = d_nm.mk_value(BitVector::mk_ones(8));
  Node zero      = d_nm.mk_value(BitVector::mk_zero(8));
  Node two       = d_nm.mk_value(BitVector::from_ui(8, 2));
  Node three     = d_nm.mk_value(BitVector::from_ui(8, 3));
  Node four      = d_nm.mk_value(BitVector::from_ui(8, 4));
  Node five      = d_nm.mk_value(BitVector::from_ui(8, 5));
  Node six       = d_nm.mk_value(BitVector::from_ui(8, 6));
  Node d_true    = d_nm.mk_value(true);

  std::unique_ptr<preprocess::pass::PassNormalize> d_pass;
  std::unique_ptr<Env> d_env;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, normalize_add1)
{
  PassNormalize::OccMap occs{{a, 2}, {b, 1}, {two, 1}, {one, 2}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 2}, {b, 1}};

  ASSERT_EQ(val, BitVector::from_ui(d_bv_type.bv_size(), 4));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, normalize_add2)
{
  PassNormalize::OccMap occs{{a, 2}, {b, 1}, {inv(b), 1}, {one, 1}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 2}, {b, 0}};

  ASSERT_EQ(val, BitVector::from_ui(d_bv_type.bv_size(), 0));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, normalize_add3)
{
  PassNormalize::OccMap occs{{a, 2}, {b, 1}, {add(a, b), 1}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 3}, {b, 2}};

  ASSERT_EQ(val, BitVector::from_ui(d_bv_type.bv_size(), 0));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, normalize_add4)
{
  PassNormalize::OccMap occs{{a, 2}, {b, 1}, {mul(two, add(a, b)), 1}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 4}, {b, 3}};

  ASSERT_EQ(val, BitVector::from_ui(d_bv_type.bv_size(), 0));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, normalize_add5)
{
  PassNormalize::OccMap occs{{a, 2}, {b, 1}, {inv(add(a, b)), 1}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 1}, {b, 0}};

  ASSERT_EQ(val, BitVector::mk_ones(d_bv_type.bv_size()));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, normalize_add6)
{
  PassNormalize::OccMap occs{{mul(ones, add(a, b)), 1}};
  auto val = d_pass->normalize_add(a, occs);

  PassNormalize::OccMap occs_exp = {{a, 255}, {b, 255}};

  ASSERT_EQ(val, BitVector::from_ui(d_bv_type.bv_size(), 0));
  ASSERT_EQ(occs_exp, occs);
}

TEST_F(TestPassNormalize, compute_occurrences0)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_cd   = mul(c, d);
  Node mul_cd_e = mul(mul_cd, e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 1}, {b, 1}, {c, 1}, {d, 1}, {e, 1}},
                           {{a, 1}, {b, 1}, {c, 1}, {d, 1}, {e, 1}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences1)
{
  // (a * b) * ((a * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_ad   = mul(a, d);
  Node mul_ad_e = mul(mul_ad, e);
  Node mul0     = mul(mul_ab, mul_ad_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 2}, {b, 1}, {d, 1}, {e, 1}},
                           {{a, 1}, {b, 1}, {c, 1}, {d, 1}, {e, 1}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences2)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_cd   = mul(c, d);
  Node mul_cd_e = mul(mul_cd, e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (a * e))))
  Node mul_ae   = mul(a, e);
  Node mul_cae  = mul(c, mul_ae);
  Node mul_bcae = mul(b, mul_cae);
  Node mul1     = mul(a, mul_bcae);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 1}, {b, 1}, {c, 1}, {d, 1}, {e, 1}},
                           {{a, 2}, {b, 1}, {c, 1}, {e, 1}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences3)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_cd      = mul(c, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 2}, {b, 2}, {c, 1}, {d, 1}, {e, 1}},
                           {{a, 1}, {b, 1}, {c, 1}, {d, 1}, {e, 1}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences4)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_cd      = mul(c, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_a_cd    = mul(a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 2}, {b, 2}, {c, 1}, {d, 1}, {e, 1}},
                           {{a, 2}, {b, 1}, {c, 2}, {d, 2}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences5)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_ad      = mul(a, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_cd      = mul(c, d);
  Node mul_a_cd    = mul(a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 3}, {b, 2}, {d, 1}, {e, 1}},
                           {{a, 2}, {b, 1}, {c, 2}, {d, 2}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences6)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_ad      = mul(a, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 3}, {b, 2}, {d, 1}, {e, 1}},
                           {{a, 7}, {b, 6}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences7)
{
  // (a * b) * ((a + d) * (e * (a + b))
  Node mul_ab      = mul(a, b);
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node mul_e_ab    = mul(e, add_ab);
  Node mul_ad_e_ab = mul(add_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a + b) * ((c * d) * (a + (c + d))
  Node mul_cd      = mul(c, d);
  Node add_cd      = add(c, d);
  Node add_a_cd    = add(a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  test_compute_occurrences(equal(mul0, mul1),
                           {{a, 1}, {b, 1}, {e, 1}, {add_ab, 1}, {add_ad, 1}},
                           {{c, 1}, {d, 1}, {add_ab, 1}, {add_a_cd, 1}},
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences8)
{
  Node add_ab   = add(a, b);
  Node add_abc  = add(add_ab, c);
  Node add_2abc = add(add_abc, add_abc);
  Node add0     = add(add_2abc, add_ab);

  test_compute_occurrences(add0,
                           {
                               {a, 3},
                               {b, 3},
                               {c, 2},
                           },
                           false);
}

TEST_F(TestPassNormalize, compute_occurrences_neg0)
{
  // (a + b) + ((-a + d) + (-e + (a + b))
  Node add_ab      = add(a, b);
  Node add_ad      = add(neg(a), d);
  Node add_e_ab    = add(neg(e), add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_occurrences(add0, {{a, 1}, {b, 2}, {d, 1}, {e, -1}}, true);
}

TEST_F(TestPassNormalize, compute_occurrences_neg1)
{
  // (a + b) + (-(a + d) + (e + -(a + b))
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node add_e_ab    = add(e, neg(add_ab));
  Node add_ad_e_ab = add(neg(add_ad), add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_occurrences(add0,
                           {{a, -1},
                            {b, 0},
                            {d, -1},
                            {e, 1},
                            {one, 0},
                            {inv(add_ab), 0},
                            {inv(add_ad), 0}},
                           true);
}

TEST_F(TestPassNormalize, compute_occurrences_neg2)
{
  // -(a + (b + c))
  Node add_bc      = add(b, c);
  Node add_abc     = add(a, add_bc);
  Node neg_add_abc = neg(add_abc);

  test_compute_occurrences(neg_add_abc,
                           {
                               {a, -1},
                               {b, -1},
                               {c, -1},
                               {one, 0},
                               {inv(add_abc), 0},
                           },
                           true);
}

TEST_F(TestPassNormalize, compute_occurrences_neg3)
{
  // (a + b) + ~(a + b)
  Node add_ab = add(a, b);

  test_compute_occurrences(add(add_ab, inv(add_ab)),
                           {
                               {a, 0},
                               {b, 0},
                               {inv(add_ab), 0},
                               {ones, 1},
                               {inv(add_ab), 0},
                           },
                           true);
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, compute_common_occurrences_mul1)
{
  PassNormalize::OccMap lhs{{c, 1}, {b, 3}, {a, 2}, {d, 1}};
  PassNormalize::OccMap rhs{{a, 6}, {b, 7}};

  PassNormalize::OccMap lhs_exp{{c, 1}, {b, 0}, {a, 0}, {d, 1}};
  PassNormalize::OccMap rhs_exp{{a, 4}, {b, 4}};
  PassNormalize::OccMap occs_exp{{a, 2}, {b, 3}};

  Node exp  = d_pass->mk_node(Kind::BV_MUL, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_MUL, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_mul2)
{
  PassNormalize::OccMap lhs{{c, 2}, {b, 3}, {a, 4}};
  PassNormalize::OccMap rhs{{a, 6}, {b, 5}, {c, 3}};

  PassNormalize::OccMap lhs_exp{{c, 0}, {b, 0}, {a, 0}};
  PassNormalize::OccMap rhs_exp{{a, 2}, {b, 2}, {c, 1}};
  PassNormalize::OccMap occs_exp{{a, 4}, {b, 3}, {c, 2}};

  Node exp  = d_pass->mk_node(Kind::BV_MUL, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_MUL, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_mul3)
{
  PassNormalize::OccMap lhs{{c, 2}, {b, 3}, {a, 6}};
  PassNormalize::OccMap rhs{{a, 7}, {b, 5}, {c, 3}};

  PassNormalize::OccMap lhs_exp{{c, 0}, {b, 0}, {a, 0}};
  PassNormalize::OccMap rhs_exp{{a, 1}, {b, 2}, {c, 1}};
  PassNormalize::OccMap occs_exp{{a, 6}, {b, 3}, {c, 2}};

  Node exp  = d_pass->mk_node(Kind::BV_MUL, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_MUL, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_add1)
{
  PassNormalize::OccMap lhs{{c, 1}, {b, 3}, {a, 2}, {d, 1}};
  PassNormalize::OccMap rhs{{a, 6}, {b, 7}};

  PassNormalize::OccMap lhs_exp{{c, 1}, {b, 0}, {a, 0}, {d, 1}};
  PassNormalize::OccMap rhs_exp{{a, 4}, {b, 4}};
  PassNormalize::OccMap occs_exp{{a, 2}, {b, 3}};

  Node exp  = d_pass->mk_node(Kind::BV_ADD, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_ADD, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_add2)
{
  PassNormalize::OccMap lhs{{c, 2}, {b, 3}, {a, 4}};
  PassNormalize::OccMap rhs{{a, 6}, {b, 5}, {c, 3}};

  PassNormalize::OccMap lhs_exp{{c, 0}, {b, 0}, {a, 0}};
  PassNormalize::OccMap rhs_exp{{a, 2}, {b, 2}, {c, 1}};
  PassNormalize::OccMap occs_exp{{a, 4}, {b, 3}, {c, 2}};

  Node exp  = d_pass->mk_node(Kind::BV_ADD, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_ADD, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_add3)
{
  PassNormalize::OccMap lhs{{c, 2}, {b, 3}, {a, 6}};
  PassNormalize::OccMap rhs{{a, 6}, {b, 5}, {c, 3}};

  PassNormalize::OccMap lhs_exp{{c, 0}, {b, 0}, {a, 0}};
  PassNormalize::OccMap rhs_exp{{a, 0}, {b, 2}, {c, 1}};
  PassNormalize::OccMap occs_exp{{a, 6}, {b, 3}, {c, 2}};

  Node exp  = d_pass->mk_node(Kind::BV_ADD, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_ADD, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

TEST_F(TestPassNormalize, compute_common_occurrences_add4)
{
  PassNormalize::OccMap lhs{{a, 1}, {b, 1}, {c, 1}};
  PassNormalize::OccMap rhs{{a, 1}, {b, 1}};

  PassNormalize::OccMap lhs_exp{{a, 0}, {b, 0}, {c, 1}};
  PassNormalize::OccMap rhs_exp{{a, 0}, {b, 0}};
  PassNormalize::OccMap occs_exp{{a, 1}, {b, 1}};

  Node exp  = d_pass->mk_node(Kind::BV_ADD, occs_exp);
  auto occs = d_pass->compute_common_subterms(lhs, rhs);
  Node res  = d_pass->mk_node(Kind::BV_ADD, occs);

  ASSERT_EQ(occs, occs_exp);
  ASSERT_EQ(res, exp);
  ASSERT_EQ(lhs, lhs_exp);
  ASSERT_EQ(rhs, rhs_exp);
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, mul_normalize00)
{
  // (a * b) = (b * a)
  test_assertion(equal(mul(a, b), mul(b, a)), d_true);
}

TEST_F(TestPassNormalize, mul_normalize01)
{
  // (a * b) = (b * a) * (a * b)
  Node mul_ab = mul(a, b);
  test_assertion(equal(mul_ab, mul(mul(b, a), mul_ab)),
                 equal(mul_ab, mul(mul_ab, mul_ab)));
}

TEST_F(TestPassNormalize, mul_normalize0)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_cd   = mul(c, d);
  Node mul_cd_e = mul(mul_cd, e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  test_assertion(equal(mul0, mul1), d_true);
}

TEST_F(TestPassNormalize, mul_normalize1)
{
  // (a * b) * ((a * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_ad   = mul(a, d);
  Node mul_ad_e = mul(mul_ad, e);
  Node mul0     = mul(mul_ab, mul_ad_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  // common: abde
  // a * common = c * common
  Node common = mul(mul(a, b), mul(d, e));
  Node exp    = equal(mul(a, common), mul(c, common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize2)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(a, b);
  Node mul_cd   = mul(c, d);
  Node mul_cd_e = mul(mul_cd, e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (a * e))))
  Node mul_ae   = mul(a, e);
  Node mul_cae  = mul(c, mul_ae);
  Node mul_bcae = mul(b, mul_cae);
  Node mul1     = mul(a, mul_bcae);

  // common: abce
  // d * common = a * common
  Node common = mul(mul(a, b), mul(c, e));
  Node exp    = equal(mul(d, common), mul(a, common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize3)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_cd      = mul(c, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d, e);
  Node mul_cde  = mul(c, mul_de);
  Node mul_bcde = mul(b, mul_cde);
  Node mul1     = mul(a, mul_bcde);

  // common: (ab)cde
  // common = (ab) * common
  Node common = mul(mul(mul(a, b), e), mul(c, d));
  Node exp    = equal(common, mul(mul(a, b), common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize4)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored

  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_cd      = mul(c, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_a_cd    = mul(a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  // FIXME: expected to fail since (cd) is not properly shared

  // common: (aa)b(cd)
  // (be) * common = (cd) * common
  Node common = mul(mul(mul(a, a), b), mul(c, d));
  Node exp    = equal(mul(mul(b, e), common), mul(mul(c, d), common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize5)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored

  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_ad      = mul(a, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_cd      = mul(c, d);
  Node mul_a_cd    = mul(a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  // FIXME: expected to fail since (ab) is not properly shared

  // common: (ab)ad
  // (ab)e * common = (cc)d * common
  Node common = mul(mul(mul(a, b), a), d);
  Node exp =
      equal(mul(mul(mul(a, b), e), common), mul(mul(mul(c, c), d), common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize6)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(a, b);
  Node mul_ad      = mul(a, d);
  Node mul_e_ab    = mul(e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  // common: ((ab)(ab))a
  // (de) * common = (((ab)(ab))*((ab)(ab))) * common
  Node common = mul(mul(mul_ab, mul_ab), a);
  Node exp    = equal(mul(mul(d, e), common),
                   mul(mul(mul(mul_ab, mul_ab), mul(mul_ab, mul_ab)), common));

  test_assertion(equal(mul0, mul1), exp);
}

TEST_F(TestPassNormalize, mul_normalize7)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored

  // (a * b) * ((a + d) * (e * (a + b))
  Node mul_ab      = mul(a, b);
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node mul_e_ab    = mul(e, add_ab);
  Node mul_ad_e_ab = mul(add_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a + b) * ((c * d) * (a + (c + d))
  Node mul_cd      = mul(c, d);
  Node add_cd      = add(c, d);
  Node add_a_cd    = add(a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  Node common = add_ab;

  test_assertion(equal(mul0, mul1),
                 equal(mul(a, mul(b, mul(e, mul(common, add_ad)))),
                       mul(c, mul(d, mul(common, add_a_cd)))));
}

TEST_F(TestPassNormalize, mul_normalize8)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored
  //
  // (a * b) * ((a + d) * (e * (ite (a * b == b * a) 0 1))
  Node mul_ab = mul(a, b);
  Node add_ad = add(a, d);
  Node mul_e_ite =
      mul(e, d_nm.mk_node(Kind::ITE, {equal(mul(a, b), mul(b, a)), zero, one}));
  Node mul_ad_e_ite = mul(add_ad, mul_e_ite);
  Node mul0         = mul(mul_ab, mul_ad_e_ite);
  // (a + b) * ((c * d) * (a + (c + d))
  Node add_ab      = add(a, b);
  Node mul_cd      = mul(c, d);
  Node add_cd      = add(c, d);
  Node add_a_cd    = add(a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  test_assertion(
      equal(mul0, mul1),
      equal(mul(a,
                mul(b,
                    mul(e,
                        mul(add_ad,
                            d_nm.mk_node(Kind::ITE, {d_true, zero, one}))))),
            mul(c, mul(d, mul(add_ab, add_a_cd)))));
}

TEST_F(TestPassNormalize, mul_normalize9)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored

  // (a * b) * ((a + d) * (e * (ite (a * b == b * a) 0 1))
  Node mul_ab = mul(a, b);
  Node add_ad = add(a, d);
  Node mul_e_ite =
      mul(e, d_nm.mk_node(Kind::ITE, {equal(mul(a, b), mul(b, a)), zero, one}));
  Node mul_ad_e_ite = mul(add_ad, mul_e_ite);
  Node mul0         = mul(mul_ab, mul_ad_e_ite);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  Node common = mul_ab;

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(mul0, mul1)}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(
               mul(e,
                   mul(common,
                       mul(add_ad,
                           d_nm.mk_node(Kind::ITE, {d_true, zero, one})))),
               mul(a,
                   mul(a,
                       mul(a,
                           mul(a,
                               mul(a,
                                   mul(a,
                                       mul(b,
                                           mul(b,
                                               mul(b,
                                                   mul(b,
                                                       mul(b,
                                                           common))))))))))))}));
}

TEST_F(TestPassNormalize, mul_normalize10)
{
  GTEST_SKIP();  // FIXME: This needs to be refactored
  //
  // 2 * (a * b) * ((3 * (a * d)) * (e * (a * (5 * b)))
  Node mul_2ab       = mul(two, mul(a, b));
  Node mul_3ad       = mul(three, mul(a, d));
  Node mul_a5b       = mul(a, mul(five, b));
  Node mul_e_a5b     = mul(e, mul_a5b);
  Node mul_3ad_e_a5b = mul(mul_3ad, mul_e_a5b);
  Node mul0          = mul(mul_2ab, mul_3ad_e_a5b);
  // (a * b) * (2 * (3 * ((c * d) * (a * (c * d))))
  Node mul_ab       = mul(a, b);
  Node mul_cd       = mul(c, d);
  Node mul_a_cd     = mul(a, mul_cd);
  Node mul_6cd_a_cd = mul(two, mul(three, mul(mul_cd, mul_a_cd)));
  Node mul1         = mul(mul_ab, mul_6cd_a_cd);

  // TODO:
  // common: 6 * (ab)(ad)
  // 5 * (ab)e * common = (cc)d * common
  Node thirty = d_nm.mk_value(BitVector::from_ui(8, 30));
  Node common = mul(a, mul(mul_ab, d));
  test_assertion(equal(mul0, mul1),
                 equal(mul(a, mul(b, mul(e, mul(thirty, common)))),
                       mul(c, mul(c, mul(d, mul(six, common))))));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, add_normalize00)
{
  // (a + b) = (b + a)
  test_assertion(equal(add(a, b), add(b, a)), d_true);
}

TEST_F(TestPassNormalize, add_normalize01)
{
  // (a + b) = (b + a) + (a + b)
  test_assertion(equal(add(a, b), add(add(b, a), add(a, b))),
                 equal(zero, add(a, b)));
}

TEST_F(TestPassNormalize, add_normalize0)
{
  // (a + b) + ((c + d) + e)
  Node add_ab   = add(a, b);
  Node add_cd   = add(c, d);
  Node add_cd_e = add(add_cd, e);
  Node add0     = add(add_ab, add_cd_e);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d, e);
  Node add_cde  = add(c, add_de);
  Node add_bcde = add(b, add_cde);
  Node add1     = add(a, add_bcde);

  test_assertion(equal(add0, add1), d_true);
}

TEST_F(TestPassNormalize, add_normalize1)
{
  // (a + b) + ((a + d) + e)
  Node add_ab   = add(a, b);
  Node add_ad   = add(a, d);
  Node add_ad_e = add(add_ad, e);
  Node add0     = add(add_ab, add_ad_e);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d, e);
  Node add_cde  = add(c, add_de);
  Node add_bcde = add(b, add_cde);
  Node add1     = add(a, add_bcde);

  test_assertion(equal(add0, add1), equal(a, c));
}

TEST_F(TestPassNormalize, add_normalize2)
{
  // (a + b) + ((c + d) + e)
  Node add_ab   = add(a, b);
  Node add_cd   = add(c, d);
  Node add_cd_e = add(add_cd, e);
  Node add0     = add(add_ab, add_cd_e);
  // (a + (b + (c + (a + e))))
  Node add_ae   = add(a, e);
  Node add_cae  = add(c, add_ae);
  Node add_bcae = add(b, add_cae);
  Node add1     = add(a, add_bcae);

  test_assertion(equal(add0, add1), equal(d, a));
}

TEST_F(TestPassNormalize, add_normalize3)
{
  // (a + b) + ((c + d) + (e + (a + b))
  Node add_ab      = add(a, b);
  Node add_cd      = add(c, d);
  Node add_e_ab    = add(e, add_ab);
  Node add_cd_e_ab = add(add_cd, add_e_ab);
  Node add0        = add(add_ab, add_cd_e_ab);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d, e);
  Node add_cde  = add(c, add_de);
  Node add_bcde = add(b, add_cde);
  Node add1     = add(a, add_bcde);

  test_assertion(equal(add0, add1), equal(add(a, b), zero));
}

TEST_F(TestPassNormalize, add_normalize4)
{
  // (a + b) + ((c + d) + (e + (a + b))
  Node add_ab      = add(a, b);
  Node add_cd      = add(c, d);
  Node add_e_ab    = add(e, add_ab);
  Node add_cd_e_ab = add(add_cd, add_e_ab);
  Node add0        = add(add_ab, add_cd_e_ab);
  // (a + b) + ((c + d) + (a + (c + d))
  Node add_a_cd    = add(a, add_cd);
  Node add_cd_a_cd = add(add_cd, add_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1), equal(add(b, e), add(c, d)));
}

TEST_F(TestPassNormalize, add_normalize5)
{
  // (a + b) + ((a + d) + (e + (a + b))
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node add_e_ab    = add(e, add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + b) + ((c + d) + (a + (c + d))
  Node add_cd      = add(c, d);
  Node add_a_cd    = add(a, add_cd);
  Node add_cd_a_cd = add(add_cd, add_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1),
                 equal(add(add(a, b), e), add(d, mul(two, c))));
}

TEST_F(TestPassNormalize, add_normalize6)
{
  // (a + b) + ((a + d) + (e + (a + b))
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node add_e_ab    = add(e, add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  test_assertion(equal(add0, add1), equal(add(d, e), mul(four, add(a, b))));
}

TEST_F(TestPassNormalize, add_normalize7)
{
  // (a + b) + ((a * d) + (e + (a * b))
  Node add_ab      = add(a, b);
  Node mul_ab      = mul(a, b);
  Node mul_ad      = mul(a, d);
  Node add_e_ab    = add(e, mul_ab);
  Node add_ad_e_ab = add(mul_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a * b) + ((c + d) + (a * (c * d))
  Node add_cd      = add(c, d);
  Node mul_cd      = mul(c, d);
  Node mul_a_cd    = mul(a, mul_cd);
  Node add_cd_a_cd = add(add_cd, mul_a_cd);
  Node add1        = add(mul_ab, add_cd_a_cd);

  test_assertion(
      equal(add0, add1),
      equal(add(add(add(a, b), e), mul_ad), add(add(c, d), mul(d, mul(a, c)))));
}

TEST_F(TestPassNormalize, add_normalize8)
{
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(a, b);
  Node mul_ad = mul(a, d);
  Node ite = d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one});
  Node add_e_ite    = add(e, ite);
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + b) + ((c + d) + (a * (c * d))
  Node add_cd      = add(c, d);
  Node mul_cd      = mul(c, d);
  Node mul_a_cd    = mul(a, mul_cd);
  Node add_cd_a_cd = add(add_cd, mul_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(
      equal(add0, add1),
      equal(add(add(e, mul_ad), d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
            add(add(c, d), mul(d, mul(a, c)))));
}

TEST_F(TestPassNormalize, add_normalize9)
{
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(a, b);
  Node mul_ad = mul(a, d);
  Node add_e_ite =
      add(e, d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  Node a6 = mul(six, a);
  Node b5 = mul(five, b);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
                          add(a6, b5))}));
}

TEST_F(TestPassNormalize, add_normalize10)
{
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab          = add(a, b);
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add0            = add(add_a_ab_ab, add_ab_ab_ab_ab);
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node mul_ad = mul(a, d);
  Node add_e_ite =
      add(e, d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add1         = add(add_ab, add_ad_e_ite);

  Node a6 = mul(six, a);
  Node b5 = mul(five, b);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(a6, b5),
                          add(add(e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})))}));
}

#if 0
TEST_F(TestPassNormalize, add_normalize11)
{
  Type bv_type = d_nm.mk_bv_type(2);
  Node a       = d_nm.mk_const(bv_type, "a");
  Node b       = d_nm.mk_const(bv_type, "b");
  Node c       = d_nm.mk_const(bv_type, "c");
  Node d       = d_nm.mk_const(bv_type, "d");
  Node e       = d_nm.mk_const(bv_type, "e");
  Node zero    = d_nm.mk_value(BitVector::mk_zero(2));
  Node one     = d_nm.mk_value(BitVector::mk_one(2));
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(a, b);
  Node mul_ad = mul(a, d);
  Node add_e_ite =
      add(e, d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(add(e, mul_ad),
                     d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
                 add(b, mul(d_nm.mk_value(BitVector::from_ui(2, 2)), a)))}));
}

TEST_F(TestPassNormalize, add_normalize12)
{
  Type bv_type = d_nm.mk_bv_type(2);
  Node a       = d_nm.mk_const(bv_type, "a");
  Node b       = d_nm.mk_const(bv_type, "b");
  Node c       = d_nm.mk_const(bv_type, "c");
  Node d       = d_nm.mk_const(bv_type, "d");
  Node e       = d_nm.mk_const(bv_type, "e");
  Node zero    = d_nm.mk_value(BitVector::mk_zero(2));
  Node one     = d_nm.mk_value(BitVector::mk_one(2));
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(a, b);
  Node mul_ad = mul(a, d);
  Node ite = d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one});
  Node add_e_ite    = add(e, ite);
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + ((a + b) + (a + b))) +
  // (((a + b) + (a + b)) + (((a + b) + (a + b)) + ((a + b) + (a + b))))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_ab_ab, add(add_a_ab_ab, add_ab_ab_ab_ab));

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(add(b, e), mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
                          zero)}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(add(e, add_ab), mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
                          a)}));
}
#endif

TEST_F(TestPassNormalize, add_normalize13)
{
  // (a & b) + (a | b)
  Node and_ab = aand(a, b);
  Node or_ab  = oor(a, b);
  Node add0   = add(and_ab, or_ab);
  // a + b
  Node add1 = add(a, b);
  test_assertion(equal(add0, add1), equal(add0, add1));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, add_normalize_neg0)
{
  // (a + b) = (-b + -a)
  test_assertion(equal(add(a, b), add(neg(b), neg(a))),
                 equal(mul(two, add(a, b)), zero));
}

TEST_F(TestPassNormalize, add_normalize_neg1)
{
  // (a + b) + c = (-b + -a) + (b + c)
  test_assertion(equal(add(add(a, b), c), add(add(neg(b), neg(a)), add(b, c))),
                 equal(add(b, mul(two, a)), zero));
}

TEST_F(TestPassNormalize, add_normalize_neg2)
{
  // (a + ~b) + c + 2 = (-b + -a) + (b + c)

  // expected: 2a + 1 = b
  // actual: 2a = b - 1
  test_assertion(equal(add(add(add(a, inv(b)), c), two),
                       add(add(neg(b), neg(a)), add(b, c))),
                 equal(add(one, mul(two, a)), b));
}

TEST_F(TestPassNormalize, add_normalize_neg3)
{
  // (a + ~(b + 1)) + c + 2 = (-b + -a) + (b + c)
  test_assertion(equal(add(add(add(a, inv(add(b, one))), c), two),
                       add(add(neg(b), neg(a)), add(b, c))),
                 equal(mul(two, a), b));
}

TEST_F(TestPassNormalize, add_normalize_neg4)
{
  // (a + b) + ((a + d) + (e + ~(a + b))
  Node add_ab      = add(a, b);
  Node add_ad      = add(a, d);
  Node add_e_ab    = add(e, inv(add_ab));
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + ((a + b) + ~(a + b))) + (((a + b) + ~(a + b)) + ((a + b) + ~(a + b)))
  Node add_ab_ab       = add(add_ab, inv(add_ab));
  Node add_a_ab_ab     = add(a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  test_assertion(equal(add0, add1), equal(add(add(d, e), two), zero));
}

TEST_F(TestPassNormalize, add_normalize_neg5)
{
  // ((a + ~(a + (b + ~(a + b)))) + c)
  Node add_ab = add(a, b);
  Node add0   = add(add(a, inv(add(a, add(b, inv(add_ab))))), c);
  // (-b + ((-a + ~(b + c)) + ((b + c) + ~(a + b))))
  Node add_bc = add(b, c);
  Node add1 =
      add(neg(b), add(add(neg(a), inv(add_bc)), add(add_bc, inv(add_ab))));

  Node m3a = mul(d_nm.mk_value(BitVector::from_si(8, 3)), a);
  Node m2b = mul(d_nm.mk_value(BitVector::from_si(8, 2)), b);

  // expected: 3a 2b c == -2
  test_assertion(
      equal(add0, add1),
      equal(d_nm.mk_value(BitVector::from_si(8, -2)), add(add(m3a, m2b), c)));
}
//(not (= s (bvadd (bvadd (bvadd s t) (bvmul s t)) (bvmul t (bvnot s)))))

TEST_F(TestPassNormalize, mk_node1)
{
  PassNormalize::OccMap occs1{{a, 2}};
  Node aa = mul(a, a);
  ASSERT_EQ(d_pass->mk_node(Kind::BV_MUL, occs1), aa);

  PassNormalize::OccMap occs2{{a, 4}};
  ASSERT_EQ(d_pass->mk_node(Kind::BV_MUL, occs2), mul(aa, aa));

  PassNormalize::OccMap occs3{{a, 5}};
  ASSERT_EQ(d_pass->mk_node(Kind::BV_MUL, occs3), mul(a, mul(aa, aa)));
}

#if 0 // Disable code until new normalization code is merged back.
TEST_F(TestPassNormalize, add_normalize_ult1)
{
  // (a + b) + (c + d)
  Node ab   = add(a, b);
  Node cd   = add(c, d);
  Node add0 = add(ab, cd);
  // (d + (a + (c  + b)))
  Node cb   = add(c, b);
  Node acb  = add(a, cb);
  Node add1 = add(d, acb);

  Node exp = add(add(add(a, b), c), d);
  test_assertion(ult(add0, add1), ult(exp, exp));
}

TEST_F(TestPassNormalize, add_normalize_ult2)
{
  // (a + b) + (c + e)
  Node ab   = add(a, b);
  Node ce   = add(c, e);
  Node add0 = add(ab, ce);
  // (d + (a + (c  + b)))
  Node cb   = add(c, b);
  Node acb  = add(a, cb);
  Node add1 = add(d, acb);

  // (e + (a + b +c )) < (d + (a + b + c))
  Node lhs = add(e, add(add(a, b), c));
  Node rhs = add(d, add(add(a, b), c));

  test_assertion(ult(add0, add1), ult(lhs, rhs));
}

TEST_F(TestPassNormalize, add_normalize_ult3)
{
  // (a + 1)
  Node a1 = add(a, one);

  test_assertion(ult(a1, one), ult(a1, one));
}
#endif

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
