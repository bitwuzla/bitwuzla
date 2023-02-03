#include "gtest/gtest.h"
#include "preprocess/pass/normalize.h"
#include "rewrite/rewrites_bv.h"
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
    d_options.rewrite_level.set(0);
    d_options.pp_normalize_share_aware.set(false);
    d_env.reset(new Env(d_options));
    d_pass.reset(new PassNormalize(*d_env, &d_bm));
  };

  Node neg(const Node& a) const
  {
    return RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
               d_env->rewriter(), d_nm.mk_node(Kind::BV_NEG, {a}))
        .first;
  }

  Node inv(const Node& a) const { return d_nm.mk_node(Kind::BV_NOT, {a}); }

  Node add(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::BV_ADD, {a, b});
  }

  Node mul(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::BV_MUL, {a, b});
  }

  Node aand(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::BV_AND, {a, b});
  }

  Node oor(const Node& a, const Node& b) const
  {
    return RewriteRule<RewriteRuleKind::BV_OR_ELIM>::apply(
               d_env->rewriter(), d_nm.mk_node(Kind::BV_OR, {a, b}))
        .first;
  }

  Node equal(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::EQUAL, {a, b});
  }

  void test_compute_factors(const Node& node,
                            const std::unordered_map<Node, uint64_t>& expected,
                            bool consider_neg)
  {
    auto factors = d_pass->compute_factors(node, {}, consider_neg);
    for (auto& p : expected)
    {
      auto it = factors.find(p.first);
      if (it == factors.end())
      {
        std::cout << "missing factor for: " << p.first << std::endl;
        std::cout << "factors:" << std::endl;
        for (const auto& f : factors)
        {
          std::cout << "  " << f.first << ": " << f.second << std::endl;
        }
      }
      assert(it != factors.end());
      if (it->second != p.second)
      {
        std::cout << it->first << " with " << it->second
                  << ", expected: " << p.second << std::endl;
        for (auto& f : factors)
        {
          std::cout << " - " << f.first << ": " << f.second << std::endl;
        }
      }
      ASSERT_EQ(it->second, p.second);
    }
  }

  void test_compute_factors(const Node& node,
                            const std::unordered_map<Node, uint64_t>& expected0,
                            const std::unordered_map<Node, uint64_t>& expected1,
                            bool consider_neg)
  {
    auto factors0 = d_pass->compute_factors(node[0], {}, consider_neg);
    auto factors1 = d_pass->compute_factors(node[1], {}, consider_neg);
    const std::unordered_map<Node, uint64_t>* factors[2]{&factors0, &factors1};
    const std::unordered_map<Node, uint64_t>* expected[2]{&expected0,
                                                          &expected1};
    for (size_t i = 0; i < 2; ++i)
    {
      for (auto& p : *expected[i])
      {
        auto it = factors[i]->find(p.first);
        if (it == factors[i]->end())
        {
          std::cout << "missing factor for: " << p.first << std::endl;
        }
        assert(it != factors[i]->end());
        if (it->second != p.second)
        {
          std::cout << "factors" << i << ": " << it->first << " with "
                    << it->second << ", expected: " << p.second << std::endl;
          for (auto& f : *factors[i])
          {
            std::cout << " - " << f.first << ": " << f.second << std::endl;
          }
        }
        ASSERT_EQ(it->second, p.second);
      }
    }
  }

  void test_assertion(const Node& node,
                      const Node& expected,
                      const Node& expected_shares)
  {
    {
      AssertionStack as;
      as.push_back(node);
      ASSERT_EQ(as.size(), 1);
      preprocess::AssertionVector assertions(as.view());
      d_pass->apply(assertions);
      ASSERT_EQ(as.size(), 1);
      ASSERT_EQ(as[0], expected);
    }

    if (!expected_shares.is_null())
    {
      d_options.pp_normalize_share_aware.set(true);
      d_env.reset(new Env(d_options));
      d_pass.reset(new PassNormalize(*d_env, &d_bm));
      AssertionStack as;
      as.push_back(node);
      ASSERT_EQ(as.size(), 1);
      preprocess::AssertionVector assertions(as.view());
      d_pass->apply(assertions);
      ASSERT_EQ(as.size(), 1);
      ASSERT_EQ(as[0], expected_shares);
    }
  }

  Type d_bv_type = d_nm.mk_bv_type(8);
  Node d_a       = d_nm.mk_const(d_bv_type, "a");
  Node d_b       = d_nm.mk_const(d_bv_type, "b");
  Node d_c       = d_nm.mk_const(d_bv_type, "c");
  Node d_d       = d_nm.mk_const(d_bv_type, "d");
  Node d_e       = d_nm.mk_const(d_bv_type, "e");
  Node d_one     = d_nm.mk_value(BitVector::mk_one(8));
  Node d_zero    = d_nm.mk_value(BitVector::mk_zero(8));
  Node d_two     = d_nm.mk_value(BitVector::from_ui(8, 2));
  Node d_four    = d_nm.mk_value(BitVector::from_ui(8, 4));
  Node d_five    = d_nm.mk_value(BitVector::from_ui(8, 5));
  Node d_six     = d_nm.mk_value(BitVector::from_ui(8, 6));
  Node d_true    = d_nm.mk_value(true);

  std::unique_ptr<preprocess::pass::PassNormalize> d_pass;
  std::unique_ptr<Env> d_env;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, compute_factors0)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_cd   = mul(d_c, d_d);
  Node mul_cd_e = mul(mul_cd, d_e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors1)
{
  // (a * b) * ((a * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_ad   = mul(d_a, d_d);
  Node mul_ad_e = mul(mul_ad, d_e);
  Node mul0     = mul(mul_ab, mul_ad_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 2}, {d_b, 1}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors2)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_cd   = mul(d_c, d_d);
  Node mul_cd_e = mul(mul_cd, d_e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (a * e))))
  Node mul_ae   = mul(d_a, d_e);
  Node mul_cae  = mul(d_c, mul_ae);
  Node mul_bcae = mul(d_b, mul_cae);
  Node mul1     = mul(d_a, mul_bcae);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 2}, {d_b, 1}, {d_c, 1}, {d_e, 1}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors3)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 2}, {d_b, 2}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors4)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 2}, {d_b, 2}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 2}, {d_b, 1}, {d_c, 2}, {d_d, 2}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors5)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_ad      = mul(d_a, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_cd      = mul(d_c, d_d);
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 3}, {d_b, 2}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 2}, {d_b, 1}, {d_c, 2}, {d_d, 2}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors6)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_ad      = mul(d_a, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(d_a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 3}, {d_b, 2}, {d_d, 1}, {d_e, 1}},
                       {{d_a, 7}, {d_b, 6}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors7)
{
  // (a * b) * ((a + d) * (e * (a + b))
  Node mul_ab      = mul(d_a, d_b);
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node mul_e_ab    = mul(d_e, add_ab);
  Node mul_ad_e_ab = mul(add_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a + b) * ((c * d) * (a + (c + d))
  Node mul_cd      = mul(d_c, d_d);
  Node add_cd      = add(d_c, d_d);
  Node add_a_cd    = add(d_a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  test_compute_factors(equal(mul0, mul1),
                       {{d_a, 1}, {d_b, 1}, {d_e, 1}},
                       {{d_c, 1}, {d_d, 1}},
                       false);
}

TEST_F(TestPassNormalize, compute_factors_neg0)
{
  // (a + b) + ((-a + d) + (-e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(neg(d_a), d_d);
  Node add_e_ab    = add(neg(d_e), add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_factors(
      add0,
      {{d_a, 2}, {inv(d_a), 1}, {d_b, 2}, {inv(d_e), 1}, {d_one, 2}},
      true);
}

TEST_F(TestPassNormalize, compute_factors_neg1)
{
  // (a + b) + (-(a + d) + (e + -(a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node add_e_ab    = add(d_e, neg(add_ab));
  Node add_ad_e_ab = add(neg(add_ad), add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_factors(add0,
                       {{d_a, UINT64_MAX},
                        {d_b, 0},
                        {d_e, 1},
                        {d_one, 2},
                        {d_nm.mk_value(BitVector::mk_ones(8).ibvdec()), 1}},
                       true);
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, mul_normalize00)
{
  // (a * b) = (b * a)
  test_assertion(equal(mul(d_a, d_b), mul(d_b, d_a)), d_true, d_true);
}

TEST_F(TestPassNormalize, mul_normalize01)
{
  // (a * b) = (b * a) * (a * b)
  test_assertion(equal(mul(d_a, d_b), mul(mul(d_b, d_a), mul(d_a, d_b))),
                 equal(d_one, mul(d_a, d_b)),
                 equal(d_one, mul(d_a, d_b)));
}

TEST_F(TestPassNormalize, mul_normalize0)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_cd   = mul(d_c, d_d);
  Node mul_cd_e = mul(mul_cd, d_e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_assertion(equal(mul0, mul1), d_true, d_true);
}

TEST_F(TestPassNormalize, mul_normalize1)
{
  // (a * b) * ((a * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_ad   = mul(d_a, d_d);
  Node mul_ad_e = mul(mul_ad, d_e);
  Node mul0     = mul(mul_ab, mul_ad_e);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_assertion(equal(mul0, mul1), equal(d_a, d_c), equal(d_a, d_c));
}

TEST_F(TestPassNormalize, mul_normalize2)
{
  // (a * b) * ((c * d) * e)
  Node mul_ab   = mul(d_a, d_b);
  Node mul_cd   = mul(d_c, d_d);
  Node mul_cd_e = mul(mul_cd, d_e);
  Node mul0     = mul(mul_ab, mul_cd_e);
  // (a * (b * (c * (a * e))))
  Node mul_ae   = mul(d_a, d_e);
  Node mul_cae  = mul(d_c, mul_ae);
  Node mul_bcae = mul(d_b, mul_cae);
  Node mul1     = mul(d_a, mul_bcae);

  test_assertion(equal(mul0, mul1), equal(d_d, d_a), equal(d_d, d_a));
}

TEST_F(TestPassNormalize, mul_normalize3)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * (b * (c * (d * e))))
  Node mul_de   = mul(d_d, d_e);
  Node mul_cde  = mul(d_c, mul_de);
  Node mul_bcde = mul(d_b, mul_cde);
  Node mul1     = mul(d_a, mul_bcde);

  test_assertion(equal(mul0, mul1),
                 equal(mul(d_a, d_b), d_one),
                 equal(mul(d_a, d_b), d_one));
}

TEST_F(TestPassNormalize, mul_normalize4)
{
  // (a * b) * ((c * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_cd_e_ab = mul(mul_cd, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_cd_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_assertion(equal(mul0, mul1),
                 equal(mul(d_b, d_e), mul(d_c, d_d)),
                 equal(mul(d_b, d_e), mul(d_c, d_d)));
}

TEST_F(TestPassNormalize, mul_normalize5)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_ad      = mul(d_a, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * b) * ((c * d) * (a * (c * d))
  Node mul_cd      = mul(d_c, d_d);
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node mul_cd_a_cd = mul(mul_cd, mul_a_cd);
  Node mul1        = mul(mul_ab, mul_cd_a_cd);

  test_assertion(equal(mul0, mul1),
                 equal(mul(d_a, mul(d_b, d_e)), mul(d_c, mul(d_c, d_d))),
                 equal(mul(d_a, mul(d_b, d_e)), mul(d_c, mul(d_c, d_d))));
}

TEST_F(TestPassNormalize, mul_normalize6)
{
  // (a * b) * ((a * d) * (e * (a * b))
  Node mul_ab      = mul(d_a, d_b);
  Node mul_ad      = mul(d_a, d_d);
  Node mul_e_ab    = mul(d_e, mul_ab);
  Node mul_ad_e_ab = mul(mul_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(d_a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  test_assertion(
      equal(mul0, mul1),
      equal(
          mul(d_d, d_e),
          mul(d_a,
              mul(d_a, mul(d_a, mul(d_a, mul(d_b, mul(d_b, mul(d_b, d_b)))))))),
      equal(mul(d_d, d_e),
            mul(d_a,
                mul(d_a,
                    mul(d_a, mul(d_a, mul(d_b, mul(d_b, mul(d_b, d_b)))))))));
}

TEST_F(TestPassNormalize, mul_normalize7)
{
  // (a * b) * ((a + d) * (e * (a + b))
  Node mul_ab      = mul(d_a, d_b);
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node mul_e_ab    = mul(d_e, add_ab);
  Node mul_ad_e_ab = mul(add_ad, mul_e_ab);
  Node mul0        = mul(mul_ab, mul_ad_e_ab);
  // (a + b) * ((c * d) * (a + (c + d))
  Node mul_cd      = mul(d_c, d_d);
  Node add_cd      = add(d_c, d_d);
  Node add_a_cd    = add(d_a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  test_assertion(equal(mul0, mul1), equal(mul0, mul1), equal(mul0, mul1));
}

TEST_F(TestPassNormalize, mul_normalize8)
{
  // (a * b) * ((a + d) * (e * (ite (a * b == b * a) 0 1))
  Node mul_ab = mul(d_a, d_b);
  Node add_ad = add(d_a, d_d);
  Node mul_e_ite =
      mul(d_e,
          d_nm.mk_node(Kind::ITE,
                       {equal(mul(d_a, d_b), mul(d_b, d_a)), d_zero, d_one}));
  Node mul_ad_e_ite = mul(add_ad, mul_e_ite);
  Node mul0         = mul(mul_ab, mul_ad_e_ite);
  // (a + b) * ((c * d) * (a + (c + d))
  Node add_ab      = add(d_a, d_b);
  Node mul_cd      = mul(d_c, d_d);
  Node add_cd      = add(d_c, d_d);
  Node add_a_cd    = add(d_a, add_cd);
  Node mul_cd_a_cd = mul(mul_cd, add_a_cd);
  Node mul1        = mul(add_ab, mul_cd_a_cd);

  test_assertion(
      equal(mul0, mul1),
      equal(
          mul(mul_ab,
              mul(add_ad,
                  mul(d_e, d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})))),
          mul1),
      equal(mul0, mul1));
}

TEST_F(TestPassNormalize, mul_normalize9)
{
  // (a * b) * ((a + d) * (e * (ite (a * b == b * a) 0 1))
  Node mul_ab = mul(d_a, d_b);
  Node add_ad = add(d_a, d_d);
  Node mul_e_ite =
      mul(d_e,
          d_nm.mk_node(Kind::ITE,
                       {equal(mul(d_a, d_b), mul(d_b, d_a)), d_zero, d_one}));
  Node mul_ad_e_ite = mul(add_ad, mul_e_ite);
  Node mul0         = mul(mul_ab, mul_ad_e_ite);
  // (a * ((a * b) * (a * b))) * (((a * b) * (a * b)) * ((a * b) * (a * b)))
  Node mul_ab_ab       = mul(mul_ab, mul_ab);
  Node mul_a_ab_ab     = mul(d_a, mul_ab_ab);
  Node mul_ab_ab_ab_ab = mul(mul_ab_ab, mul_ab_ab);
  Node mul1            = mul(mul_a_ab_ab, mul_ab_ab_ab_ab);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(mul0, mul1)}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(mul(d_e,
                     mul(add_ad,
                         d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one}))),
                 mul(d_a,
                     mul(d_a,
                         mul(d_a,
                             mul(d_a,
                                 mul(d_a,
                                     mul(d_a,
                                         mul(d_b,
                                             mul(d_b,
                                                 mul(d_b,
                                                     mul(d_b, d_b)))))))))))}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(mul(d_e,
                     mul(add_ad,
                         d_nm.mk_node(Kind::ITE,
                                      {equal(mul(d_a, d_b), mul(d_b, d_a)),
                                       d_zero,
                                       d_one}))),
                 mul(d_a,
                     mul(mul_ab,
                         mul(mul_ab, mul(mul_ab, mul(mul_ab, mul_ab))))))}));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, add_normalize00)
{
  // (a + b) = (b + a)
  test_assertion(equal(add(d_a, d_b), add(d_b, d_a)), d_true, d_true);
}

TEST_F(TestPassNormalize, add_normalize01)
{
  // (a + b) = (b + a) + (a + b)
  test_assertion(equal(add(d_a, d_b), add(add(d_b, d_a), add(d_a, d_b))),
                 equal(d_zero, add(d_a, d_b)),
                 equal(d_zero, add(d_a, d_b)));
}

TEST_F(TestPassNormalize, add_normalize0)
{
  // (a + b) + ((c + d) + e)
  Node add_ab   = add(d_a, d_b);
  Node add_cd   = add(d_c, d_d);
  Node add_cd_e = add(add_cd, d_e);
  Node add0     = add(add_ab, add_cd_e);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d_d, d_e);
  Node add_cde  = add(d_c, add_de);
  Node add_bcde = add(d_b, add_cde);
  Node add1     = add(d_a, add_bcde);

  test_assertion(equal(add0, add1), d_true, d_true);
}

TEST_F(TestPassNormalize, add_normalize1)
{
  // (a + b) + ((a + d) + e)
  Node add_ab   = add(d_a, d_b);
  Node add_ad   = add(d_a, d_d);
  Node add_ad_e = add(add_ad, d_e);
  Node add0     = add(add_ab, add_ad_e);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d_d, d_e);
  Node add_cde  = add(d_c, add_de);
  Node add_bcde = add(d_b, add_cde);
  Node add1     = add(d_a, add_bcde);

  test_assertion(equal(add0, add1), equal(d_a, d_c), equal(d_a, d_c));
}

TEST_F(TestPassNormalize, add_normalize2)
{
  // (a + b) + ((c + d) + e)
  Node add_ab   = add(d_a, d_b);
  Node add_cd   = add(d_c, d_d);
  Node add_cd_e = add(add_cd, d_e);
  Node add0     = add(add_ab, add_cd_e);
  // (a + (b + (c + (a + e))))
  Node add_ae   = add(d_a, d_e);
  Node add_cae  = add(d_c, add_ae);
  Node add_bcae = add(d_b, add_cae);
  Node add1     = add(d_a, add_bcae);

  test_assertion(equal(add0, add1), equal(d_d, d_a), equal(d_d, d_a));
}

TEST_F(TestPassNormalize, add_normalize3)
{
  // (a + b) + ((c + d) + (e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_cd      = add(d_c, d_d);
  Node add_e_ab    = add(d_e, add_ab);
  Node add_cd_e_ab = add(add_cd, add_e_ab);
  Node add0        = add(add_ab, add_cd_e_ab);
  // (a + (b + (c + (d + e))))
  Node add_de   = add(d_d, d_e);
  Node add_cde  = add(d_c, add_de);
  Node add_bcde = add(d_b, add_cde);
  Node add1     = add(d_a, add_bcde);

  test_assertion(equal(add0, add1),
                 equal(add(d_a, d_b), d_zero),
                 equal(add(d_a, d_b), d_zero));
}

TEST_F(TestPassNormalize, add_normalize4)
{
  // (a + b) + ((c + d) + (e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_cd      = add(d_c, d_d);
  Node add_e_ab    = add(d_e, add_ab);
  Node add_cd_e_ab = add(add_cd, add_e_ab);
  Node add0        = add(add_ab, add_cd_e_ab);
  // (a + b) + ((c + d) + (a + (c + d))
  Node add_a_cd    = add(d_a, add_cd);
  Node add_cd_a_cd = add(add_cd, add_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1),
                 equal(add(d_b, d_e), add(d_c, d_d)),
                 equal(add(d_b, d_e), add(d_c, d_d)));
}

TEST_F(TestPassNormalize, add_normalize5)
{
  // (a + b) + ((a + d) + (e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node add_e_ab    = add(d_e, add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + b) + ((c + d) + (a + (c + d))
  Node add_cd      = add(d_c, d_d);
  Node add_a_cd    = add(d_a, add_cd);
  Node add_cd_a_cd = add(add_cd, add_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1),
                 equal(add(add(d_a, d_b), d_e), add(d_d, mul(d_two, d_c))),
                 equal(add(add(d_a, d_b), d_e), add(d_d, mul(d_two, d_c))));
}

TEST_F(TestPassNormalize, add_normalize6)
{
  // (a + b) + ((a + d) + (e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node add_e_ab    = add(d_e, add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(d_a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  Node a4 = mul(d_four, d_a);
  Node b4 = mul(d_four, d_b);

  test_assertion(equal(add0, add1),
                 equal(add(d_d, d_e), add(a4, b4)),
                 equal(add(d_d, d_e), add(a4, b4)));
}

TEST_F(TestPassNormalize, add_normalize7)
{
  // (a + b) + ((a * d) + (e + (a * b))
  Node add_ab      = add(d_a, d_b);
  Node mul_ab      = mul(d_a, d_b);
  Node mul_ad      = mul(d_a, d_d);
  Node add_e_ab    = add(d_e, mul_ab);
  Node add_ad_e_ab = add(mul_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a * b) + ((c + d) + (a * (c * d))
  Node add_cd      = add(d_c, d_d);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node add_cd_a_cd = add(add_cd, mul_a_cd);
  Node add1        = add(mul_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1), equal(add0, add1), equal(add0, add1));
}

TEST_F(TestPassNormalize, add_normalize8)
{
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(d_a, d_b);
  Node mul_ad = mul(d_a, d_d);
  Node add_e_ite =
      add(d_e,
          d_nm.mk_node(Kind::ITE,
                       {equal(add(d_a, d_b), add(d_b, d_a)), d_zero, d_one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + b) * ((c * d) * (a + (c + d))
  Node mul_ab      = mul(d_a, d_b);
  Node add_cd      = add(d_c, d_d);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node add_cd_a_cd = add(add_cd, mul_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(
      equal(add0, add1),
      equal(
          add(add_ab,
              add(mul_ad,
                  add(d_e, d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})))),
          add1),
      equal(add0, add1));
}

TEST_F(TestPassNormalize, add_normalize9)
{
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(d_a, d_b);
  Node mul_ad = mul(d_a, d_d);
  Node add_e_ite =
      add(d_e,
          d_nm.mk_node(Kind::ITE,
                       {equal(add(d_a, d_b), add(d_b, d_a)), d_zero, d_one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(d_a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  Node a6 = mul(d_six, d_a);
  Node b5 = mul(d_five, d_b);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(d_e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})),
                          add(a6, b5))}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(add(d_e, mul_ad),
                     d_nm.mk_node(
                         Kind::ITE,
                         {equal(add(d_a, d_b), add(d_b, d_a)), d_zero, d_one})),
                 add(d_a, mul(d_five, add_ab)))}));
}

TEST_F(TestPassNormalize, add_normalize10)
{
  // (a + ((a + b) + (a + b))) + (((a + b) + (a + b)) + ((a + b) + (a + b)))
  Node add_ab          = add(d_a, d_b);
  Node add_ab_ab       = add(add_ab, add_ab);
  Node add_a_ab_ab     = add(d_a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add0            = add(add_a_ab_ab, add_ab_ab_ab_ab);
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node mul_ad = mul(d_a, d_d);
  Node add_e_ite =
      add(d_e,
          d_nm.mk_node(Kind::ITE,
                       {equal(add(d_a, d_b), add(d_b, d_a)), d_zero, d_one}));
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add1         = add(add_ab, add_ad_e_ite);

  Node a6 = mul(d_six, d_a);
  Node b5 = mul(d_five, d_b);

  test_assertion(
      d_nm.mk_node(Kind::AND, {d_true, equal(add0, add1)}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(a6, b5),
                 add(add(d_e, mul_ad),
                     d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})))}),
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(d_a, mul(d_five, add_ab)),
                          add(add(d_e, mul_ad),
                              d_nm.mk_node(Kind::ITE,
                                           {equal(add(d_a, d_b), add(d_b, d_a)),
                                            d_zero,
                                            d_one})))}));
}

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
                 add(b, mul(d_nm.mk_value(BitVector::from_ui(2, 2)), a)))}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(add(e, mul_ad),
                     d_nm.mk_node(Kind::ITE,
                                  {equal(add(a, b), add(b, a)), zero, one})),
                 add(a, add_ab))}));
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
  Node add_e_ite =
      add(e, d_nm.mk_node(Kind::ITE, {equal(add(a, b), add(b, a)), zero, one}));
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
                    equal(add(add(e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
                          add(inv(b), one))}),
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(add(e, mul_ad),
                     d_nm.mk_node(Kind::ITE,
                                  {equal(add(a, b), add(b, a)), zero, one})),
                 add(a, add(inv(add_ab), one)))}));
}

TEST_F(TestPassNormalize, add_normalize13)
{
  // (a & b) + (a | b)
  Node and_ab = aand(d_a, d_b);
  Node or_ab  = oor(d_a, d_b);
  Node add0   = add(and_ab, or_ab);
  // s + t
  Node add1 = add(d_a, d_b);
  test_assertion(equal(add0, add1),
                 equal(add(and_ab, d_nm.mk_value(BitVector::mk_ones(8))),
                       add(add(d_a, d_b), aand(inv(d_a), inv(d_b)))),
                 equal(add(and_ab, d_nm.mk_value(BitVector::mk_ones(8))),
                       add(add(d_a, d_b), aand(inv(d_a), inv(d_b)))));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, add_normalize_neg0)
{
  // (a + b) = (-b + -a)
  Node a2 = mul(d_two, d_a);
  Node b2 = mul(d_two, d_b);
  test_assertion(equal(add(d_a, d_b), add(neg(d_b), neg(d_a))),
                 equal(add(a2, b2), d_zero),
                 equal(add(a2, b2), d_zero));
}

TEST_F(TestPassNormalize, add_normalize_neg1)
{
  // (a + b) + c = (-b + -a) + (b + c)
  test_assertion(equal(add(add(d_a, d_b), d_c),
                       add(add(neg(d_b), neg(d_a)), add(d_b, d_c))),
                 equal(add(d_b, mul(d_two, d_a)), d_zero),
                 equal(add(d_b, mul(d_two, d_a)), d_zero));
}

TEST_F(TestPassNormalize, add_normalize_neg2)
{
  // (a + ~b) + c + 2 = (-b + -a) + (b + c)
  test_assertion(equal(add(add(add(d_a, inv(d_b)), d_c), d_two),
                       add(add(neg(d_b), neg(d_a)), add(d_b, d_c))),
                 equal(add(d_one, mul(d_two, d_a)), d_b),
                 equal(add(d_one, mul(d_two, d_a)), d_b));
}

TEST_F(TestPassNormalize, add_normalize_neg3)
{
  // (a + ~(b + 1)) + c + 2 = (-b + -a) + (b + c)
  test_assertion(equal(add(add(add(d_a, inv(add(d_b, d_one))), d_c), d_two),
                       add(add(neg(d_b), neg(d_a)), add(d_b, d_c))),
                 equal(add(mul(d_two, d_a), add(inv(d_b), d_one)), d_zero),
                 equal(add(mul(d_two, d_a), add(inv(d_b), d_one)), d_zero));
}

TEST_F(TestPassNormalize, add_normalize_neg4)
{
  // (a + b) + ((a + d) + (e + ~(a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node add_e_ab    = add(d_e, inv(add_ab));
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);
  // (a + ((a + b) + ~(a + b))) + (((a + b) + ~(a + b)) + ((a + b) + ~(a + b)))
  Node add_ab_ab       = add(add_ab, inv(add_ab));
  Node add_a_ab_ab     = add(d_a, add_ab_ab);
  Node add_ab_ab_ab_ab = add(add_ab_ab, add_ab_ab);
  Node add1            = add(add_a_ab_ab, add_ab_ab_ab_ab);

  test_assertion(equal(add0, add1),
                 equal(add(add(d_d, d_e), d_two), d_zero),
                 equal(add(add(d_d, d_e), d_two), d_zero));
}

//(not (= s (bvadd (bvadd (bvadd s t) (bvmul s t)) (bvmul t (bvnot s)))))

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
