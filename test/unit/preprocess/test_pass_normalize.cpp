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

  void test_compute_coefficients(
      const Node& node,
      const std::unordered_map<Node, int64_t>& expected,
      bool consider_neg)
  {
    PassNormalize::CoefficientsMap coeffs;
    d_pass->compute_coefficients(node, {}, coeffs);

    if (consider_neg)
    {
      if (node.kind() == Kind::BV_ADD)
      {
        auto value = d_pass->normalize_add(node, coeffs);
        if (!value.is_zero())
        {
          auto [it, inserted] = coeffs.emplace(
              d_nm.mk_value(value), BitVector::mk_one(node.type().bv_size()));
          if (!inserted)
          {
            it->second.ibvinc();
          }
        }
      }
    }
    for (auto& p : expected)
    {
      auto it = coeffs.find(p.first);
      if (it == coeffs.end())
      {
        std::cout << "missing factor for: " << p.first << std::endl;
        std::cout << "coeffs:" << std::endl;
        for (const auto& f : coeffs)
        {
          std::cout << "  " << f.first << ": "
                    << ((int64_t) f.second.bvsext(64 - f.second.size())
                            .to_uint64(true))
                    << std::endl;
        }
      }
      ASSERT_TRUE(it != coeffs.end());
      assert(it->second.size() < 64);
      int64_t factor =
          it->second.bvsext(64 - it->second.size()).to_uint64(true);
      if (factor != p.second)
      {
        std::cout << it->first << " with " << factor
                  << ", expected: " << p.second << std::endl;
        for (auto& f : coeffs)
        {
          std::cout << " - " << f.first << ": "
                    << ((int64_t) f.second.bvsext(64 - f.second.size())
                            .to_uint64(true))
                    << std::endl;
        }
      }
      ASSERT_EQ(factor, p.second);
    }

    for (auto& p : coeffs)
    {
      auto it = expected.find(p.first);
      if (it == expected.end())
      {
        std::cout << "computed factor for: " << p.first << std::endl;
        for (const auto& f : coeffs)
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

  void test_compute_coefficients(
      const Node& node,
      const std::unordered_map<Node, int64_t>& expected0,
      const std::unordered_map<Node, int64_t>& expected1,
      bool consider_neg)
  {
    PassNormalize::CoefficientsMap coeffs0, coeffs1;
    d_pass->compute_coefficients(node[0], {}, coeffs0);
    d_pass->compute_coefficients(node[1], {}, coeffs1);

    test_compute_coefficients(node[0], expected0, consider_neg);
    test_compute_coefficients(node[1], expected1, consider_neg);
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
  Node d_ones    = d_nm.mk_value(BitVector::mk_ones(8));
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

TEST_F(TestPassNormalize, compute_coefficients0)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients1)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 2}, {d_b, 1}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients2)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 2}, {d_b, 1}, {d_c, 1}, {d_e, 1}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients3)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 2}, {d_b, 2}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 1}, {d_b, 1}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients4)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 2}, {d_b, 2}, {d_c, 1}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 2}, {d_b, 1}, {d_c, 2}, {d_d, 2}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients5)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 3}, {d_b, 2}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 2}, {d_b, 1}, {d_c, 2}, {d_d, 2}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients6)
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

  test_compute_coefficients(equal(mul0, mul1),
                            {{d_a, 3}, {d_b, 2}, {d_d, 1}, {d_e, 1}},
                            {{d_a, 7}, {d_b, 6}},
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients7)
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

  test_compute_coefficients(
      equal(mul0, mul1),
      {{d_a, 1}, {d_b, 1}, {d_e, 1}, {add_ab, 1}, {add_ad, 1}},
      {{d_c, 1}, {d_d, 1}, {add_ab, 1}, {add_a_cd, 1}},
      false);
}

TEST_F(TestPassNormalize, compute_coefficients8)
{
  Node add_ab   = add(d_a, d_b);
  Node add_abc  = add(add_ab, d_c);
  Node add_2abc = add(add_abc, add_abc);
  Node add0     = add(add_2abc, add_ab);

  test_compute_coefficients(add0,
                            {
                                {d_a, 3},
                                {d_b, 3},
                                {d_c, 2},
                            },
                            false);
}

TEST_F(TestPassNormalize, compute_coefficients_neg0)
{
  // (a + b) + ((-a + d) + (-e + (a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(neg(d_a), d_d);
  Node add_e_ab    = add(neg(d_e), add_ab);
  Node add_ad_e_ab = add(add_ad, add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_coefficients(add0,
                            {{d_a, 2},
                             {inv(d_a), 1},
                             {d_b, 2},
                             {d_d, 1},
                             {inv(d_e), 1},
                             {d_one, 0},
                             {d_two, 1}},
                            true);
}

TEST_F(TestPassNormalize, compute_coefficients_neg1)
{
  // (a + b) + (-(a + d) + (e + -(a + b))
  Node add_ab      = add(d_a, d_b);
  Node add_ad      = add(d_a, d_d);
  Node add_e_ab    = add(d_e, neg(add_ab));
  Node add_ad_e_ab = add(neg(add_ad), add_e_ab);
  Node add0        = add(add_ab, add_ad_e_ab);

  test_compute_coefficients(add0,
                            {{d_a, -1},
                             {d_b, 0},
                             {d_d, -1},
                             {d_e, 1},
                             {d_one, 0},
                             {inv(add_ab), 0},
                             {inv(add_ad), 0}},
                            true);
}

TEST_F(TestPassNormalize, compute_coefficients_neg2)
{
  // -(a + (b + c))
  Node add_bc      = add(d_b, d_c);
  Node add_abc     = add(d_a, add_bc);
  Node neg_add_abc = neg(add_abc);

  test_compute_coefficients(neg_add_abc,
                            {
                                {d_a, -1},
                                {d_b, -1},
                                {d_c, -1},
                                {d_one, 0},
                                {inv(add_abc), 0},
                            },
                            true);
}

TEST_F(TestPassNormalize, compute_coefficients_neg3)
{
  // (a + b) + ~(a + b)
  Node add_ab = add(d_a, d_b);

  test_compute_coefficients(add(add_ab, inv(add_ab)),
                            {
                                {d_a, 0},
                                {d_b, 0},
                                {inv(add_ab), 0},
                                {d_ones, 1},
                                {inv(add_ab), 0},
                            },
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

  test_assertion(
      equal(mul0, mul1),
      equal(mul(d_a, mul(d_b, mul(d_e, add_ad))), mul(d_c, mul(d_d, add_a_cd))),
      equal(mul(d_a, mul(d_b, mul(d_e, add_ad))),
            mul(d_c, mul(d_d, add_a_cd))));
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
          mul(d_a,
              mul(d_b,
                  mul(d_e,
                      mul(add_ad,
                          d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one}))))),
          mul(d_c, mul(d_d, mul(add_ab, add_a_cd)))),
      equal(mul(d_e,
                mul(mul_ab,
                    mul(add_ad,
                        d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})))),
            mul(d_c, mul(d_d, mul(add_ab, add_a_cd)))));
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
                         d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one}))),
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

  test_assertion(
      equal(add0, add1),
      equal(add(add(add(d_a, d_b), d_e), mul_ad), add(add(d_c, d_d), mul_a_cd)),
      equal(add(add(add(d_a, d_b), d_e), mul_ad),
            add(add(d_c, d_d), mul_a_cd)));
}

TEST_F(TestPassNormalize, add_normalize8)
{
  // (a + b) + ((a * d) + (e + (ite (a + b == b + a) 0 1))
  Node add_ab = add(d_a, d_b);
  Node mul_ad = mul(d_a, d_d);
  Node ite          = d_nm.mk_node(Kind::ITE,
                          {equal(add(d_a, d_b), add(d_b, d_a)), d_zero, d_one});
  Node add_e_ite    = add(d_e, ite);
  Node add_ad_e_ite = add(mul_ad, add_e_ite);
  Node add0         = add(add_ab, add_ad_e_ite);
  // (a + b) + ((c + d) + (a * (c * d))
  Node add_cd      = add(d_c, d_d);
  Node mul_cd      = mul(d_c, d_d);
  Node mul_a_cd    = mul(d_a, mul_cd);
  Node add_cd_a_cd = add(add_cd, mul_a_cd);
  Node add1        = add(add_ab, add_cd_a_cd);

  test_assertion(equal(add0, add1),
                 equal(add(add(d_e, mul_ad),
                           d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})),
                       add(add(d_c, d_d), mul_a_cd)),
                 equal(add(add(d_e, mul_ad),
                           d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})),
                       add(add(d_c, d_d), mul_a_cd)));
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
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(d_e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})),
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
      d_nm.mk_node(
          Kind::AND,
          {d_true,
           equal(add(d_a, mul(d_five, add_ab)),
                 add(add(d_e, mul_ad),
                     d_nm.mk_node(Kind::ITE, {d_true, d_zero, d_one})))}));
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
      d_nm.mk_node(Kind::AND,
                   {d_true,
                    equal(add(add(e, mul_ad),
                              d_nm.mk_node(Kind::ITE, {d_true, zero, one})),
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

TEST_F(TestPassNormalize, add_normalize13)
{
  // (a & b) + (a | b)
  Node and_ab = aand(d_a, d_b);
  Node or_ab  = oor(d_a, d_b);
  Node add0   = add(and_ab, or_ab);
  // s + t
  Node add1 = add(d_a, d_b);
  test_assertion(
      equal(add0, add1),
      equal(add(d_ones, and_ab), add(add(d_a, d_b), aand(inv(d_a), inv(d_b)))),
      equal(add(d_ones, and_ab), add(add(d_a, d_b), aand(inv(d_a), inv(d_b)))));
}

/* -------------------------------------------------------------------------- */

#if 0
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
#endif

//(not (= s (bvadd (bvadd (bvadd s t) (bvmul s t)) (bvmul t (bvnot s)))))

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
