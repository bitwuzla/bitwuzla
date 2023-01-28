#include "gtest/gtest.h"
#include "preprocess/pass/normalize.h"
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
    d_env.reset(new Env(d_options));
    d_pass.reset(new PassNormalize(*d_env, &d_bm));
  };

  Node add(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::BV_ADD, {a, b});
  }

  Node mul(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::BV_MUL, {a, b});
  }

  Node equal(const Node& a, const Node& b) const
  {
    return d_nm.mk_node(Kind::EQUAL, {a, b});
  }

  void test_compute_factors(const Node& node,
                            const unordered_node_ref_map<uint64_t>& expected0,
                            const unordered_node_ref_map<uint64_t>& expected1)
  {
    auto factors0 = PassNormalize::compute_factors(node[0]);
    auto factors1 = PassNormalize::compute_factors(node[1]);
    const unordered_node_ref_map<uint64_t>* factors[2]{&factors0, &factors1};
    const unordered_node_ref_map<uint64_t>* expected[2]{&expected0, &expected1};
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

  void test_assertion(const Node& node, const Node& expected)
  {
    AssertionStack as;
    as.push_back(node);
    ASSERT_EQ(as.size(), 1);

    preprocess::AssertionVector assertions(as.view());
    d_pass->apply(assertions);

    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], expected);
  }

  Type d_bv_type = d_nm.mk_bv_type(8);
  Node d_a       = d_nm.mk_const(d_bv_type, "a");
  Node d_b       = d_nm.mk_const(d_bv_type, "b");
  Node d_c       = d_nm.mk_const(d_bv_type, "c");
  Node d_d       = d_nm.mk_const(d_bv_type, "d");
  Node d_e       = d_nm.mk_const(d_bv_type, "e");
  Node d_one     = d_nm.mk_value(BitVector::mk_one(8));
  Node d_zero    = d_nm.mk_value(BitVector::mk_zero(8));
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
                       {{d_a, 1},
                        {d_b, 1},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 1},
                        {mul_cd, 1},
                        {mul_cd_e, 1},
                        {mul0, 1}},
                       {{d_a, 1},
                        {d_b, 1},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_de, 1},
                        {mul_cde, 1},
                        {mul_bcde, 1},
                        {mul1, 1}});
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
                       {{d_a, 2},
                        {d_b, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 1},
                        {mul_ad, 1},
                        {mul_ad_e, 1},
                        {mul0, 1}},
                       {{d_a, 1},
                        {d_b, 1},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_de, 1},
                        {mul_cde, 1},
                        {mul_bcde, 1},
                        {mul1, 1}});
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
                       {{d_a, 1},
                        {d_b, 1},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 1},
                        {mul_cd, 1},
                        {mul_cd_e, 1},
                        {mul0, 1}},
                       {{d_a, 2},
                        {d_b, 1},
                        {d_c, 1},
                        {d_e, 1},
                        {mul_ae, 1},
                        {mul_cae, 1},
                        {mul_bcae, 1},
                        {mul1, 1}});
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
                       {{d_a, 2},
                        {d_b, 2},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 2},
                        {mul_cd, 1},
                        {mul_e_ab, 1},
                        {mul_cd_e_ab, 1},
                        {mul0, 1}},
                       {{d_a, 1},
                        {d_b, 1},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_de, 1},
                        {mul_cde, 1},
                        {mul_bcde, 1},
                        {mul1, 1}});
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
                       {{d_a, 2},
                        {d_b, 2},
                        {d_c, 1},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 2},
                        {mul_cd, 1},
                        {mul_e_ab, 1},
                        {mul_cd_e_ab, 1},
                        {mul0, 1}},
                       {{d_a, 2},
                        {d_b, 1},
                        {d_c, 2},
                        {d_d, 2},
                        {mul_ab, 1},
                        {mul_cd, 2},
                        {mul_cd_a_cd, 1},
                        {mul1, 1}});
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
                       {{d_a, 3},
                        {d_b, 2},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 2},
                        {mul_ad, 1},
                        {mul_e_ab, 1},
                        {mul_ad_e_ab, 1},
                        {mul0, 1}},
                       {{d_a, 2},
                        {d_b, 1},
                        {d_c, 2},
                        {d_d, 2},
                        {mul_ab, 1},
                        {mul_cd, 2},
                        {mul_cd_a_cd, 1},
                        {mul1, 1}});
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
                       {{d_a, 3},
                        {d_b, 2},
                        {d_d, 1},
                        {d_e, 1},
                        {mul_ab, 2},
                        {mul_ad, 1},
                        {mul_e_ab, 1},
                        {mul_ad_e_ab, 1},
                        {mul0, 1}},
                       {{d_a, 7},
                        {d_b, 6},
                        {mul_ab, 6},
                        {mul_ab_ab, 3},
                        {mul_a_ab_ab, 1},
                        {mul_ab_ab_ab_ab, 1},
                        {mul1, 1}});
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
                       {{d_a, 1},
                        {d_b, 1},
                        {d_e, 1},
                        {mul_ab, 1},
                        {add_ab, 1},
                        {add_ad, 1},
                        {mul_e_ab, 1},
                        {mul_ad_e_ab, 1},
                        {mul0, 1}},
                       {{d_c, 1},
                        {d_d, 1},
                        {add_ab, 1},
                        {add_a_cd, 1},
                        {mul_cd, 1},
                        {mul_cd_a_cd, 1},
                        {mul1, 1}});
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassNormalize, normalize00)
{
  // (a * b) = (b * a)
  test_assertion(equal(mul(d_a, d_b), mul(d_b, d_a)), d_true);
}

TEST_F(TestPassNormalize, normalize01)
{
  // (a * b) = (b * a) * (a * b)
  test_assertion(equal(mul(d_a, d_b), mul(mul(d_b, d_a), mul(d_a, d_b))),
                 equal(d_one, mul(d_a, d_b)));
}

TEST_F(TestPassNormalize, normalize0)
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

  test_assertion(equal(mul0, mul1), d_true);
}

TEST_F(TestPassNormalize, normalize1)
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

  test_assertion(equal(mul0, mul1), equal(d_a, d_c));
}

TEST_F(TestPassNormalize, normalize2)
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

  test_assertion(equal(mul0, mul1), equal(d_d, d_a));
}

TEST_F(TestPassNormalize, normalize3)
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

  test_assertion(equal(mul0, mul1), equal(mul(d_a, d_b), d_one));
}

TEST_F(TestPassNormalize, normalize4)
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

  test_assertion(equal(mul0, mul1), equal(mul(d_b, d_e), mul(d_c, d_d)));
}

TEST_F(TestPassNormalize, normalize5)
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
                 equal(mul(d_a, mul(d_b, d_e)), mul(d_c, mul(d_c, d_d))));
}

TEST_F(TestPassNormalize, normalize6)
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
      equal(mul(d_d, d_e),
            mul(d_a,
                mul(d_a,
                    mul(d_a, mul(d_a, mul(d_b, mul(d_b, mul(d_b, d_b)))))))));
}

TEST_F(TestPassNormalize, normalize7)
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

  test_assertion(equal(mul0, mul1), equal(mul0, mul1));
}

TEST_F(TestPassNormalize, normalize8)
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
          mul1));
}

TEST_F(TestPassNormalize, normalize9)
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
                                                     mul(d_b, d_b)))))))))))}));
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
