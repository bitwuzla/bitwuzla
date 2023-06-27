/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bitblast/aig/aig_manager.h"
#include "test_lib.h"

namespace bzla::test {

class TestAigMgr : public TestCommon
{
};

TEST_F(TestAigMgr, ctor_dtor) { bb::AigManager aigmgr; }

TEST_F(TestAigMgr, false_true_aig)
{
  bb::AigManager aigmgr;
  auto true_aig  = aigmgr.mk_true();
  auto false_aig = aigmgr.mk_false();

  ASSERT_TRUE(false_aig.is_false());
  ASSERT_FALSE(false_aig.is_true());
  ASSERT_FALSE(false_aig.is_const());
  ASSERT_FALSE(false_aig.is_and());
  ASSERT_TRUE(false_aig.is_negated());
  ASSERT_TRUE(true_aig.is_true());
  ASSERT_FALSE(true_aig.is_false());
  ASSERT_FALSE(true_aig.is_const());
  ASSERT_FALSE(true_aig.is_and());
  ASSERT_FALSE(true_aig.is_negated());
  ASSERT_EQ(aigmgr.mk_not(true_aig), false_aig);
}

TEST_F(TestAigMgr, const_aig)
{
  bb::AigManager aigmgr;

  auto const_aig = aigmgr.mk_bit();

  ASSERT_TRUE(const_aig.is_const());
  ASSERT_FALSE(const_aig.is_false());
  ASSERT_FALSE(const_aig.is_true());
  ASSERT_FALSE(const_aig.is_and());
  ASSERT_FALSE(const_aig.is_negated());
}

TEST_F(TestAigMgr, not_aig)
{
  bb::AigManager aigmgr;

  auto bit     = aigmgr.mk_bit();
  auto not_aig = aigmgr.mk_not(bit);

  ASSERT_FALSE(not_aig.is_and());
  ASSERT_FALSE(not_aig.is_false());
  ASSERT_FALSE(not_aig.is_true());
  ASSERT_TRUE(not_aig.is_const());
  ASSERT_TRUE(not_aig.is_negated());
  ASSERT_FALSE(aigmgr.mk_not(not_aig).is_negated());
  ASSERT_EQ(bit, aigmgr.mk_not(not_aig));
}

TEST_F(TestAigMgr, and_aig)
{
  bb::AigManager aigmgr;

  auto and_aig = aigmgr.mk_and(aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(and_aig.is_and());
  ASSERT_FALSE(and_aig.is_false());
  ASSERT_FALSE(and_aig.is_true());
  ASSERT_FALSE(and_aig.is_const());
  ASSERT_FALSE(and_aig.is_negated());
}

TEST_F(TestAigMgr, and_unique_aig)
{
  bb::AigManager aigmgr;

  auto left    = aigmgr.mk_bit();
  auto right   = aigmgr.mk_bit();
  auto and_aig = aigmgr.mk_and(left, right);

  ASSERT_TRUE(and_aig.is_and());
  ASSERT_FALSE(and_aig.is_false());
  ASSERT_FALSE(and_aig.is_true());
  ASSERT_FALSE(and_aig.is_const());
  ASSERT_FALSE(and_aig.is_negated());
  ASSERT_EQ(and_aig, aigmgr.mk_and(left, right));
  ASSERT_EQ(and_aig, aigmgr.mk_and(right, left));
}

TEST_F(TestAigMgr, or_aig)
{
  bb::AigManager aigmgr;

  auto and_aig = aigmgr.mk_or(aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(and_aig.is_and());
  ASSERT_FALSE(and_aig.is_false());
  ASSERT_FALSE(and_aig.is_true());
  ASSERT_FALSE(and_aig.is_const());
  ASSERT_TRUE(and_aig.is_negated());
}

TEST_F(TestAigMgr, or_unique_aig)
{
  bb::AigManager aigmgr;

  auto left   = aigmgr.mk_bit();
  auto right  = aigmgr.mk_bit();
  auto or_aig = aigmgr.mk_or(left, right);

  ASSERT_TRUE(or_aig.is_and());
  ASSERT_FALSE(or_aig.is_false());
  ASSERT_FALSE(or_aig.is_true());
  ASSERT_FALSE(or_aig.is_const());
  ASSERT_TRUE(or_aig.is_negated());
  ASSERT_EQ(or_aig, aigmgr.mk_or(left, right));
  ASSERT_EQ(or_aig, aigmgr.mk_or(right, left));
}

TEST_F(TestAigMgr, iff_aig)
{
  bb::AigManager aigmgr;

  auto iff_aig = aigmgr.mk_iff(aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(iff_aig.is_and());
  ASSERT_FALSE(iff_aig.is_false());
  ASSERT_FALSE(iff_aig.is_true());
  ASSERT_FALSE(iff_aig.is_const());
}

TEST_F(TestAigMgr, iff_unique_aig)
{
  bb::AigManager aigmgr;

  auto left    = aigmgr.mk_bit();
  auto right   = aigmgr.mk_bit();
  auto iff_aig = aigmgr.mk_iff(left, right);

  ASSERT_TRUE(iff_aig.is_and());
  ASSERT_FALSE(iff_aig.is_false());
  ASSERT_FALSE(iff_aig.is_true());
  ASSERT_FALSE(iff_aig.is_const());
  ASSERT_EQ(iff_aig, aigmgr.mk_iff(left, right));
  ASSERT_EQ(iff_aig, aigmgr.mk_iff(right, left));
}

TEST_F(TestAigMgr, ite_aig)
{
  bb::AigManager aigmgr;

  auto ite_aig =
      aigmgr.mk_ite(aigmgr.mk_bit(), aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(ite_aig.is_and());
  ASSERT_FALSE(ite_aig.is_false());
  ASSERT_FALSE(ite_aig.is_true());
  ASSERT_FALSE(ite_aig.is_const());
}

TEST_F(TestAigMgr, ite_unique_aig)
{
  bb::AigManager aigmgr;

  auto cond    = aigmgr.mk_bit();
  auto left    = aigmgr.mk_bit();
  auto right   = aigmgr.mk_bit();
  auto ite_aig = aigmgr.mk_ite(cond, left, right);

  ASSERT_TRUE(ite_aig.is_and());
  ASSERT_FALSE(ite_aig.is_false());
  ASSERT_FALSE(ite_aig.is_true());
  ASSERT_FALSE(ite_aig.is_const());
  ASSERT_EQ(ite_aig, aigmgr.mk_ite(cond, left, right));
  ASSERT_EQ(ite_aig, aigmgr.mk_ite(aigmgr.mk_not(cond), right, left));
}

TEST_F(TestAigMgr, neutrality1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto T = mgr.mk_true();

  ASSERT_EQ(mgr.mk_and(a, T), a);
  ASSERT_EQ(mgr.mk_and(T, a), a);
}

TEST_F(TestAigMgr, boundedness1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto F = mgr.mk_false();

  ASSERT_EQ(mgr.mk_and(a, F), F);
  ASSERT_EQ(mgr.mk_and(F, a), F);
}

TEST_F(TestAigMgr, idempotence1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = a;

  ASSERT_EQ(mgr.mk_and(a, b), a);
  ASSERT_EQ(mgr.mk_and(b, a), a);
}

TEST_F(TestAigMgr, contradiction1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_not(a);
  auto F = mgr.mk_false();

  ASSERT_EQ(mgr.mk_and(a, b), F);
  ASSERT_EQ(mgr.mk_and(b, a), F);
}

TEST_F(TestAigMgr, contradiction2_1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto F = mgr.mk_false();

  // case: (a = ~c)
  {
    auto c = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), c), F);
  }

  // case: (b = ~c)
  {
    auto c = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), c), F);
  }
}

TEST_F(TestAigMgr, contradiction2_2)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto c = mgr.mk_bit();
  auto d = mgr.mk_bit();
  auto F = mgr.mk_false();

  // case: (a = ~c)
  {
    auto c = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)), F);
  }

  // case: (a = ~d)
  {
    auto d = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)), F);
  }

  // case: (b = ~c)
  {
    auto c = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)), F);
  }

  // case: (b = ~d)
  {
    auto d = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)), F);
  }
}

TEST_F(TestAigMgr, subsumption2_1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();

  // case: (a = ~c)
  {
    auto c = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), c), c);
  }

  // case: (b = ~c)
  {
    auto c = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), c), c);
  }
}

TEST_F(TestAigMgr, subsumption2_2)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto c = mgr.mk_bit();
  auto d = mgr.mk_bit();

  // case: (a = ~c)
  {
    auto c = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
              mgr.mk_and(c, d));
  }

  // case: (a = ~d)
  {
    auto d = mgr.mk_not(a);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
              mgr.mk_and(c, d));
  }

  // case: (b = ~c)
  {
    auto c = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
              mgr.mk_and(c, d));
  }

  // case: (b = ~d)
  {
    auto d = mgr.mk_not(b);
    ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
              mgr.mk_and(c, d));
  }
}

TEST_F(TestAigMgr, idempotence2)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();

  // case: (a = c)
  {
    auto c = a;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), c), mgr.mk_and(a, b));
  }

  // case: (b = c)
  {
    auto c = b;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), c), mgr.mk_and(a, b));
  }
}

TEST_F(TestAigMgr, resolution2)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();

  // (a = c) /\ (b = ~d)
  {
    auto c = a;
    auto d = mgr.mk_not(b);
    ASSERT_EQ(
        mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_not(mgr.mk_and(c, d))),
        mgr.mk_not(a));
  }

  // (a = d) /\ (b = ~c)
  {
    auto c = mgr.mk_not(b);
    auto d = a;
    ASSERT_EQ(
        mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_not(mgr.mk_and(c, d))),
        mgr.mk_not(a));
  }

  // (b = d) /\ (a = ~c)
  {
    auto c = mgr.mk_not(a);
    auto d = b;
    ASSERT_EQ(
        mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_not(mgr.mk_and(c, d))),
        mgr.mk_not(d));
  }

  // (a = d) /\ (b = ~c) (redundant)
  {
    auto c = mgr.mk_not(b);
    auto d = a;
    ASSERT_EQ(
        mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_not(mgr.mk_and(c, d))),
        mgr.mk_not(d));
  }
}

TEST_F(TestAigMgr, substitution3_1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto c = b;

  ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), c),
            mgr.mk_and(mgr.mk_not(a), b));
  ASSERT_EQ(mgr.mk_and(c, mgr.mk_not(mgr.mk_and(a, b))),
            mgr.mk_and(mgr.mk_not(a), b));
}

TEST_F(TestAigMgr, substitution3_2)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto c = b;
  auto d = mgr.mk_bit();

  ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
            mgr.mk_and(mgr.mk_not(a), mgr.mk_and(c, d)));
  ASSERT_EQ(mgr.mk_and(mgr.mk_and(c, d), mgr.mk_not(mgr.mk_and(a, b))),
            mgr.mk_and(mgr.mk_not(a), mgr.mk_and(c, d)));
}

TEST_F(TestAigMgr, idempotence4_1)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto d = mgr.mk_bit();

  {
    auto c = a;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)),
              mgr.mk_and(mgr.mk_and(a, b), d));
  }

  {
    auto c = b;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)),
              mgr.mk_and(mgr.mk_and(a, b), d));
  }
}

TEST_F(TestAigMgr, idempotence4_3)
{
  bb::AigManager mgr;

  auto a = mgr.mk_bit();
  auto b = mgr.mk_bit();
  auto c = mgr.mk_bit();
  auto d = mgr.mk_bit();

  {
    auto d = a;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)),
              mgr.mk_and(mgr.mk_and(a, b), c));
  }

  {
    auto d = b;
    ASSERT_EQ(mgr.mk_and(mgr.mk_and(a, b), mgr.mk_and(c, d)),
              mgr.mk_and(mgr.mk_and(a, b), c));
  }
}

}  // namespace bzla::test
