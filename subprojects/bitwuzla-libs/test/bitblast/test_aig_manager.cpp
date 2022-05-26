#include "bitblast/aig/aig_manager.h"
#include "test.h"

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

}  // namespace bzla::test
