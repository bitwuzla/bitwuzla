/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <utility>
#include <vector>

#include "bitblast/aig/aig_manager.h"
#include "bitblast/aig_bitblaster.h"
#include "test_lib.h"

namespace bzla::test {

class TestAigMgr : public TestCommon
{
};

TEST_F(TestAigMgr, ctor_dtor) { bitblast::AigManager aigmgr; }

TEST_F(TestAigMgr, move)
{
  bitblast::AigManager aigmgr;
  auto a     = aigmgr.mk_const();
  int64_t id = a.get_id();

  // Move construction transfers ownership and nulls the source.
  bitblast::AigNode b(std::move(a));
  ASSERT_TRUE(a.is_null());
  ASSERT_FALSE(b.is_null());
  ASSERT_EQ(b.get_id(), id);

  // Move assignment transfers ownership and nulls the source.
  bitblast::AigNode c;
  c = std::move(b);
  ASSERT_TRUE(b.is_null());
  ASSERT_FALSE(c.is_null());
  ASSERT_EQ(c.get_id(), id);

  // Self-move assignment must leave the node intact (no use-after-free, not
  // nulled). The reference indirection avoids a -Wself-move warning.
  bitblast::AigNode& ref = c;
  c                      = std::move(ref);
  ASSERT_FALSE(c.is_null());
  ASSERT_EQ(c.get_id(), id);
}

TEST_F(TestAigMgr, false_true_aig)
{
  bitblast::AigManager aigmgr;
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
  bitblast::AigManager aigmgr;

  auto const_aig = aigmgr.mk_const();

  ASSERT_TRUE(const_aig.is_const());
  ASSERT_FALSE(const_aig.is_false());
  ASSERT_FALSE(const_aig.is_true());
  ASSERT_FALSE(const_aig.is_and());
  ASSERT_FALSE(const_aig.is_negated());
}

TEST_F(TestAigMgr, not_aig)
{
  bitblast::AigManager aigmgr;

  auto bit     = aigmgr.mk_const();
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
  bitblast::AigManager aigmgr;

  auto and_aig = aigmgr.mk_and(aigmgr.mk_const(), aigmgr.mk_const());

  ASSERT_TRUE(and_aig.is_and());
  ASSERT_FALSE(and_aig.is_false());
  ASSERT_FALSE(and_aig.is_true());
  ASSERT_FALSE(and_aig.is_const());
  ASSERT_FALSE(and_aig.is_negated());
}

TEST_F(TestAigMgr, and_unique_aig)
{
  bitblast::AigManager aigmgr;

  auto left    = aigmgr.mk_const();
  auto right   = aigmgr.mk_const();
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
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

  auto a      = aigmgr.mk_bit();
  auto b      = aigmgr.mk_bit();
  auto or_aig = aigmgr.mk_or(a, b);

  ASSERT_TRUE(or_aig.is_and());
  ASSERT_FALSE(or_aig.is_false());
  ASSERT_FALSE(or_aig.is_true());
  ASSERT_FALSE(or_aig.is_const());
  ASSERT_TRUE(or_aig.is_negated());
}

TEST_F(TestAigMgr, or_unique_aig)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

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
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

  auto iff_aig = aigmgr.mk_iff(aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(iff_aig.is_and());
  ASSERT_FALSE(iff_aig.is_false());
  ASSERT_FALSE(iff_aig.is_true());
  ASSERT_FALSE(iff_aig.is_const());
}

TEST_F(TestAigMgr, iff_unique_aig)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

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
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

  auto ite_aig =
      aigmgr.mk_ite(aigmgr.mk_bit(), aigmgr.mk_bit(), aigmgr.mk_bit());

  ASSERT_TRUE(ite_aig.is_and());
  ASSERT_FALSE(ite_aig.is_false());
  ASSERT_FALSE(ite_aig.is_true());
  ASSERT_FALSE(ite_aig.is_const());
}

TEST_F(TestAigMgr, ite_unique_aig)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto T = mgr.mk_true();

  ASSERT_EQ(mgr.mk_and(a, T), a);
  ASSERT_EQ(mgr.mk_and(T, a), a);
}

TEST_F(TestAigMgr, boundedness1)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto F = mgr.mk_false();

  ASSERT_EQ(mgr.mk_and(a, F), F);
  ASSERT_EQ(mgr.mk_and(F, a), F);
}

TEST_F(TestAigMgr, idempotence1)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = a;

  ASSERT_EQ(mgr.mk_and(a, b), a);
  ASSERT_EQ(mgr.mk_and(b, a), a);
}

TEST_F(TestAigMgr, contradiction1)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_not(a);
  auto F = mgr.mk_false();

  ASSERT_EQ(mgr.mk_and(a, b), F);
  ASSERT_EQ(mgr.mk_and(b, a), F);
}

TEST_F(TestAigMgr, contradiction2_1)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto c = mgr.mk_const();
  auto d = mgr.mk_const();
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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto c = mgr.mk_const();
  auto d = mgr.mk_const();

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto c = b;

  ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), c),
            mgr.mk_and(mgr.mk_not(a), b));
  ASSERT_EQ(mgr.mk_and(c, mgr.mk_not(mgr.mk_and(a, b))),
            mgr.mk_and(mgr.mk_not(a), b));
}

TEST_F(TestAigMgr, substitution3_2)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto c = b;
  auto d = mgr.mk_const();

  ASSERT_EQ(mgr.mk_and(mgr.mk_not(mgr.mk_and(a, b)), mgr.mk_and(c, d)),
            mgr.mk_and(mgr.mk_not(a), mgr.mk_and(c, d)));
  ASSERT_EQ(mgr.mk_and(mgr.mk_and(c, d), mgr.mk_not(mgr.mk_and(a, b))),
            mgr.mk_and(mgr.mk_not(a), mgr.mk_and(c, d)));
}

TEST_F(TestAigMgr, idempotence4_1)
{
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto d = mgr.mk_const();

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
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  auto b = mgr.mk_const();
  auto c = mgr.mk_const();
  auto d = mgr.mk_const();

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

TEST_F(TestAigMgr, copy_assign_null)
{
  // Regression: the copy assignment operator unconditionally incremented the
  // assigned data's reference count. Copy-assigning a null
  // (default-constructed) AigNode dereferenced a nullptr. The source must be a
  // named lvalue: an rvalue (e.g. `a = AigNode()`) binds to the move assignment
  // operator instead, which already handled null correctly.
  bitblast::AigManager mgr;

  auto a = mgr.mk_const();
  ASSERT_FALSE(a.is_null());

  bitblast::AigNode null_node;
  a = null_node;
  ASSERT_TRUE(a.is_null());
}

TEST_F(TestAigMgr, unique_table_resize)
{
  // Regression: the unique table computed the bucket index by masking the hash
  // with d_buckets.capacity() - 1 (and the load-factor check and resize used
  // capacity() as well), assuming capacity() is exactly the power-of-two bucket
  // count requested via resize(). std::vector only guarantees
  // capacity() >= size(), so on an over-allocating implementation capacity()
  // need not be a power of two and the mask could yield an index in
  // [size(), capacity()), an out-of-bounds access. Create enough distinct AND
  // gates to force several resizes (initial bucket count is 16) and check that
  // hash consing still returns the same node for each, exercising insert and
  // lookup across the resize path.
  bitblast::AigManager mgr;

  std::vector<bitblast::AigNode> consts;
  for (size_t i = 0; i < 40; ++i)
  {
    consts.push_back(mgr.mk_const());
  }

  // Build distinct AND gates over all pairs of independent constants. None of
  // these are simplified by the AIG rewriter, so each creates a fresh AND node,
  // growing the unique table far past its initial 16 buckets.
  std::vector<bitblast::AigNode> ands;
  for (size_t i = 0; i < consts.size(); ++i)
  {
    for (size_t j = i + 1; j < consts.size(); ++j)
    {
      ands.push_back(mgr.mk_and(consts[i], consts[j]));
    }
  }

  // Every AND gate must remain hash consed across the resizes: re-creating it
  // (in either argument order) returns the same node.
  size_t k = 0;
  for (size_t i = 0; i < consts.size(); ++i)
  {
    for (size_t j = i + 1; j < consts.size(); ++j)
    {
      ASSERT_EQ(ands[k], mgr.mk_and(consts[i], consts[j]));
      ASSERT_EQ(ands[k], mgr.mk_and(consts[j], consts[i]));
      ++k;
    }
  }
}

TEST_F(TestAigMgr, copy_assign_self)
{
  // Regression: on self-assignment where *this holds the last reference, the
  // copy assignment operator decremented first, garbage collecting the data,
  // then accessed it again (use-after-free). Use a pointer to avoid
  // -Wself-assign-overloaded.
  bitblast::AigManager mgr;

  auto a               = mgr.mk_const();
  bitblast::AigNode* p = &a;
  a                    = *p;
  ASSERT_FALSE(a.is_null());
}

}  // namespace bzla::test
