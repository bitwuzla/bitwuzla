#include "bitvector_node.h"
#include "bzlals.h"
#include "test.h"

namespace bzlals {
namespace test {

class TestBzlaLs : public TestBvNodeCommon
{
 protected:
  void SetUp() override
  {
    TestBvNodeCommon::SetUp();

    d_c1.reset(new BitVectorNode(d_rng.get(), TEST_BW));
    d_v1.reset(new BitVectorNode(d_rng.get(), TEST_BW));
    d_v2.reset(new BitVectorNode(d_rng.get(), TEST_BW));
    d_v3.reset(new BitVectorNode(d_rng.get(), TEST_BW));

    // v1 + c1
    d_v1pc1.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v1.get(), d_c1.get()));
    // (v1 + c1) + v2
    d_v1pc1pv2.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v1pc1.get(), d_v2.get()));
    // v1 + v2
    d_v1pv2.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v1.get(), d_v2.get()));
    // (v1 + v2) & v2
    d_v1pv2av2.reset(
        new BitVectorAnd(d_rng.get(), TEST_BW, d_v1pv2.get(), d_v2.get()));

    // v1[0:0]
    d_v1e.reset(new BitVectorExtract(d_rng.get(), TEST_BW, d_v1.get(), 0, 0));
    // v3[0:0]
    d_v3e.reset(new BitVectorExtract(d_rng.get(), TEST_BW, d_v3.get(), 0, 0));
    // v1[0:0] + v3[0:0]
    d_v1epv3e.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v1e.get(), d_v3e.get()));
    // sext(v1[0:0] + v3[0:0], 3)
    d_v1epv3e_ext.reset(
        new BitVectorSignExtend(d_rng.get(), TEST_BW, d_v1epv3e.get(), 3));

    // v3 + c1
    d_v3pc1.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v3.get(), d_c1.get()));
    // (v3 + c1) + v3
    d_v3pc1pv3.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v3pc1.get(), d_v3.get()));
    // ((v3 + c1) + v3) + v1
    d_v3pc1pv3pv1.reset(
        new BitVectorAdd(d_rng.get(), TEST_BW, d_v3pc1pv3.get(), d_v1.get()));

    // root1: (v1 + c1) + v2 < (v1 + v2) & v2
    d_root1.reset(new BitVectorUlt(
        d_rng.get(), TEST_BW, d_v1pc1pv2.get(), d_v1pv2av2.get()));
    // root2: sext(v1[0:0] + v3[0:0], 3) = ((v3 + c1) + v3) + v1
    d_root2.reset(new BitVectorEq(
        d_rng.get(), TEST_BW, d_v1epv3e_ext.get(), d_v3pc1pv3pv1.get()));
  }

  std::unique_ptr<BitVectorNode> d_c1, d_v1, d_v2, d_v3;
  std::unique_ptr<BitVectorNode> d_v1pc1, d_v1pc1pv2;
  std::unique_ptr<BitVectorNode> d_v1pv2, d_v1pv2av2;
  std::unique_ptr<BitVectorNode> d_v1e, d_v3e;
  std::unique_ptr<BitVectorNode> d_v1epv3e, d_v1epv3e_ext;
  std::unique_ptr<BitVectorNode> d_v3pc1, d_v3pc1pv3;
  std::unique_ptr<BitVectorNode> d_v3pc1pv3pv1;
  std::unique_ptr<BitVectorNode> d_root1, d_root2;
};

TEST_F(TestBzlaLs, parents)
{
  BzlaLs bzlals(100);
  bzlals.register_root(d_root1.get());
  bzlals.register_root(d_root2.get());
  bzlals.init_parents();

  const BzlaLs::ParentsMap& parents = bzlals.get_parents();

  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_c1.get());
    ASSERT_TRUE(p.size() == 2);
    ASSERT_TRUE(p.find(d_v1pc1.get()) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1.get());
    ASSERT_TRUE(p.size() == 4);
    ASSERT_TRUE(p.find(d_v1pc1.get()) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2.get()) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1.get()) != p.end());
    ASSERT_TRUE(p.find(d_v1e.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v2.get());
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v1pc1pv2.get()) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2.get()) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2av2.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v3.get());
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v3pc1.get()) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3.get()) != p.end());
    ASSERT_TRUE(p.find(d_v3e.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1pc1.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pc1pv2.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1pc1pv2.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1pv2.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pv2av2.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1pv2av2.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1e.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v3e.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v1epv3e.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e_ext.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p =
        parents.at(d_v1epv3e_ext.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v3pc1.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_v3pc1pv3.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p =
        parents.at(d_v3pc1pv3pv1.get());
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2.get()) != p.end());
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_root1.get());
    ASSERT_TRUE(p.size() == 0);
  }
  {
    const std::unordered_set<BitVectorNode*>& p = parents.at(d_root2.get());
    ASSERT_TRUE(p.size() == 0);
  }
}

}  // namespace test
}  // namespace bzlals
