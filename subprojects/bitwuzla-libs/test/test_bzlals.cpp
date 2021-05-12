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

    d_bzlals.reset(new BzlaLs(100));

    d_c1 = d_bzlals->mk_node(BzlaLs::NodeKind::CONST, TEST_BW, {});
    d_v1 = d_bzlals->mk_node(BzlaLs::NodeKind::CONST, TEST_BW, {});
    d_v2 = d_bzlals->mk_node(BzlaLs::NodeKind::CONST, TEST_BW, {});
    d_v3 = d_bzlals->mk_node(BzlaLs::NodeKind::CONST, TEST_BW, {});

    // v1 + c1
    d_v1pc1 = d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v1, d_c1});
    // (v1 + c1) + v2
    d_v1pc1pv2 =
        d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v1pc1, d_v2});
    // v1 + v2
    d_v1pv2 = d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v1, d_v2});
    // (v1 + v2) & v2
    d_v1pv2av2 =
        d_bzlals->mk_node(BzlaLs::NodeKind::AND, TEST_BW, {d_v1pv2, d_v2});

    // v1[0:0]
    d_v1e =
        d_bzlals->mk_indexed_node(BzlaLs::NodeKind::EXTRACT, 1, d_v1, {0, 0});
    // v3[0:0]
    d_v3e =
        d_bzlals->mk_indexed_node(BzlaLs::NodeKind::EXTRACT, 1, d_v3, {0, 0});
    // v1[0:0] + v3[0:0]
    d_v1epv3e = d_bzlals->mk_node(BzlaLs::NodeKind::ADD, 1, {d_v1e, d_v3e});
    // sext(v1[0:0] + v3[0:0], 3)
    d_v1epv3e_ext = d_bzlals->mk_indexed_node(
        BzlaLs::NodeKind::SEXT, TEST_BW, d_v1epv3e, {3});

    // v3 + c1
    d_v3pc1 = d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v3, d_c1});
    // (v3 + c1) + v3
    d_v3pc1pv3 =
        d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v3pc1, d_v3});
    // ((v3 + c1) + v3) + v1
    d_v3pc1pv3pv1 =
        d_bzlals->mk_node(BzlaLs::NodeKind::ADD, TEST_BW, {d_v3pc1pv3, d_v1});

    // root1: (v1 + c1) + v2 < (v1 + v2) & v2
    d_root1 =
        d_bzlals->mk_node(BzlaLs::NodeKind::ULT, 1, {d_v1pc1pv2, d_v1pv2av2});
    // root2: sext(v1[0:0] + v3[0:0], 3) = ((v3 + c1) + v3) + v1
    d_root2 = d_bzlals->mk_node(
        BzlaLs::NodeKind::EQ, 1, {d_v1epv3e_ext, d_v3pc1pv3pv1});
  }

  std::unique_ptr<BzlaLs> d_bzlals;

  uint32_t d_c1, d_v1, d_v2, d_v3;
  uint32_t d_v1pc1, d_v1pc1pv2;
  uint32_t d_v1pv2, d_v1pv2av2;
  uint32_t d_v1e, d_v3e;
  uint32_t d_v1epv3e, d_v1epv3e_ext;
  uint32_t d_v3pc1, d_v3pc1pv3;
  uint32_t d_v3pc1pv3pv1;
  uint32_t d_root1, d_root2;
};

TEST_F(TestBzlaLs, parents)
{
  d_bzlals->register_root(d_root1);
  d_bzlals->register_root(d_root2);
  d_bzlals->init_parents();

  const BzlaLs::ParentsMap& parents = d_bzlals->get_parents();

  {
    const std::unordered_set<uint32_t>& p = parents.at(d_c1);
    ASSERT_TRUE(p.size() == 2);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1);
    ASSERT_TRUE(p.size() == 4);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1) != p.end());
    ASSERT_TRUE(p.find(d_v1e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v2);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v1pc1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v3pc1) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3) != p.end());
    ASSERT_TRUE(p.find(d_v3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pc1);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pc1pv2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pc1pv2);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pv2);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pv2av2);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1e);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3e);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1epv3e);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e_ext) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1epv3e_ext);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1pv3);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1pv3pv1);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_root1);
    ASSERT_TRUE(p.size() == 0);
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_root2);
    ASSERT_TRUE(p.size() == 0);
  }
}

}  // namespace test
}  // namespace bzlals
