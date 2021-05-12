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

  /**
   * Create a mapping from nodes to their parents to compare against the
   * mapping created internally on node creation.
   */
  BzlaLs::ParentsMap get_parents();

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

BzlaLs::ParentsMap
TestBzlaLs::get_parents()
{
  BzlaLs::ParentsMap parents;
  const BzlaLs::NodesIdTable& nodes = d_bzlals->get_nodes();
  std::vector<uint32_t> to_visit    = {d_root1, d_root2};
  while (!to_visit.empty())
  {
    uint32_t cur_id = to_visit.back();
    assert(cur_id < nodes.size());
    to_visit.pop_back();
    const BitVectorNode* cur = nodes[cur_id].get();
    if (parents.find(cur_id) == parents.end())
    {
      parents[cur_id] = {};
    }
    for (uint32_t i = 0; i < cur->arity(); ++i)
    {
      BitVectorNode* child = (*cur)[i];
      uint32_t child_id    = child->id();
      if (parents.find(child_id) == parents.end())
      {
        parents[child_id] = {};
      }
      if (parents.at(child_id).find(cur_id) == parents.at(child_id).end())
      {
        parents.at(child_id).insert(cur_id);
      }
      to_visit.push_back(child_id);
    }
  }
  return parents;
}

TEST_F(TestBzlaLs, parents)
{
  d_bzlals->register_root(d_root1);
  d_bzlals->register_root(d_root2);

  BzlaLs::ParentsMap parents          = d_bzlals->get_parents();
  BzlaLs::ParentsMap parents_expected = get_parents();

  {
    const std::unordered_set<uint32_t>& p = parents.at(d_c1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_c1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 2);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 4);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1) != p.end());
    ASSERT_TRUE(p.find(d_v1e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v2);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v1pc1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v3);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v3pc1) != p.end());
    ASSERT_TRUE(p.find(d_v3pc1pv3) != p.end());
    ASSERT_TRUE(p.find(d_v3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pc1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1pc1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pc1pv2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pc1pv2);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1pc1pv2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pv2);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1pv2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1pv2av2);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1pv2av2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1e);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3e);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v3e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1epv3e);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1epv3e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1epv3e_ext) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v1epv3e_ext);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v1epv3e_ext);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v3pc1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1pv3);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v3pc1pv3);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3pc1pv3pv1) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_v3pc1pv3pv1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_v3pc1pv3pv1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_root1);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_root1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 0);
  }
  {
    const std::unordered_set<uint32_t>& p = parents.at(d_root2);
    const std::unordered_set<uint32_t>& pe = parents_expected.at(d_root2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 0);
  }
}

}  // namespace test
}  // namespace bzlals
