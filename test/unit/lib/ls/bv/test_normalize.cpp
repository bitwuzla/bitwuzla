/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "gtest/gtest.h"
#include "ls/bv/bitvector_node.h"
#include "ls/ls_bv.h"

namespace bzla::ls::test {

/* -------------------------------------------------------------------------- */

class TestLsBvNormalize : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_ls.reset(new LocalSearchBV(100, 100));
    d_id   = d_ls->mk_node(NodeKind::CONST, 8);
    d_node = d_ls->get_node(d_id);
  }

  void test_split_indices(
      const std::vector<std::pair<uint64_t, uint64_t>>& extracts,
      const std::vector<std::pair<uint64_t, uint64_t>>& expected) const
  {
    std::vector<BitVectorExtract*> registered;
    for (auto ex : extracts)
    {
      uint64_t id = d_ls->mk_node(NodeKind::BV_EXTRACT,
                                  ex.first - ex.second + 1,
                                  {d_id},
                                  {ex.first, ex.second});
      registered.push_back(static_cast<BitVectorExtract*>(d_ls->get_node(id)));
    }
    ASSERT_EQ(d_node->d_extracts, registered);
    auto indices = d_ls->split_indices(d_node);
    ASSERT_EQ(indices, expected);
  }

  void test_normalize(
      const std::vector<std::pair<uint64_t, uint64_t>>& extracts,
      const std::vector<std::vector<std::pair<uint64_t, uint64_t>>>& expected)
      const
  {
    assert(extracts.size() == expected.size());
    std::vector<BitVectorExtract*> registered;
    std::vector<BitVectorNode*> child0s;
    for (auto ex : extracts)
    {
      BitVectorExtract* e = static_cast<BitVectorExtract*>(
          d_ls->get_node(d_ls->mk_node(NodeKind::BV_EXTRACT,
                                       ex.first - ex.second + 1,
                                       {d_id},
                                       {ex.first, ex.second})));
      registered.push_back(e);
      child0s.push_back(e->child(0));
    }
    d_ls->normalize_extracts(d_node);
    for (size_t i = 0, size = extracts.size(); i < size; ++i)
    {
      BitVectorExtract* ex      = registered[i];
      BitVectorNode* child0     = child0s[i];
      BitVectorNode* normalized = ex->child(0);
      BitVectorNode* orig       = ex->d_child0_original;
      ASSERT_EQ(orig == nullptr, expected[i].size() <= 1);
      ASSERT_EQ(orig == nullptr, child0 == normalized);
      if (expected[i].size() > 1)
      {
        ASSERT_EQ(*d_ls->d_parents.at(normalized->id()).begin(), ex->id());
        ASSERT_TRUE(normalized->kind() == NodeKind::BV_CONCAT);
        for (auto p : expected[i])
        {
          if (normalized->kind() != NodeKind::BV_CONCAT)
          {
            break;
          }
          auto [hi, lo] = p;
          ASSERT_EQ(normalized->child(1)->kind(), NodeKind::BV_EXTRACT);
          BitVectorExtract* ex1 =
              static_cast<BitVectorExtract*>(normalized->child(1));
          ASSERT_EQ(hi, ex1->hi());
          ASSERT_EQ(lo, ex1->lo());
          normalized = normalized->child(0);
        }
      }
    }
  }

  std::unique_ptr<LocalSearchBV> d_ls;
  BitVectorNode* d_node;
  uint64_t d_id;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestLsBvNormalize, split_indices_1) { test_split_indices({{3, 2}}, {}); }

TEST_F(TestLsBvNormalize, split_indices_2_n)
{
  // two extracts, not overlapping
  test_split_indices({{3, 2}, {4, 4}}, {{1, 0}, {3, 2}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_3_n)
{
  // three extracts, not overlapping
  test_split_indices({{3, 2}, {4, 4}, {1, 0}},
                     {{1, 0}, {3, 2}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o00)
{
  // two extracts, overlapping
  test_split_indices({{7, 0}, {7, 0}}, {{7, 0}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o01)
{
  // two extracts, overlapping
  test_split_indices({{3, 2}, {3, 2}}, {{1, 0}, {3, 2}, {7, 4}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o1)
{
  // two extracts, overlapping
  test_split_indices({{3, 2}, {4, 2}}, {{1, 0}, {3, 2}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o2)
{
  // two extracts, overlapping
  test_split_indices({{3, 2}, {4, 3}},
                     {{1, 0}, {2, 2}, {3, 3}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o3)
{
  // two extracts, overlapping
  test_split_indices({{3, 2}, {4, 1}},
                     {{0, 0}, {1, 1}, {3, 2}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o4)
{
  // two extracts, overlapping
  test_split_indices({{3, 0}, {4, 1}}, {{0, 0}, {3, 1}, {4, 4}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o5)
{
  // two extracts, overlapping
  test_split_indices({{4, 0}, {4, 1}}, {{0, 0}, {4, 1}, {7, 5}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o6)
{
  // two extracts, overlapping
  test_split_indices({{4, 0}, {6, 0}}, {{4, 0}, {6, 5}, {7, 7}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o7)
{
  // two extracts, overlapping
  test_split_indices({{6, 0}, {4, 0}}, {{4, 0}, {6, 5}, {7, 7}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o8)
{
  // two extracts, overlapping
  test_split_indices({{7, 3}, {7, 2}}, {{1, 0}, {2, 2}, {7, 3}});
}

TEST_F(TestLsBvNormalize, split_indices_2_o9)
{
  // two extracts, overlapping
  test_split_indices({{7, 1}, {7, 2}}, {{0, 0}, {1, 1}, {7, 2}});
}

TEST_F(TestLsBvNormalize, split_indices_3_o0)
{
  // three extracts, overlapping
  test_split_indices({{7, 5}, {6, 3}, {4, 0}},
                     {{2, 0}, {4, 3}, {6, 5}, {7, 7}});
}

TEST_F(TestLsBvNormalize, split_indices_3_o1)
{
  // three extracts, overlapping
  test_split_indices({{7, 5}, {6, 3}, {2, 0}},
                     {{2, 0}, {4, 3}, {6, 5}, {7, 7}});
}

TEST_F(TestLsBvNormalize, split_indices_3_o2)
{
  // three extracts, overlapping
  test_split_indices({{7, 5}, {6, 4}, {5, 0}},
                     {{3, 0}, {4, 4}, {5, 5}, {6, 6}, {7, 7}});
}

/* -------------------------------------------------------------------------- */

TEST_F(TestLsBvNormalize, normalize_1) { test_normalize({{3, 2}}, {{}}); }

TEST_F(TestLsBvNormalize, normalize_2_n)
{
  // two extracts, not overlapping
  test_normalize({{3, 2}, {4, 4}}, {{{3, 2}}, {{4, 4}}});
}

TEST_F(TestLsBvNormalize, normalize_3_n)
{
  // three extracts, not overlapping
  test_normalize({{3, 2}, {4, 4}, {1, 0}}, {{{3, 2}}, {{4, 4}}, {{1, 0}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o00)
{
  test_normalize({{7, 0}, {7, 0}}, {{}, {}});
}

TEST_F(TestLsBvNormalize, normalize_2_o01)
{
  // two extracts, overlapping
  test_normalize({{3, 2}, {3, 2}}, {{}, {}});
}

TEST_F(TestLsBvNormalize, normalize_2_o1)
{
  // two extracts, overlapping
  test_normalize({{3, 2}, {4, 2}}, {{{3, 2}}, {{3, 2}, {4, 4}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o2)
{
  // two extracts, overlapping
  test_normalize({{3, 2}, {4, 3}}, {{{2, 2}, {3, 3}}, {{3, 3}, {4, 4}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o3)
{
  // two extracts, overlapping
  test_normalize({{3, 2}, {4, 1}}, {{{3, 2}}, {{1, 1}, {3, 2}, {4, 4}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o4)
{
  // two extracts, overlapping
  test_normalize({{3, 0}, {4, 1}}, {{{0, 0}, {3, 1}}, {{3, 1}, {4, 4}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o5)
{
  // two extracts, overlapping
  test_normalize({{4, 0}, {4, 1}}, {{{0, 0}, {4, 1}}, {{4, 1}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o6)
{
  // two extracts, overlapping
  test_normalize({{4, 0}, {6, 0}}, {{{4, 0}}, {{4, 0}, {6, 5}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o7)
{
  // two extracts, overlapping
  test_normalize({{6, 0}, {4, 0}}, {{{4, 0}, {6, 5}}, {{4, 0}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o8)
{
  // two extracts, overlapping
  test_normalize({{7, 3}, {7, 2}}, {{{7, 3}}, {{2, 2}, {7, 3}}});
}

TEST_F(TestLsBvNormalize, normalize_2_o9)
{
  // two extracts, overlapping
  test_normalize({{7, 1}, {7, 2}}, {{{1, 1}, {7, 2}}, {{7, 2}}});
}

TEST_F(TestLsBvNormalize, normalize_3_o0)
{
  // three extracts, overlapping
  test_normalize({{7, 5}, {6, 3}, {4, 0}},
                 {{{6, 5}, {7, 7}}, {{4, 3}, {6, 5}}, {{2, 0}, {4, 3}}});
}

TEST_F(TestLsBvNormalize, normalize_3_o1)
{
  // three extracts, overlapping
  test_normalize({{7, 5}, {6, 3}, {2, 0}},
                 {{{6, 5}, {7, 7}}, {{4, 3}, {6, 5}}, {{2, 0}}});
}

TEST_F(TestLsBvNormalize, normalize_3_o2)
{
  // three extracts, overlapping
  test_normalize({{7, 5}, {6, 4}, {5, 0}},
                 {{{5, 5}, {6, 6}, {7, 7}},
                  {{4, 4}, {5, 5}, {6, 6}},
                  {{3, 0}, {4, 4}, {5, 5}}});
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::ls::test
