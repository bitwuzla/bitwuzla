/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "test_bvnode.h"

namespace bzla::ls::test {

class TestBvNodeSelPath : public TestBvNode
{
 protected:
  void SetUp() override
  {
    TestBvNode::SetUp();
    /* We want to test deterministically, with selecting essential inputs when
     * there are any. For this we additionally have to set the probability of
     * selecting essential inputs to 100% to disables random input selection in
     * essential path selection mode, which is performed with (the complement of
     * this) configured probability for completeness.
     */
    BitVectorNode::s_path_sel_essential  = true;
    BitVectorNode::s_prob_pick_ess_input = 1000;
  }
  template <class T>
  void test_binary(NodeKind kind);
  void test_ite();
  void test_not();
  void test_extract();
  void test_sext();
};

template <class T>
void
TestBvNodeSelPath::test_binary(NodeKind kind)
{
  uint64_t bw_s0 = TEST_BW;
  uint64_t bw_s1 = TEST_BW;
  uint64_t bw_t  = TEST_BW;

  if (kind == NodeKind::BV_ULT || kind == NodeKind::BV_SLT
      || kind == NodeKind::EQ)
  {
    bw_t = 1;
  }
  else if (kind == NodeKind::BV_CONCAT)
  {
    bw_s1 = 2; /* decrease number of tests for concat */
    bw_t  = bw_s0 + bw_s1;
  }

  uint64_t nval_t = 1 << bw_t;

  std::vector<std::string>& s0values = d_xvalues;
  std::vector<std::string> s1values;
  if (kind == NodeKind::BV_CONCAT)
  {
    gen_xvalues(bw_s1, s1values);
  }
  else
  {
    s1values = d_xvalues;
  }

  bool test_both_const_leafs = true;
  bool test_both_const_ops   = true;
  std::vector<uint64_t> ess_inputs;

  for (const std::string& s0_value : s0values)
  {
    BitVectorDomain s0(s0_value);
    for (const std::string& s1_value : s1values)
    {
      BitVectorDomain s1(s1_value);
      for (uint64_t j = 0; j < nval_t; ++j)
      {
        /* Target value of the operation (op). */
        BitVector t = BitVector::from_ui(bw_t, j);

        /* The current assignment of the operands, we choose a random value. */
        BitVector s0_val = s0.lo();
        if (!s0.is_fixed())
        {
          BitVectorDomainGenerator gen(s0, d_rng.get());
          s0_val = gen.random();
        }
        BitVector s1_val = s1.lo();
        if (!s1.is_fixed())
        {
          BitVectorDomainGenerator gen(s1, d_rng.get());
          s1_val = gen.random();
        }

        uint64_t pos_x;
        bool is_val0, is_val1;
        bool is_essential0, is_essential1;

        /* Both operands leaf nodes. */
        std::unique_ptr<BitVectorNode> leaf0(
            new BitVectorNode(d_rng.get(), s0_val, s0));
        std::unique_ptr<BitVectorNode> leaf1(
            new BitVectorNode(d_rng.get(), s1_val, s1));
        T lop(d_rng.get(), bw_t, leaf0.get(), leaf1.get());
        is_val0       = lop[0]->is_value();
        is_val1       = lop[1]->is_value();
        is_essential0 = lop.is_essential(t, 0);
        is_essential1 = lop.is_essential(t, 1);
        /* we only perform this death test once (for performance reasons) */
        if (is_val0 && is_val1)
        {
          if (test_both_const_leafs)
          {
            ASSERT_DEATH_DEBUG(lop.select_path(t, ess_inputs), "!all_value");
            test_both_const_leafs = false;
          }
          continue;
        }
        pos_x = std::get<0>(lop.select_path(t, ess_inputs));
        ASSERT_TRUE(!is_val0 || pos_x == 1);
        ASSERT_TRUE(!is_val1 || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential0
                    || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential1
                    || pos_x == 1);

        /* Both operands ops. */
        std::unique_ptr<BitVectorNode> child0(
            new BitVectorNode(d_rng.get(), bw_s0));
        std::unique_ptr<BitVectorNode> child1(
            new BitVectorNode(d_rng.get(), bw_s1));
        std::unique_ptr<BitVectorNode> op_s0(
            new BitVectorAnd(d_rng.get(), s0, child0.get(), child0.get()));
        std::unique_ptr<BitVectorNode> op_s1(
            new BitVectorAdd(d_rng.get(), s1, child1.get(), child1.get()));
        T oop(d_rng.get(), bw_t, op_s0.get(), op_s1.get());
        is_val0       = lop[0]->is_value();
        is_val1       = lop[1]->is_value();
        is_essential0 = oop.is_essential(t, 0);
        is_essential1 = oop.is_essential(t, 1);
        /* we only perform this death test once (for performance reasons) */
        if (is_val0 && is_val1)
        {
          if (test_both_const_ops)
          {
            ASSERT_DEATH_DEBUG(oop.select_path(t, ess_inputs), "!all_value");
            test_both_const_ops = false;
          }
          continue;
        }
        pos_x = std::get<0>(oop.select_path(t, ess_inputs));
        assert(!(pos_x == 0 ? is_val0 : is_val1));
        ASSERT_FALSE(pos_x == 0 ? is_val0 : is_val1);
        ASSERT_TRUE(!is_val0 || pos_x == 1);
        ASSERT_TRUE(!is_val1 || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential0
                    || is_val0 || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential1
                    || is_val1 || pos_x == 1);
      }
    }
  }
}

void
TestBvNodeSelPath::test_ite()
{
  uint64_t bw_t = TEST_BW;

  uint64_t nval_t = 1 << bw_t;

  std::vector<std::string> s0values  = {"x", "0", "1"};
  std::vector<std::string>& s1values = d_xvalues;
  std::vector<std::string>& s2values = d_xvalues;

  bool test_all_value_leafs = true;
  bool test_all_value_ops   = true;
  std::vector<uint64_t> ess_inputs;

  for (const std::string& s0_value : s0values)
  {
    BitVectorDomain s0(s0_value);
    for (const std::string& s1_value : s1values)
    {
      BitVectorDomain s1(s1_value);
      for (const std::string& s2_value : s2values)
      {
        BitVectorDomain s2(s2_value);

        for (uint64_t j = 0; j < nval_t; ++j)
        {
          /* Target value of the operation (op). */
          BitVector t = BitVector::from_ui(bw_t, j);

          /* Current assignment of the operands, we choose a random value. */
          BitVector s0_val = s0.lo();
          if (!s0.is_fixed())
          {
            BitVectorDomainGenerator gen(s0, d_rng.get());
            s0_val = gen.random();
          }
          BitVector s1_val = s1.lo();
          if (!s1.is_fixed())
          {
            BitVectorDomainGenerator gen(s1, d_rng.get());
            s1_val = gen.random();
          }
          BitVector s2_val = s2.lo();
          if (!s2.is_fixed())
          {
            BitVectorDomainGenerator gen(s2, d_rng.get());
            s2_val = gen.random();
          }

          uint64_t pos_x;
          bool is_val0, is_val1, is_val2;
          bool is_essential0, is_essential1, is_essential2;

          /* Both operands leaf nodes. */
          std::unique_ptr<BitVectorNode> leaf0(
              new BitVectorNode(d_rng.get(), s0_val, s0));
          std::unique_ptr<BitVectorNode> leaf1(
              new BitVectorNode(d_rng.get(), s1_val, s1));
          std::unique_ptr<BitVectorNode> leaf2(
              new BitVectorNode(d_rng.get(), s2_val, s2));
          BitVectorIte lop(
              d_rng.get(), bw_t, leaf0.get(), leaf1.get(), leaf2.get());
          is_val0       = lop[0]->is_value();
          is_val1       = lop[1]->is_value();
          is_val2       = lop[2]->is_value();
          is_essential0 = lop.is_essential(t, 0);
          is_essential1 = lop.is_essential(t, 1);
          is_essential2 = lop.is_essential(t, 2);
          /* we only perform this death test once (for performance reasons) */
          if (is_val0 && is_val1 && is_val2)
          {
            if (test_all_value_leafs)
            {
              ASSERT_DEATH_DEBUG(lop.select_path(t, ess_inputs), "!all_value");
              test_all_value_leafs = false;
            }
            continue;
          }
          pos_x = std::get<0>(lop.select_path(t, ess_inputs));
          ASSERT_FALSE(pos_x == 0 ? is_val0 : (pos_x == 1 ? is_val1 : is_val2));
          ASSERT_TRUE(!is_val1 || !is_val2 || pos_x == 0);
          ASSERT_TRUE(!is_val0 || !is_val2 || pos_x == 1);
          ASSERT_TRUE(!is_val0 || !is_val1 || pos_x == 2);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential0 || pos_x == 0);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential1 || pos_x == 1);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential2 || pos_x == 2);

          /* All operands ops. */
          std::unique_ptr<BitVectorNode> child1(
              new BitVectorNode(d_rng.get(), 1));
          std::unique_ptr<BitVectorNode> childbwt(
              new BitVectorNode(d_rng.get(), bw_t));
          std::unique_ptr<BitVectorNode> op_s0(
              new BitVectorAnd(d_rng.get(), s0, child1.get(), child1.get()));
          std::unique_ptr<BitVectorNode> op_s1(new BitVectorAdd(
              d_rng.get(), s1, childbwt.get(), childbwt.get()));
          std::unique_ptr<BitVectorNode> op_s2(new BitVectorMul(
              d_rng.get(), s2, childbwt.get(), childbwt.get()));
          BitVectorIte oop(
              d_rng.get(), bw_t, op_s0.get(), op_s1.get(), op_s2.get());
          is_val0       = lop[0]->is_value();
          is_val1       = lop[1]->is_value();
          is_val2       = lop[2]->is_value();
          is_essential0 = oop.is_essential(t, 0);
          is_essential1 = oop.is_essential(t, 1);
          is_essential2 = oop.is_essential(t, 2);
          /* we only perform this death test once (for performance reasons) */
          if (is_val0 && is_val1 && is_val2)
          {
            if (test_all_value_ops)
            {
              ASSERT_DEATH_DEBUG(oop.select_path(t, ess_inputs), "!all_value");
              test_all_value_ops = false;
            }
            continue;
          }
          pos_x = std::get<0>(oop.select_path(t, ess_inputs));
          ASSERT_TRUE(!is_val1 || !is_val2 || pos_x == 0);
          ASSERT_TRUE(!is_val0 || !is_val2 || pos_x == 1);
          ASSERT_TRUE(!is_val0 || !is_val1 || pos_x == 2);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential0 || is_val0 || pos_x == 0);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential1 || is_val1 || pos_x == 1);
          ASSERT_TRUE((is_essential0 && is_essential1 && is_essential2)
                      || !is_essential2 || is_val2 || pos_x == 2);
        }
      }
    }
  }
}

void
TestBvNodeSelPath::test_not()
{
  uint64_t bw_t = TEST_BW;

  bool test_const_leaf = true;
  bool test_const_op   = true;
  std::vector<uint64_t> ess_inputs;

  for (const std::string& s0_value : d_xvalues)
  {
    BitVectorDomain s0(s0_value);
    for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
    {
      /* Target value of the operation (op). */
      BitVector t = BitVector::from_ui(bw_t, i);

      /* The current assignment of the operands, we choose a random value. */
      BitVector s0_val = s0.lo();
      if (!s0.is_fixed())
      {
        BitVectorDomainGenerator gen(s0, d_rng.get());
        s0_val = gen.random();
      }

      uint64_t pos_x;
      bool is_val;
      bool is_essential;

      /* Operand is leaf node. */
      std::unique_ptr<BitVectorNode> leaf0(
          new BitVectorNode(d_rng.get(), s0_val, s0));
      BitVectorNot lop(d_rng.get(), bw_t, leaf0.get());
      is_val       = lop[0]->is_value();
      is_essential = lop.is_essential(t, 0);
      /* we only perform this death test once (for performance reasons) */
      if (is_val)
      {
        if (test_const_leaf)
        {
          ASSERT_DEATH_DEBUG(lop.select_path(t, ess_inputs), "!all_value");
          test_const_leaf = false;
        }
        continue;
      }
      pos_x = std::get<0>(lop.select_path(t, ess_inputs));
      ASSERT_TRUE(is_val || pos_x == 0);
      ASSERT_TRUE(is_essential || pos_x == 0);

      /* Operands is op. */
      std::unique_ptr<BitVectorNode> child(
          new BitVectorNode(d_rng.get(), bw_t));
      std::unique_ptr<BitVectorNode> op_s0(
          new BitVectorNot(d_rng.get(), s0, child.get()));
      BitVectorNot oop(d_rng.get(), bw_t, op_s0.get());
      is_val       = lop[0]->is_value();
      is_essential = oop.is_essential(t, 0);
      /* we only perform this death test once (for performance reasons) */
      if (is_val)
      {
        if (test_const_op)
        {
          ASSERT_DEATH_DEBUG(oop.select_path(t, ess_inputs), "!all_value");
          test_const_op = false;
        }
        continue;
      }
      pos_x = std::get<0>(oop.select_path(t, ess_inputs));
      ASSERT_TRUE(!is_val || pos_x == 0);
      ASSERT_TRUE(is_essential || is_val || pos_x == 0);
    }
  }
}

void
TestBvNodeSelPath::test_extract()
{
  uint64_t bw_x = TEST_BW;

  bool test_const_leaf = true;
  bool test_const_op   = true;
  std::vector<uint64_t> ess_inputs;

  for (const std::string& s0_value : d_xvalues)
  {
    BitVectorDomain s0(s0_value);
    for (uint64_t lo = 0; lo < bw_x; ++lo)
    {
      for (uint64_t hi = lo; hi < bw_x; ++hi)
      {
        uint64_t bw_t = hi - lo + 1;
        for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
        {
          /* Target value of the operation (op). */
          BitVector t = BitVector::from_ui(bw_t, i);

          /* The current assignment of the operands, we choose a random value.
           */
          BitVector s0_val = s0.lo();
          if (!s0.is_fixed())
          {
            BitVectorDomainGenerator gen(s0, d_rng.get());
            s0_val = gen.random();
          }

          uint64_t pos_x;
          bool is_val;
          bool is_essential;

          /* Operand is leaf node. */
          std::unique_ptr<BitVectorNode> leaf0(
              new BitVectorNode(d_rng.get(), s0_val, s0));
          BitVectorExtract lop(d_rng.get(), bw_t, leaf0.get(), hi, lo, false);
          is_val       = lop[0]->is_value();
          is_essential = lop.is_essential(t, 0);
          /* we only perform this death test once (for performance reasons) */
          if (is_val)
          {
            if (test_const_leaf)
            {
              ASSERT_DEATH_DEBUG(lop.select_path(t, ess_inputs), "!all_value");
              test_const_leaf = false;
            }
            continue;
          }
          pos_x = std::get<0>(lop.select_path(t, ess_inputs));
          ASSERT_TRUE(is_val || pos_x == 0);
          ASSERT_TRUE(is_essential || pos_x == 0);

          /* Operands is op. */
          std::unique_ptr<BitVectorNode> child(
              new BitVectorNode(d_rng.get(), bw_x));
          std::unique_ptr<BitVectorNode> op_s0(
              new BitVectorMul(d_rng.get(), s0, child.get(), child.get()));
          BitVectorExtract oop(d_rng.get(), bw_t, op_s0.get(), hi, lo, false);
          is_val       = lop[0]->is_value();
          is_essential = oop.is_essential(t, 0);
          /* we only perform this death test once (for performance reasons) */
          if (is_val)
          {
            if (test_const_op)
            {
              ASSERT_DEATH_DEBUG(oop.select_path(t, ess_inputs), "!all_value");
              test_const_op = false;
            }
            continue;
          }
          pos_x = std::get<0>(oop.select_path(t, ess_inputs));
          ASSERT_TRUE(!is_val || pos_x == 0);
          ASSERT_TRUE(is_essential || is_val || pos_x == 0);
        }
      }
    }
  }
}

void
TestBvNodeSelPath::test_sext()
{
  uint64_t bw_x = TEST_BW;

  bool test_const_leaf = true;
  bool test_const_op   = true;
  std::vector<uint64_t> ess_inputs;

  for (const std::string& s0_value : d_xvalues)
  {
    BitVectorDomain s0(s0_value);
    for (uint64_t n = 1; n <= bw_x; ++n)
    {
      uint64_t bw_t = bw_x + n;
      for (uint64_t i = 0, m = 1 << bw_t; i < m; ++i)
      {
        /* Target value of the operation (op). */
        BitVector t = BitVector::from_ui(bw_t, i);

        /* The current assignment of the operands, we choose a random value. */
        BitVector s0_val = s0.lo();
        if (!s0.is_fixed())
        {
          BitVectorDomainGenerator gen(s0, d_rng.get());
          s0_val = gen.random();
        }

        uint64_t pos_x;
        bool is_val;
        bool is_essential;

        /* Operand is leaf node. */
        std::unique_ptr<BitVectorNode> leaf0(
            new BitVectorNode(d_rng.get(), s0_val, s0));
        BitVectorSignExtend lop(d_rng.get(), bw_t, leaf0.get(), n);
        is_val       = lop[0]->is_value();
        is_essential = lop.is_essential(t, 0);
        /* we only perform this death test once (for performance reasons) */
        if (is_val)
        {
          if (test_const_leaf)
          {
            ASSERT_DEATH_DEBUG(lop.select_path(t, ess_inputs), "!all_value");
            test_const_leaf = false;
          }
          continue;
        }
        pos_x = std::get<0>(lop.select_path(t, ess_inputs));
        ASSERT_TRUE(is_val || pos_x == 0);
        ASSERT_TRUE(is_essential || pos_x == 0);

        /* Operands is op. */
        std::unique_ptr<BitVectorNode> child(
            new BitVectorNode(d_rng.get(), bw_x));
        std::unique_ptr<BitVectorNode> op_s0(
            new BitVectorUdiv(d_rng.get(), s0, child.get(), child.get()));
        BitVectorSignExtend oop(d_rng.get(), bw_t, op_s0.get(), n);
        is_val       = lop[0]->is_value();
        is_essential = oop.is_essential(t, 0);
        /* we only perform this death test once (for performance reasons) */
        if (is_val)
        {
          if (test_const_op)
          {
            ASSERT_DEATH_DEBUG(oop.select_path(t, ess_inputs), "!all_value");
            test_const_op = false;
          }
          continue;
        }
        pos_x = std::get<0>(oop.select_path(t, ess_inputs));
        ASSERT_TRUE(!is_val || pos_x == 0);
        ASSERT_TRUE(is_essential || is_val || pos_x == 0);
      }
    }
  }
}

TEST_F(TestBvNodeSelPath, add) { test_binary<BitVectorAdd>(NodeKind::BV_ADD); }

TEST_F(TestBvNodeSelPath, and) { test_binary<BitVectorAnd>(NodeKind::BV_AND); }

TEST_F(TestBvNodeSelPath, concat)
{
  test_binary<BitVectorConcat>(NodeKind::BV_CONCAT);
}

TEST_F(TestBvNodeSelPath, eq) { test_binary<BitVectorEq>(NodeKind::EQ); }

TEST_F(TestBvNodeSelPath, mul) { test_binary<BitVectorMul>(NodeKind::BV_MUL); }

TEST_F(TestBvNodeSelPath, shl) { test_binary<BitVectorShl>(NodeKind::BV_SHL); }

TEST_F(TestBvNodeSelPath, shr) { test_binary<BitVectorShr>(NodeKind::BV_SHR); }

TEST_F(TestBvNodeSelPath, ashr)
{
  test_binary<BitVectorAshr>(NodeKind::BV_ASHR);
}

TEST_F(TestBvNodeSelPath, udiv)
{
  test_binary<BitVectorUdiv>(NodeKind::BV_UDIV);
}

TEST_F(TestBvNodeSelPath, ult) { test_binary<BitVectorUlt>(NodeKind::BV_ULT); }

TEST_F(TestBvNodeSelPath, slt) { test_binary<BitVectorSlt>(NodeKind::BV_SLT); }

TEST_F(TestBvNodeSelPath, urem)
{
  test_binary<BitVectorUrem>(NodeKind::BV_UREM);
}

TEST_F(TestBvNodeSelPath, xor) { test_binary<BitVectorXor>(NodeKind::BV_XOR); }

TEST_F(TestBvNodeSelPath, ite) { test_ite(); }

TEST_F(TestBvNodeSelPath, not ) { test_not(); }

TEST_F(TestBvNodeSelPath, extract) { test_extract(); }

TEST_F(TestBvNodeSelPath, sext) { test_sext(); }

}  // namespace bzla::ls::test
