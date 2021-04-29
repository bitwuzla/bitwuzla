#include "test.h"
namespace bzlals {
namespace test {

class TestBvNodeSelPath : public TestBvNode
{
 protected:
  template <class T>
  void test_binary(OpKind op_kind);
};

template <class T>
void
TestBvNodeSelPath::test_binary(OpKind op_kind)
{
  uint32_t bw_s0 = TEST_BW;
  uint32_t bw_s1 = TEST_BW;
  uint32_t bw_t  = TEST_BW;

  if (op_kind == ULT || op_kind == SLT || op_kind == EQ)
  {
    bw_t = 1;
  }
  else if (op_kind == CONCAT)
  {
    bw_s1 = 2; /* decrease number of tests for concat */
    bw_t  = bw_s0 + bw_s1;
  }

  uint32_t nval_t = 1 << bw_t;

  std::vector<std::string>& s0values = d_xvalues;
  std::vector<std::string> s1values;
  if (op_kind == CONCAT)
  {
    gen_xvalues(bw_s1, s1values);
  }
  else
  {
    s1values = d_xvalues;
  }

  bool test_both_const_leafs = true;
  bool test_both_const_ops   = true;

  for (const std::string& s0_value : s0values)
  {
    BitVectorDomain s0(s0_value);
    for (const std::string& s1_value : s1values)
    {
      BitVectorDomain s1(s1_value);
      for (uint32_t j = 0; j < nval_t; j++)
      {
        /* Target value of the operation (op). */
        BitVector t(bw_t, j);

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

        uint32_t pos_x;
        bool is_const0, is_const1;
        bool is_essential0, is_essential1;

        /* Both operands leaf nodes. */
        std::unique_ptr<BitVectorNode> leaf0(
            new BitVectorNode(d_rng.get(), s0_val, s0));
        std::unique_ptr<BitVectorNode> leaf1(
            new BitVectorNode(d_rng.get(), s1_val, s1));
        T lop(d_rng.get(), bw_t, leaf0.get(), leaf1.get());
        is_const0     = lop[0]->is_const();
        is_const1     = lop[1]->is_const();
        is_essential0 = lop.is_essential(t, 0);
        is_essential1 = lop.is_essential(t, 1);
        /* we only perform this death test once (for performance reasons) */
        if (is_const0 && is_const1)
        {
          if (test_both_const_leafs)
          {
            ASSERT_DEATH(lop.select_path(t), "!all_const");
            test_both_const_leafs = false;
          }
          continue;
        }
        pos_x = lop.select_path(t);
        ASSERT_TRUE(!is_const0 || pos_x == 1);
        ASSERT_TRUE(!is_const1 || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential0
                    || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential1
                    || pos_x == 1);

        /* Both operands ops. */
        std::unique_ptr<BitVectorNode> child(
            new BitVectorNode(d_rng.get(), bw_t));
        std::unique_ptr<BitVectorNode> op_s0(
            new T(d_rng.get(), s0_val, s0, child.get(), child.get()));
        std::unique_ptr<BitVectorNode> op_s1(
            new T(d_rng.get(), s1_val, s1, child.get(), child.get()));
        T oop(d_rng.get(), bw_t, op_s0.get(), op_s1.get());
        is_const0     = lop[0]->is_const();
        is_const1     = lop[1]->is_const();
        is_essential0 = oop.is_essential(t, 0);
        is_essential1 = oop.is_essential(t, 1);
        /* we only perform this death test once (for performance reasons) */
        if (is_const0 && is_const1)
        {
          if (test_both_const_ops)
          {
            ASSERT_DEATH(oop.select_path(t), "!all_const");
            test_both_const_ops = false;
          }
          continue;
        }
        pos_x = oop.select_path(t);
        ASSERT_TRUE(!is_const0 || pos_x == 1);
        ASSERT_TRUE(!is_const1 || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential0
                    || pos_x == 0);
        ASSERT_TRUE((is_essential0 && is_essential1) || !is_essential1
                    || pos_x == 1);
      }
    }
  }
}

TEST_F(TestBvNodeSelPath, add)
{
  test_binary<BitVectorAdd>(ADD);
  test_binary<BitVectorAdd>(ADD);
}

}  // namespace test
}  // namespace bzlals
