#include "test_ls_common.h"

namespace bzla {
namespace ls {
namespace test {

/* -------------------------------------------------------------------------- */

class TestBvNodeInv : public TestBvNode
{
 protected:
  template <class T>
  void test_inv_ineq_concat(OpKind op_kind,
                            uint32_t pos_x,
                            bool use_bounds = false);
};

template <class T>
void
TestBvNodeInv::test_inv_ineq_concat(OpKind op_kind,
                                    uint32_t pos_x,
                                    bool use_bounds)
{
  assert(op_kind == ULT || op_kind == SLT);

  uint32_t bw_x = TEST_BW;
  uint32_t bw_s = TEST_BW;
  uint32_t bw_t = 1;

  uint32_t nval_s = 1 << bw_s;
  uint32_t nval_t = 1 << bw_t;

  for (const std::string& x_value : d_xvalues)
  {
    BitVectorDomain x(x_value);
    for (uint32_t i = 0; i < nval_s; i++)
    {
      /* Assignment of the other operand. */
      BitVector s_val(bw_s, i);
      for (uint32_t j = 0; j < nval_t; j++)
      {
        /* Target value of the operation (op). */
        BitVector t(bw_t, j);
        /* For this test, we don't care about the current assignment of x,
         * thus we initialize it with a random value that matches constant
         * bits in x. */
        BitVector x_val = x.lo();
        if (!x.is_fixed())
        {
          BitVectorDomainGenerator gen(x, d_rng.get());
          x_val = gen.random();
        }

        bool is_signed   = op_kind == SLT;
        uint32_t n_tests = 0;
        std::unique_ptr<BitVector> min, max;
        do
        {
          uint32_t bw_x0     = d_rng->pick<uint32_t>(1, TEST_BW - 1);
          uint32_t bw_x1     = bw_x - bw_x0;
          BitVectorDomain x0 = x.bvextract(bw_x - 1, bw_x1);
          BitVectorDomain x1 = x.bvextract(bw_x1 - 1, 0);
          BitVector x0_val   = x_val.bvextract(bw_x - 1, bw_x1);
          BitVector x1_val   = x_val.bvextract(bw_x1 - 1, 0);

          std::unique_ptr<BitVectorNode> op_x0(
              new BitVectorNode(d_rng.get(), x0_val, x0));
          std::unique_ptr<BitVectorNode> op_x1(
              new BitVectorNode(d_rng.get(), x1_val, x1));
          std::unique_ptr<BitVectorNode> op_x(
              new BitVectorConcat(d_rng.get(), x, op_x0.get(), op_x1.get()));

          /* For this test, we don't care about the domain of s, thus we
           * initialize it with an unconstrained domain. */
          BitVectorDomain s(bw_s);
          std::unique_ptr<BitVectorNode> op_s(
              new BitVectorNode(d_rng.get(), s_val, s));
          /* For this test, we don't care about current assignment and domain
           * of the op and initialize them with 0 and x..x, respectively. */
          T op(d_rng.get(),
               bw_t,
               pos_x == 0 ? op_x.get() : op_s.get(),
               pos_x == 1 ? op_x.get() : op_s.get(),
               true);

          if (use_bounds)
          {
            min.reset(new BitVector(bw_x, *d_rng.get()));
            max.reset(new BitVector(bw_x,
                                    *d_rng.get(),
                                    *min,
                                    is_signed ? BitVector::mk_max_signed(bw_x)
                                              : BitVector::mk_ones(bw_x),
                                    is_signed));
            op_x->update_min_bound(*min, is_signed, false);
            op_x->update_max_bound(*max, is_signed, false);
          }

          if (!op.is_invertible(t, pos_x)) continue;
          if (x.is_fixed()) continue;
          BitVector inv = op.inverse_value(t, pos_x);
          int32_t cmp   = t.compare(eval_op_binary(op_kind, inv, s_val, pos_x));
          if (cmp != 0)
          {
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "t: " << t << std::endl;
            std::cout << "x: " << x_value << ": " << x_val << std::endl;
            std::cout << "s: " << s_val << std::endl;
            std::cout << "inverse: " << inv << std::endl;
          }
          ASSERT_EQ(cmp, 0);
          ASSERT_TRUE(op.is_consistent(t, pos_x));
        } while (use_bounds && ++n_tests < 10);
      }
    }
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBvNodeInv, add)
{
  test_binary<BitVectorAdd>(INV, ADD, 0);
  test_binary<BitVectorAdd>(INV, ADD, 1);
}

TEST_F(TestBvNodeInv, and)
{
  test_binary<BitVectorAnd>(INV, AND, 0);
  test_binary<BitVectorAnd>(INV, AND, 1);
  test_binary<BitVectorAnd>(INV, AND, 0, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(INV, AND, 1, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(INV, AND, 0, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorAnd>(INV, AND, 1, TestBvNode::BoundsKind::SIGNED);
}

TEST_F(TestBvNodeInv, concat)
{
  test_binary<BitVectorConcat>(INV, CONCAT, 0);
  test_binary<BitVectorConcat>(INV, CONCAT, 1);
}

TEST_F(TestBvNodeInv, eq)
{
  test_binary<BitVectorEq>(INV, EQ, 0);
  test_binary<BitVectorEq>(INV, EQ, 1);
}

TEST_F(TestBvNodeInv, mul)
{
  test_binary<BitVectorMul>(INV, MUL, 0);
  test_binary<BitVectorMul>(INV, MUL, 1);
}

TEST_F(TestBvNodeInv, shl)
{
  test_binary<BitVectorShl>(INV, SHL, 0);
  test_binary<BitVectorShl>(INV, SHL, 1);
}

TEST_F(TestBvNodeInv, shr)
{
  test_binary<BitVectorShr>(INV, SHR, 0);
  test_binary<BitVectorShr>(INV, SHR, 1);
}

TEST_F(TestBvNodeInv, ashr)
{
  test_binary<BitVectorAshr>(INV, ASHR, 0);
  test_binary<BitVectorAshr>(INV, ASHR, 1);
}

TEST_F(TestBvNodeInv, slt)
{
  test_binary<BitVectorSlt>(INV, SLT, 0);
  test_binary<BitVectorSlt>(INV, SLT, 1);
  // test_binary<BitVectorSlt>(INV, SLT, 0, TestBvNode::BoundsKind::UNSIGNED);
  // test_binary<BitVectorSlt>(INV, SLT, 1, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorSlt>(INV, SLT, 0, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorSlt>(INV, SLT, 1, TestBvNode::BoundsKind::SIGNED);
}

TEST_F(TestBvNodeInv, udiv)
{
  test_binary<BitVectorUdiv>(INV, UDIV, 0);
  test_binary<BitVectorUdiv>(INV, UDIV, 1);
}

TEST_F(TestBvNodeInv, ult)
{
  test_binary<BitVectorUlt>(INV, ULT, 0);
  test_binary<BitVectorUlt>(INV, ULT, 1);
  test_binary<BitVectorUlt>(INV, ULT, 0, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorUlt>(INV, ULT, 1, TestBvNode::BoundsKind::UNSIGNED);
  // test_binary<BitVectorUlt>(INV, ULT, 0, TestBvNode::BoundsKind::SIGNED);
  // test_binary<BitVectorUlt>(INV, ULT, 1, TestBvNode::BoundsKind::SIGNED);
}

TEST_F(TestBvNodeInv, ult_concat)
{
  test_inv_ineq_concat<BitVectorUlt>(ULT, 0);
  test_inv_ineq_concat<BitVectorUlt>(ULT, 1);
  test_inv_ineq_concat<BitVectorUlt>(ULT, 0, true);
  test_inv_ineq_concat<BitVectorUlt>(ULT, 1, true);
}

TEST_F(TestBvNodeInv, urem)
{
  test_binary<BitVectorUrem>(INV, UREM, 0);
  test_binary<BitVectorUrem>(INV, UREM, 1);
}

TEST_F(TestBvNodeInv, xor)
{
  test_binary<BitVectorXor>(INV, XOR, 0);
  test_binary<BitVectorXor>(INV, XOR, 1);
}

TEST_F(TestBvNodeInv, ite)
{
  test_ite(INV, 0);
  test_ite(INV, 1);
  test_ite(INV, 2);
}

TEST_F(TestBvNodeInv, not ) { test_not(INV); }

TEST_F(TestBvNodeInv, extract) { test_extract(INV); }

TEST_F(TestBvNodeInv, sext) { test_sext(INV); }

}  // namespace test
}  // namespace ls
}  // namespace bzla
