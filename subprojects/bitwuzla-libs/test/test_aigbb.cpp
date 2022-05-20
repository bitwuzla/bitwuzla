#include <filesystem>

#include "bb/aigmgr.h"
#include "test.h"

namespace bzla::test {

class TestAigBitblaster : public TestCommon
{
};

#define TEST_BIN_OP(size, op, func)  \
  {                                  \
    bb::AigBitblaster bb;            \
    auto a   = bb.bv_constant(size); \
    auto b   = bb.bv_constant(size); \
    auto res = bb.func(a, b);        \
    test_binary(op, res, a, b);      \
  }

TEST_F(TestAigBitblaster, ctor_dtor) { bb::AigBitblaster bb; }

TEST_F(TestAigBitblaster, bv_value)
{
  BitVector zero(32, 0);
  BitVector ones = zero.bvnot();
  BitVector val(32, 2863311530);  // 101010...

  bb::AigBitblaster bb;
  auto bb_zero = bb.bv_value(zero);
  for (const auto& bit : bb_zero)
  {
    ASSERT_TRUE(bit.is_false());
  }

  auto bb_ones = bb.bv_value(ones);
  for (const auto& bit : bb_ones)
  {
    ASSERT_TRUE(bit.is_true());
  }

  auto bb_val = bb.bv_value(val);
  for (size_t i = 0; i < bb_val.size(); ++i)
  {
    // even is 1
    if (i % 2 == 0)
    {
      ASSERT_TRUE(bb_val[i].is_true());
    }
    // odd is 0
    else
    {
      ASSERT_TRUE(bb_val[i].is_false());
    }
  }
}

TEST_F(TestAigBitblaster, bv_constant)
{
  bb::AigBitblaster bb;

  auto bits = bb.bv_constant(12);
  ASSERT_EQ(bits.size(), 12);
}

TEST_F(TestAigBitblaster, bv_not)
{
  BitVector zero(32, 0);
  BitVector ones = zero.bvnot();

  bb::AigBitblaster bb;
  auto bb_zero  = bb.bv_value(zero);
  auto bb_ones  = bb.bv_value(ones);
  auto bb_const = bb.bv_constant(8);

  ASSERT_EQ(bb_zero, bb.bv_not(bb_ones));
  ASSERT_EQ(bb_ones, bb.bv_not(bb_zero));
  ASSERT_EQ(bb_const, bb.bv_not(bb.bv_not(bb_const)));
}

}  // namespace bzla::test
