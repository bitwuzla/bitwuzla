#include "test_bvnode.h"

namespace bzla::ls::test {

TEST_F(TestBvNode, normalize_bounds)
{
  BitVector min_lo, min_hi, max_lo, max_hi;

  BitVector zero = BitVector::mk_zero(TEST_BW);
  BitVector ones = BitVector::mk_ones(TEST_BW);
  BitVector smin = BitVector::mk_min_signed(TEST_BW);
  BitVector smax = BitVector::mk_max_signed(TEST_BW);

  BitVectorNode node(d_rng.get(), TEST_BW);

  // no signed bounds ------------------------------------------------------

  // unsigned: [0000, 0111]
  // signed:   [0000, 0111]
  node.update_bounds(zero, smax, false, false, false);
  node.update_bounds(zero, smax, false, false, true);
  node.normalize_bounds(min_lo, min_hi, max_lo, max_hi);
  ASSERT_TRUE(min_lo.is_null());
  ASSERT_TRUE(min_hi.is_null());
  ASSERT_EQ(max_lo.compare(zero), 0);
  ASSERT_EQ(max_hi.compare(smax), 0);

  // no unsigned bounds
  // overlap in [0 ... ones]
  // overlap in [smin ... smax]
  // overlap in [0 ... ones] and [smin ... smax]
  // no overlap
  //
  // TODO exclusive bounds
}

}  // namespace bzla::ls::test
