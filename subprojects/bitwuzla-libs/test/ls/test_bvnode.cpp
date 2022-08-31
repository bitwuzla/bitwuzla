#include "test_bvnode.h"

namespace bzla::ls::test {

void
TestBvNode::test_normalize_bounds(const BitVector& min_u,
                                  bool min_u_is_excl,
                                  const BitVector& max_u,
                                  bool max_u_is_excl,
                                  const BitVector& min_s,
                                  bool min_s_is_excl,
                                  const BitVector& max_s,
                                  bool max_s_is_excl,
                                  const BitVector& min_lo_exp,
                                  const BitVector& min_hi_exp,
                                  const BitVector& max_lo_exp,
                                  const BitVector& max_hi_exp)
{
  BitVector min_lo, min_hi, max_lo, max_hi;
  BitVectorNode node(d_rng.get(), 4);
  if (!min_u.is_null())
  {
    assert(!max_u.is_null());
    if (min_u.compare(max_u) > 0)
    {
      ASSERT_DEATH(
          node.update_bounds(min_u, max_u, min_u_is_excl, max_u_is_excl, false),
          "compare");
    }
    else
    {
      node.update_bounds(min_u, max_u, min_u_is_excl, max_u_is_excl, false);
    }
  }
  if (!min_s.is_null())
  {
    assert(!max_s.is_null());
    if (min_s.signed_compare(max_s) > 0)
    {
      ASSERT_DEATH(
          node.update_bounds(min_s, max_s, min_s_is_excl, max_s_is_excl, true),
          "signed_compare");
    }
    else
    {
      node.update_bounds(min_s, max_s, min_s_is_excl, max_s_is_excl, true);
    }
  }
  node.normalize_bounds(min_lo, min_hi, max_lo, max_hi);
  ASSERT_EQ(min_lo.is_null(), min_lo_exp.is_null());
  ASSERT_EQ(min_hi.is_null(), min_hi_exp.is_null());
  ASSERT_EQ(max_lo.is_null(), max_lo_exp.is_null());
  ASSERT_EQ(max_hi.is_null(), max_hi_exp.is_null());
  ASSERT_TRUE(min_lo.is_null() || min_lo.compare(min_lo_exp) == 0);
  ASSERT_TRUE(min_hi.is_null() || min_lo.compare(min_lo_exp) == 0);
  ASSERT_TRUE(max_lo.is_null() || max_lo.compare(max_lo_exp) == 0);
  ASSERT_TRUE(max_hi.is_null() || max_lo.compare(max_lo_exp) == 0);
}

void
TestBvNode::test_normalize_bounds_no_u()
{
  // no bounds exclusive -----------------------------
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0000"),
                        BitVector(4, "0111"));
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1111"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "1111"),
                        BitVector(4, "1111"),
                        BitVector(4, "0000"),
                        BitVector(4, "0000"));
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1101"),
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "1101"),
                        BitVector(4, "1111"),
                        BitVector(4, "0000"),
                        BitVector(4, "0111"));
  // some bounds exclusive ---------------------------
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0111"));
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        false,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "1000"),
                        BitVector(4, "1110"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "0000"),
                        true,
                        BitVector(4, "1111"),
                        BitVector(4, "1111"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1101"),
                        false,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "1101"),
                        BitVector(4, "1111"),
                        BitVector(4, "0000"),
                        BitVector(4, "0110"));
  // all bounds exclusive ----------------------------
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0110"));
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "1001"),
                        BitVector(4, "1110"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "0000"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1101"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "1110"),
                        BitVector(4, "1111"),
                        BitVector(4, "0000"),
                        BitVector(4, "0110"));

  // DEATH tests -------------------------------------
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "1101"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
}

void
TestBvNode::test_normalize_bounds_no_s()
{
  // no bounds exclusive -----------------------------
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0000"),
                        BitVector(4, "0111"));
  test_normalize_bounds(BitVector(4, "1000"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1111"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1111"),
                        BitVector(4, "0000"),
                        BitVector(4, "0111"));
  test_normalize_bounds(BitVector(4, "0011"),
                        false,
                        BitVector(4, "1101"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1101"),
                        BitVector(4, "0011"),
                        BitVector(4, "0111"));
  // some bounds exclusive ---------------------------
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0111"));
  test_normalize_bounds(BitVector(4, "1000"),
                        false,
                        BitVector(4, "1111"),
                        true,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1110"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1110"),
                        BitVector(4, "0001"),
                        BitVector(4, "0111"));
  test_normalize_bounds(BitVector(4, "0011"),
                        false,
                        BitVector(4, "1101"),
                        true,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1000"),
                        BitVector(4, "1100"),
                        BitVector(4, "0011"),
                        BitVector(4, "0111"));
  // all bounds exclusive ----------------------------
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        true,
                        d_nullbv,
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0110"));
  test_normalize_bounds(BitVector(4, "1000"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        d_nullbv,
                        true,
                        d_nullbv,
                        true,
                        BitVector(4, "1001"),
                        BitVector(4, "1110"),
                        d_nullbv,
                        d_nullbv);
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        d_nullbv,
                        true,
                        d_nullbv,
                        true,
                        BitVector(4, "1000"),
                        BitVector(4, "1110"),
                        BitVector(4, "0001"),
                        BitVector(4, "0111"));
  test_normalize_bounds(BitVector(4, "0011"),
                        true,
                        BitVector(4, "1101"),
                        true,
                        d_nullbv,
                        true,
                        d_nullbv,
                        true,
                        BitVector(4, "1000"),
                        BitVector(4, "1100"),
                        BitVector(4, "0100"),
                        BitVector(4, "0111"));
}

void
TestBvNode::test_normalize_bounds_only_hi()
{
  // no bounds exclusive -----------------------------

  // unsigned: [0000, 0111]
  // signed:   [0000, 0111]
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0000"),
                        BitVector(4, "0111"));
  // unsigned: [0000, 0111]
  // signed:   [0011, 0110]
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "0110"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0110"));
  // unsigned: [0011, 0100]
  // signed:   [0001, 0110]
  test_normalize_bounds(BitVector(4, "0011"),
                        false,
                        BitVector(4, "0100"),
                        false,
                        BitVector(4, "0001"),
                        false,
                        BitVector(4, "0110"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0100"));
  // unsigned: [0010, 0100]
  // signed:   [0011, 0101]
  test_normalize_bounds(BitVector(4, "0010"),
                        false,
                        BitVector(4, "0100"),
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "0101"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0100"));
  // unsigned: [0010, 0110]
  // signed:   [0001, 0101]
  test_normalize_bounds(BitVector(4, "0010"),
                        false,
                        BitVector(4, "0110"),
                        false,
                        BitVector(4, "0001"),
                        false,
                        BitVector(4, "0101"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0010"),
                        BitVector(4, "0101"));

  // unsigned: [0001, 0010]
  // signed:   [0011, 0111]
  test_normalize_bounds(BitVector(4, "0001"),
                        false,
                        BitVector(4, "0010"),
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "0111"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);

  // some bounds exclusive ---------------------------

  // unsigned: ]0000, 0111]
  // signed:   [0000, 0111[
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0110"));
  // unsigned: [0000, 0111[
  // signed:   ]0011, 0110]
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "0110"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0100"),
                        BitVector(4, "0110"));
  // unsigned: ]0011, 0100]
  // signed:   ]0001, 0110]
  test_normalize_bounds(BitVector(4, "0011"),
                        true,
                        BitVector(4, "0100"),
                        false,
                        BitVector(4, "0001"),
                        true,
                        BitVector(4, "0110"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0100"),
                        BitVector(4, "0100"));
  // unsigned: ]0010, 0100[
  // signed:   [0011, 0101]
  test_normalize_bounds(BitVector(4, "0010"),
                        true,
                        BitVector(4, "0100"),
                        true,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "0101"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0011"));
  // unsigned: ]0010, 0110]
  // signed:   ]0001, 0101[
  test_normalize_bounds(BitVector(4, "0010"),
                        true,
                        BitVector(4, "0110"),
                        false,
                        BitVector(4, "0001"),
                        true,
                        BitVector(4, "0101"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0100"));
  // unsigned: [0001, 0010]
  // signed:   ]0011, 0111[
  test_normalize_bounds(BitVector(4, "0001"),
                        false,
                        BitVector(4, "0010"),
                        false,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);

  // all bounds exclusive ----------------------------
  // unsigned: ]0000, 0111[
  // signed:   ]0000, 0111[
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        BitVector(4, "0000"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0001"),
                        BitVector(4, "0110"));
  // unsigned: ]0000, 0111[
  // signed:   ]0011, 0110[
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0111"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "0110"),
                        false,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0100"),
                        BitVector(4, "0011"));
  // unsigned: ]0011, 0100[
  // signed:   ]0001, 0110[
  test_normalize_bounds(BitVector(4, "0011"),
                        true,
                        BitVector(4, "0100"),
                        true,
                        BitVector(4, "0001"),
                        true,
                        BitVector(4, "0110"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
  // unsigned: ]0010, 0100[
  // signed:   ]0011, 0101[
  test_normalize_bounds(BitVector(4, "0010"),
                        true,
                        BitVector(4, "0100"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "0101"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
  // unsigned: ]0010, 0110[
  // signed:   ]0001, 0101[
  test_normalize_bounds(BitVector(4, "0010"),
                        true,
                        BitVector(4, "0110"),
                        false,
                        BitVector(4, "0001"),
                        true,
                        BitVector(4, "0101"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        BitVector(4, "0011"),
                        BitVector(4, "0100"));
  // unsigned: ]0001, 0010[
  // signed:   ]0011, 0111[
  test_normalize_bounds(BitVector(4, "0001"),
                        true,
                        BitVector(4, "0010"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        BitVector(4, "0111"),
                        true,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv,
                        d_nullbv);
}

TEST_F(TestBvNode, normalize_bounds)
{
  // no signed bounds ------------------------------------------------------
  test_normalize_bounds_no_s();

  // no unsigned bounds ----------------------------------------------------
  test_normalize_bounds_no_u();

  // overlap in [0 ... smax] -----------------------------------------------
  test_normalize_bounds_only_hi();

  // overlap in [smin ... ones] --------------------------------------------

  // overlap in [0 ... ones] and [smin ... smax]
  // no overlap
}

}  // namespace bzla::ls::test
