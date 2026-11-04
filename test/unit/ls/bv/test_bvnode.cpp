/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
                                  const BitVectorRange& lo_exp,
                                  const BitVectorRange& hi_exp)
{
  (void) lo_exp;
  (void) hi_exp;

  BitVectorNode node(d_rng.get(), 4);
  if (!min_u.is_null())
  {
    assert(!max_u.is_null());
    if (min_u.compare(max_u) > 0)
    {
      ASSERT_DEATH_DEBUG(
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
      ASSERT_DEATH_DEBUG(
          node.update_bounds(min_s, max_s, min_s_is_excl, max_s_is_excl, true),
          "signed_compare");
    }
    else
    {
      node.update_bounds(min_s, max_s, min_s_is_excl, max_s_is_excl, true);
    }
  }
  BitVectorBounds bounds =
      node.normalize_bounds(node.bounds_u(), node.bounds_s());
  assert(bounds.d_lo == lo_exp);
  assert(bounds.d_hi == hi_exp);
}

void
TestBvNode::test_normalize_bounds_no_u()
{
  // no bounds exclusive -----------------------------
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0111")),
      d_nullr);
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "0000"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0000")),
      BitVectorRange(BitVector(4, "1111"), BitVector(4, "1111")));
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1101"),
      false,
      BitVector(4, "0011"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0011")),
      BitVectorRange(BitVector(4, "1101"), BitVector(4, "1111")));
  // some bounds exclusive ---------------------------
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      false,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0111")),
      d_nullr);
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1110")));
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "0000"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1111"), BitVector(4, "1111")));
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1101"),
      false,
      BitVector(4, "0011"),
      true,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0010")),
      BitVectorRange(BitVector(4, "1101"), BitVector(4, "1111")));
  // all bounds exclusive ----------------------------
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0110")),
      d_nullr);
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "0000"),
                        true,
                        d_nullr,
                        d_nullr);
  test_normalize_bounds(
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVector(4, "1101"),
      true,
      BitVector(4, "0011"),
      true,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0010")),
      BitVectorRange(BitVector(4, "1110"), BitVector(4, "1111")));

  // DEATH tests -------------------------------------
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0000"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        d_nullr,
                        d_nullr);
  test_normalize_bounds(d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        BitVector(4, "0011"),
                        false,
                        BitVector(4, "1101"),
                        false,
                        d_nullr,
                        d_nullr);
}

void
TestBvNode::test_normalize_bounds_no_s()
{
  // no bounds exclusive -----------------------------
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      false,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0111")),
      d_nullr);
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      false,
      d_nullbv,
      false,
      d_nullbv,
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "1111"),
      false,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  test_normalize_bounds(
      BitVector(4, "0011"),
      false,
      BitVector(4, "1101"),
      false,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1101")));
  test_normalize_bounds(BitVector(4, "1101"),
                        false,
                        BitVector(4, "0011"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullr,
                        d_nullr);
  // some bounds exclusive ---------------------------
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      false,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0111")),
      d_nullr);
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      true,
      d_nullbv,
      false,
      d_nullbv,
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1110")));
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      true,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1110")));
  test_normalize_bounds(
      BitVector(4, "0011"),
      false,
      BitVector(4, "1101"),
      true,
      d_nullbv,
      false,
      d_nullbv,
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1100")));
  test_normalize_bounds(BitVector(4, "1101"),
                        true,
                        BitVector(4, "0011"),
                        false,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullr,
                        d_nullr);
  test_normalize_bounds(BitVector(4, "1101"),
                        false,
                        BitVector(4, "0011"),
                        true,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullr,
                        d_nullr);
  // all bounds exclusive ----------------------------
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      true,
      d_nullbv,
      true,
      d_nullbv,
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0110")),
      d_nullr);
  test_normalize_bounds(
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      true,
      d_nullbv,
      true,
      d_nullbv,
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      true,
      d_nullbv,
      true,
      d_nullbv,
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1110")));
  test_normalize_bounds(
      BitVector(4, "0011"),
      true,
      BitVector(4, "1101"),
      true,
      d_nullbv,
      true,
      d_nullbv,
      true,
      BitVectorRange(BitVector(4, "0100"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1100")));
  test_normalize_bounds(BitVector(4, "1101"),
                        true,
                        BitVector(4, "0011"),
                        true,
                        d_nullbv,
                        false,
                        d_nullbv,
                        false,
                        d_nullr,
                        d_nullr);
}

void
TestBvNode::test_normalize_bounds_only_hi()
{
  // no bounds exclusive -----------------------------

  // unsigned: [0000, 0111]
  // signed:   [0000, 0111]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      false,
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0111")),
      d_nullr);
  // unsigned: [0000, 0111]
  // signed:   [0011, 0110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      false,
      BitVector(4, "0011"),
      false,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0110")),
      d_nullr);
  // unsigned: [0011, 0100]
  // signed:   [0001, 0110]
  test_normalize_bounds(
      BitVector(4, "0011"),
      false,
      BitVector(4, "0100"),
      false,
      BitVector(4, "0001"),
      false,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0100")),
      d_nullr);
  // unsigned: [0010, 0100]
  // signed:   [0011, 0101]
  test_normalize_bounds(
      BitVector(4, "0010"),
      false,
      BitVector(4, "0100"),
      false,
      BitVector(4, "0011"),
      false,
      BitVector(4, "0101"),
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0100")),
      d_nullr);
  // unsigned: [0010, 0110]
  // signed:   [0001, 0101]
  test_normalize_bounds(
      BitVector(4, "0010"),
      false,
      BitVector(4, "0110"),
      false,
      BitVector(4, "0001"),
      false,
      BitVector(4, "0101"),
      false,
      BitVectorRange(BitVector(4, "0010"), BitVector(4, "0101")),
      d_nullr);

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
                        d_nullr,
                        d_nullr);

  // some bounds exclusive ---------------------------

  // unsigned: ]0000, 0111]
  // signed:   [0000, 0111[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      false,
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0110")),
      d_nullr);
  // unsigned: [0000, 0111[
  // signed:   ]0011, 0110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      true,
      BitVector(4, "0011"),
      true,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0100"), BitVector(4, "0110")),
      d_nullr);
  // unsigned: ]0011, 0100]
  // signed:   ]0001, 0110]
  test_normalize_bounds(
      BitVector(4, "0011"),
      true,
      BitVector(4, "0100"),
      false,
      BitVector(4, "0001"),
      true,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0100"), BitVector(4, "0100")),
      d_nullr);
  // unsigned: ]0010, 0100[
  // signed:   [0011, 0101]
  test_normalize_bounds(
      BitVector(4, "0010"),
      true,
      BitVector(4, "0100"),
      true,
      BitVector(4, "0011"),
      false,
      BitVector(4, "0101"),
      false,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0011")),
      d_nullr);
  // unsigned: ]0010, 0110]
  // signed:   ]0001, 0101[
  test_normalize_bounds(
      BitVector(4, "0010"),
      true,
      BitVector(4, "0110"),
      false,
      BitVector(4, "0001"),
      true,
      BitVector(4, "0101"),
      true,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0100")),
      d_nullr);
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
                        d_nullr,
                        d_nullr);

  // all bounds exclusive ----------------------------
  // unsigned: ]0000, 0111[
  // signed:   ]0000, 0111[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      true,
      BitVector(4, "0000"),
      true,
      BitVector(4, "0111"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0110")),
      d_nullr);
  // unsigned: ]0000, 0111[
  // signed:   ]0011, 0110[
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0111"),
      true,
      BitVector(4, "0011"),
      true,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0100"), BitVector(4, "0110")),
      d_nullr);
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
                        d_nullr,
                        d_nullr);
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
                        d_nullr,
                        d_nullr);
  // unsigned: ]0010, 0110[
  // signed:   ]0001, 0101[
  test_normalize_bounds(
      BitVector(4, "0010"),
      true,
      BitVector(4, "0110"),
      false,
      BitVector(4, "0001"),
      true,
      BitVector(4, "0101"),
      true,
      BitVectorRange(BitVector(4, "0011"), BitVector(4, "0100")),
      d_nullr);
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
                        d_nullr,
                        d_nullr);
}

void
TestBvNode::test_normalize_bounds_only_lo()
{
  // no bounds exclusive -----------------------------

  // unsigned: [1000, 1111]
  // signed:   [1000, 1111]
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  // unsigned: [1000, 1111]
  // signed:   [1011, 1110]
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1011"),
      false,
      BitVector(4, "1110"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1110")));
  // unsigned: [1011, 1100]
  // signed:   [1001, 1110]
  test_normalize_bounds(
      BitVector(4, "1011"),
      false,
      BitVector(4, "1100"),
      false,
      BitVector(4, "1001"),
      false,
      BitVector(4, "1110"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1100")));
  // unsigned: [1010, 1100]
  // signed:   [1011, 1101]
  test_normalize_bounds(
      BitVector(4, "1010"),
      false,
      BitVector(4, "1100"),
      false,
      BitVector(4, "1011"),
      false,
      BitVector(4, "1101"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1100")));
  // unsigned: [1010, 1110]
  // signed:   [1001, 1101]
  test_normalize_bounds(
      BitVector(4, "1010"),
      false,
      BitVector(4, "1110"),
      false,
      BitVector(4, "1001"),
      false,
      BitVector(4, "1101"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1010"), BitVector(4, "1101")));

  // unsigned: [1001, 1010]
  // signed:   [1011, 1111]
  test_normalize_bounds(BitVector(4, "1001"),
                        false,
                        BitVector(4, "1010"),
                        false,
                        BitVector(4, "1011"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        d_nullr,
                        d_nullr);

  // some bounds exclusive ---------------------------

  // unsigned: [1000, 1111[
  // signed:   ]1000, 1111]
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  // unsigned: [1000, 1111[
  // signed:   [1011, 1110[
  test_normalize_bounds(
      BitVector(4, "1000"),
      false,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1011"),
      false,
      BitVector(4, "1110"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1101")));
  // unsigned: ]1011, 1100]
  // signed:   ]1001, 1110]
  test_normalize_bounds(
      BitVector(4, "1011"),
      true,
      BitVector(4, "1100"),
      false,
      BitVector(4, "1001"),
      true,
      BitVector(4, "1110"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1100"), BitVector(4, "1100")));
  // unsigned: ]1010, 1100]
  // signed:   [1011, 1101[
  test_normalize_bounds(
      BitVector(4, "1010"),
      true,
      BitVector(4, "1100"),
      false,
      BitVector(4, "1011"),
      false,
      BitVector(4, "1101"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1100")));
  // unsigned: ]1010, 1110[
  // signed:   [1001, 1101]
  test_normalize_bounds(
      BitVector(4, "1010"),
      true,
      BitVector(4, "1110"),
      true,
      BitVector(4, "1001"),
      false,
      BitVector(4, "1101"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1101")));

  // unsigned: [1001, 1010]
  // signed:   ]1011, 1111[
  test_normalize_bounds(BitVector(4, "1001"),
                        false,
                        BitVector(4, "1010"),
                        false,
                        BitVector(4, "1011"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        d_nullr,
                        d_nullr);

  // all bounds exclusive ----------------------------

  // unsigned: ]1000, 1111[
  // signed:   ]1000, 1111[
  test_normalize_bounds(
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  // unsigned: ]1000, 1111[
  // signed:   ]1011, 1110[
  test_normalize_bounds(
      BitVector(4, "1000"),
      true,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1011"),
      true,
      BitVector(4, "1110"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1100"), BitVector(4, "1101")));
  // unsigned: ]1011, 1100[
  // signed:   ]1001, 1110[
  test_normalize_bounds(BitVector(4, "1011"),
                        true,
                        BitVector(4, "1100"),
                        true,
                        BitVector(4, "1001"),
                        true,
                        BitVector(4, "1110"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]1010, 1100[
  // signed:   ]1011, 1101[
  test_normalize_bounds(BitVector(4, "1010"),
                        true,
                        BitVector(4, "1100"),
                        true,
                        BitVector(4, "1011"),
                        true,
                        BitVector(4, "1101"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]1010, 1110[
  // signed:   ]1001, 1101[
  test_normalize_bounds(
      BitVector(4, "1010"),
      true,
      BitVector(4, "1110"),
      true,
      BitVector(4, "1001"),
      true,
      BitVector(4, "1101"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1011"), BitVector(4, "1100")));

  // unsigned: ]1001, 1010[
  // signed:   ]1011, 1111[
  test_normalize_bounds(BitVector(4, "1001"),
                        true,
                        BitVector(4, "1010"),
                        true,
                        BitVector(4, "1011"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        d_nullr,
                        d_nullr);
}

void
TestBvNode::test_normalize_bounds_both()
{
  // no bounds exclusive -----------------------------

  // unsigned: [0000, 1111]
  // signed:   [1000, 0111]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1000"),
      false,
      BitVector(4, "0111"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  // unsigned: [0000, 1111]
  // signed:   [1111, 0000]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "0000"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0000")),
      BitVectorRange(BitVector(4, "1111"), BitVector(4, "1111")));
  // unsigned: [0000, 1111]
  // signed:   [1000, 0000]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1000"),
      false,
      BitVector(4, "0000"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0000")),
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1111")));
  // unsigned: [0000, 0011]
  // signed:   [1011, 0110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0011"),
      false,
      BitVector(4, "1011"),
      false,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0011")),
      d_nullr);
  // unsigned: [0000, 1010]
  // signed:   [1001, 1110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "1010"),
      false,
      BitVector(4, "1001"),
      false,
      BitVector(4, "1110"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1010")));
  // unsigned: [0000, 0010]
  // signed:   [1001, 0110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0010"),
      false,
      BitVector(4, "1001"),
      false,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0010")),
      d_nullr);
  // unsigned: [1100, 1111]
  // signed:   [1001, 1011]
  test_normalize_bounds(BitVector(4, "1100"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "1001"),
                        false,
                        BitVector(4, "1011"),
                        false,
                        d_nullr,
                        d_nullr);
  // unsigned: [0000, 0101]
  // signed:   [1001, 1011]
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0101"),
                        false,
                        BitVector(4, "1001"),
                        false,
                        BitVector(4, "1011"),
                        false,
                        d_nullr,
                        d_nullr);

  // some bounds exclusive ---------------------------

  // unsigned: ]0000, 1111]
  // signed:   ]1000, 0111]
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      false,
      BitVector(4, "1000"),
      true,
      BitVector(4, "0111"),
      false,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0111")),
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1111")));
  // unsigned: [0000, 1111[
  // signed:   [1111, 0000[
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "0000"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]0000, 1111[
  // signed:   [1000, 0000]
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1000"),
      false,
      BitVector(4, "0000"),
      false,
      d_nullr,
      BitVectorRange(BitVector(4, "1000"), BitVector(4, "1110")));
  // unsigned: [0000, 0011]
  // signed:   ]1011, 0110[
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0011"),
      false,
      BitVector(4, "1011"),
      true,
      BitVector(4, "0110"),
      true,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0011")),
      d_nullr);
  // unsigned: ]0000, 1010[
  // signed:   [1001, 1110[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1010"),
      false,
      BitVector(4, "1001"),
      true,
      BitVector(4, "1110"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1010"), BitVector(4, "1010")));
  // unsigned: [0000, 0010[
  // signed:   [1001, 0110]
  test_normalize_bounds(
      BitVector(4, "0000"),
      false,
      BitVector(4, "0010"),
      true,
      BitVector(4, "1001"),
      false,
      BitVector(4, "0110"),
      false,
      BitVectorRange(BitVector(4, "0000"), BitVector(4, "0001")),
      d_nullr);
  // unsigned: [1100, 1111]
  // signed:   ]1001, 1011]
  test_normalize_bounds(BitVector(4, "1100"),
                        false,
                        BitVector(4, "1111"),
                        false,
                        BitVector(4, "1001"),
                        true,
                        BitVector(4, "1011"),
                        false,
                        d_nullr,
                        d_nullr);
  // unsigned: [0000, 0101[
  // signed:   [1001, 1011[
  test_normalize_bounds(BitVector(4, "0000"),
                        false,
                        BitVector(4, "0101"),
                        true,
                        BitVector(4, "1001"),
                        false,
                        BitVector(4, "1011"),
                        true,
                        d_nullr,
                        d_nullr);

  // all bounds exclusive ----------------------------

  // unsigned: ]0000, 1111[
  // signed:   ]1000, 0111[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1000"),
      true,
      BitVector(4, "0111"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0110")),
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  // unsigned: ]0000, 1111[
  // signed:   ]1111, 0000[
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "0000"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]0000, 1111[
  // signed:   ]1000, 0000[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "1111"),
      true,
      BitVector(4, "1000"),
      true,
      BitVector(4, "0000"),
      true,
      d_nullr,
      BitVectorRange(BitVector(4, "1001"), BitVector(4, "1110")));
  // unsigned: ]0000, 0011[
  // signed:   ]1011, 0110[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0011"),
      true,
      BitVector(4, "1011"),
      true,
      BitVector(4, "0110"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0010")),
      d_nullr);
  // unsigned: ]0000, 1010[
  // signed:   ]1001, 1110[
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "1010"),
                        true,
                        BitVector(4, "1001"),
                        true,
                        BitVector(4, "1110"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]0000, 0010[
  // signed:   ]1001, 0110[
  test_normalize_bounds(
      BitVector(4, "0000"),
      true,
      BitVector(4, "0010"),
      true,
      BitVector(4, "1001"),
      true,
      BitVector(4, "0110"),
      true,
      BitVectorRange(BitVector(4, "0001"), BitVector(4, "0001")),
      d_nullr);
  // unsigned: ]1100, 1111[
  // signed:   ]1001, 1011[
  test_normalize_bounds(BitVector(4, "1100"),
                        true,
                        BitVector(4, "1111"),
                        true,
                        BitVector(4, "1001"),
                        true,
                        BitVector(4, "1011"),
                        true,
                        d_nullr,
                        d_nullr);
  // unsigned: ]0000, 0101[
  // signed:   ]1001, 1011[
  test_normalize_bounds(BitVector(4, "0000"),
                        true,
                        BitVector(4, "0101"),
                        true,
                        BitVector(4, "1001"),
                        true,
                        BitVector(4, "1011"),
                        true,
                        d_nullr,
                        d_nullr);
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
  test_normalize_bounds_only_lo();

  // overlap in [0 ... ones] and [smin ... smax]
  test_normalize_bounds_both();
}

TEST_F(TestBvNode, update_bounds_exclusive_after_inclusive)
{
  // An exclusive bound with the same value as an inclusive bound is tighter
  // and must be applied, independently of the order of registration.
  BitVector zero(4, "0000"), ones(4, "1111");
  BitVector smin(4, "1000"), smax(4, "0111");
  BitVector five(4, "0101"), six(4, "0110"), four(4, "0100");
  BitVector mtwo(4, "1110"), mone(4, "1111"), mthree(4, "1101");

  for (bool reverse : {false, true})
  {
    // unsigned: x >= 5 and x > 5
    {
      BitVectorNode node(d_rng.get(), 4);
      node.update_bounds(five, ones, !reverse, false, false);
      node.update_bounds(five, ones, reverse, false, false);
      ASSERT_EQ(node.bounds_u().d_min.compare(six), 0);
      ASSERT_EQ(node.bounds_u().d_max.compare(ones), 0);
    }
    // unsigned: x <= 5 and x < 5
    {
      BitVectorNode node(d_rng.get(), 4);
      node.update_bounds(zero, five, false, !reverse, false);
      node.update_bounds(zero, five, false, reverse, false);
      ASSERT_EQ(node.bounds_u().d_min.compare(zero), 0);
      ASSERT_EQ(node.bounds_u().d_max.compare(four), 0);
    }
    // signed: x >= -2 and x > -2
    {
      BitVectorNode node(d_rng.get(), 4);
      node.update_bounds(mtwo, smax, !reverse, false, true);
      node.update_bounds(mtwo, smax, reverse, false, true);
      ASSERT_EQ(node.bounds_s().d_min.compare(mone), 0);
      ASSERT_EQ(node.bounds_s().d_max.compare(smax), 0);
    }
    // signed: x <= -2 and x < -2
    {
      BitVectorNode node(d_rng.get(), 4);
      node.update_bounds(smin, mtwo, false, !reverse, true);
      node.update_bounds(smin, mtwo, false, reverse, true);
      ASSERT_EQ(node.bounds_s().d_min.compare(smin), 0);
      ASSERT_EQ(node.bounds_s().d_max.compare(mthree), 0);
    }
  }
}

}  // namespace bzla::ls::test
