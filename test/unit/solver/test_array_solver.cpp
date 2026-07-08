/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <map>
#include <set>
#include <vector>

#include "node/node_manager.h"
#include "solver/array/array_solver.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using bzla::array::ArraySolver;

/*
 * Unit tests for ArraySolver::canonicalize_array_value: two (default,
 * store-map) inputs that describe the same extensional array function must
 * produce identical nodes (value() decides array equality by node identity),
 * across all enumerable index sorts.
 */
class TestArrayCanonicalize : public TestCommon
{
 protected:
  Node canon(const Type& array_type,
             const Node& def,
             const std::map<Node, Node>& stores)
  {
    return ArraySolver::canonicalize_array_value(d_nm, array_type, def, stores);
  }

  Node bv(uint64_t size, uint64_t value)
  {
    return d_nm.mk_value(BitVector::from_ui(size, value));
  }

  Node store(const Node& base, const Node& index, const Node& value)
  {
    return d_nm.mk_node(Kind::STORE, {base, index, value});
  }

  NodeManager d_nm;
};

/* --- basic shape ---------------------------------------------------------- */

// No stores: the result is just the constant array with the given default.
TEST_F(TestArrayCanonicalize, empty_stores)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bv_type(1));
  std::map<Node, Node> stores;
  ASSERT_EQ(canon(at, bv(1, 0), stores), d_nm.mk_const_array(at, bv(1, 0)));
}

// All explicit cells equal the default: they are dropped, leaving a constant
// array.
TEST_F(TestArrayCanonicalize, all_stores_equal_default)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bv_type(1));
  std::map<Node, Node> stores{{bv(1, 0), bv(1, 0)}, {bv(1, 1), bv(1, 0)}};
  ASSERT_EQ(canon(at, bv(1, 0), stores), d_nm.mk_const_array(at, bv(1, 0)));
}

/* --- large / dominating-default domain ------------------------------------ */

// Large domain (card 256 >> 2*|stores|): the given default is already the
// most frequent value and is kept; a redundant store (== default) is dropped,
// a real store is preserved.
TEST_F(TestArrayCanonicalize, large_domain_keeps_default_drops_redundant)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(8), d_nm.mk_bv_type(1));
  std::map<Node, Node> stores{{bv(8, 1), bv(1, 1)},   // real store
                              {bv(8, 2), bv(1, 0)}};  // redundant (== default)
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), bv(8, 1), bv(1, 1));
  ASSERT_EQ(canon(at, bv(1, 0), stores), expected);
}

/* --- the core bug: extensionally-equal reps must collapse ----------------- */

// BV1 domain fully covered as {0->1, 1->0}, built two ways with different base
// defaults. Both must canonicalize to the identical node.
TEST_F(TestArrayCanonicalize, bv1_full_cover_collapses)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bv_type(1));

  // rep A: default #b0, store #b0 -> #b1
  std::map<Node, Node> a{{bv(1, 0), bv(1, 1)}};
  Node ra = canon(at, bv(1, 0), a);

  // rep B: default #b1, store #b1 -> #b0
  std::map<Node, Node> b{{bv(1, 1), bv(1, 0)}};
  Node rb = canon(at, bv(1, 1), b);

  ASSERT_EQ(ra, rb);

  // Tie in frequency (1 each) -> default is the value with the smaller node
  // id (#b0, created first), leaving the single store #b0 -> #b1.
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), bv(1, 0), bv(1, 1));
  ASSERT_EQ(ra, expected);
}

// Same collapse across the small/large branch boundary: a BV2 function built
// once with 3 explicit cells (enumerated) and once with 1 explicit cell
// (default dominates).
TEST_F(TestArrayCanonicalize, bv2_most_frequent_and_cross_branch)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(2), d_nm.mk_bv_type(2));

  // ext function: {00->01, 01->01, 10->01, 11->00}
  // rep A: default 00, pin 00,01,10 -> 01  (|stores|=3 => small branch)
  std::map<Node, Node> a{
      {bv(2, 0), bv(2, 1)}, {bv(2, 1), bv(2, 1)}, {bv(2, 2), bv(2, 1)}};
  Node ra = canon(at, bv(2, 0), a);

  // rep B: default 01, pin 11 -> 00  (|stores|=1 => large branch)
  std::map<Node, Node> b{{bv(2, 3), bv(2, 0)}};
  Node rb = canon(at, bv(2, 1), b);

  ASSERT_EQ(ra, rb);

  // Most frequent value is 01 (3 of 4 cells); the lone deviating cell is
  // 11 -> 00.
  Node expected = store(d_nm.mk_const_array(at, bv(2, 1)), bv(2, 3), bv(2, 0));
  ASSERT_EQ(ra, expected);
}

/* --- Boolean index -------------------------------------------------------- */

// (Array Bool BV1) fully covered as {false->0, true->1}, two ways.
TEST_F(TestArrayCanonicalize, bool_index_collapses)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bool_type(), d_nm.mk_bv_type(1));
  Node f  = d_nm.mk_value(false);
  Node t  = d_nm.mk_value(true);

  // rep A: default #b1, store false -> #b0
  std::map<Node, Node> a{{f, bv(1, 0)}};
  Node ra = canon(at, bv(1, 1), a);

  // rep B: default #b0, store true -> #b1
  std::map<Node, Node> b{{t, bv(1, 1)}};
  Node rb = canon(at, bv(1, 0), b);

  ASSERT_EQ(ra, rb);

  // Element-value tie broken toward #b0 -> default #b0, store true -> #b1.
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), t, bv(1, 1));
  ASSERT_EQ(ra, expected);
}

/* --- RoundingMode index --------------------------------------------------- */

// (Array RoundingMode BV1) with ext {RNA->1, others->0}, built with the default
// on either side of the majority (also crosses the small/large boundary).
TEST_F(TestArrayCanonicalize, rm_index_collapses)
{
  Type at  = d_nm.mk_array_type(d_nm.mk_rm_type(), d_nm.mk_bv_type(1));
  Node rna = d_nm.mk_value(RoundingMode::RNA);
  Node rne = d_nm.mk_value(RoundingMode::RNE);
  Node rtn = d_nm.mk_value(RoundingMode::RTN);
  Node rtp = d_nm.mk_value(RoundingMode::RTP);
  Node rtz = d_nm.mk_value(RoundingMode::RTZ);

  // rep A: default #b0, store RNA -> #b1  (|stores|=1, card 5 => large branch)
  std::map<Node, Node> a{{rna, bv(1, 1)}};
  Node ra = canon(at, bv(1, 0), a);

  // rep B: default #b1, stores RNE,RTN,RTP,RTZ -> #b0  (|stores|=4 => small)
  std::map<Node, Node> b{
      {rne, bv(1, 0)}, {rtn, bv(1, 0)}, {rtp, bv(1, 0)}, {rtz, bv(1, 0)}};
  Node rb = canon(at, bv(1, 1), b);

  ASSERT_EQ(ra, rb);

  // Most frequent value is #b0 (4 of 5); the single deviating cell is
  // RNA -> #b1.
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), rna, bv(1, 1));
  ASSERT_EQ(ra, expected);
}

/* --- deterministic tie-break --------------------------------------------- */

// The frequency tie-break is deterministic and independent of whether a cell
// equal to the default is supplied explicitly or left implicit.
TEST_F(TestArrayCanonicalize, tie_break_is_deterministic)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bv_type(1));

  // {0->1, 1->0}: frequencies tie; default is the value with the smaller node
  // id (#b0, created first).
  std::map<Node, Node> s1{{bv(1, 0), bv(1, 1)}, {bv(1, 1), bv(1, 0)}};
  // Same function with the redundant assignment 1->0 supplied as the default.
  std::map<Node, Node> s2{{bv(1, 0), bv(1, 1)}};

  Node r1 = canon(at, bv(1, 0), s1);
  Node r2 = canon(at, bv(1, 0), s2);

  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), bv(1, 0), bv(1, 1));
  ASSERT_EQ(r1, expected);
  ASSERT_EQ(r2, expected);
}

/* --- floating-point index sort -------------------------------------------- */

// Large FP domain (card 227 >> 2*|stores|): default dominates and is kept; a
// redundant store is dropped.
TEST_F(TestArrayCanonicalize, fp_large_domain_keeps_default_drops_redundant)
{
  Type fp_type = d_nm.mk_fp_type(3, 5);
  Type at      = d_nm.mk_array_type(fp_type, d_nm.mk_bv_type(1));
  uint64_t w   = fp_type.fp_ieee_bv_size();
  Node fp1     = d_nm.mk_value(FloatingPoint(3, 5, BitVector::from_ui(w, 1)));
  Node fp2     = d_nm.mk_value(FloatingPoint(3, 5, BitVector::from_ui(w, 2)));

  std::map<Node, Node> stores{{fp1, bv(1, 1)},   // real store
                              {fp2, bv(1, 0)}};  // redundant (== default)
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), fp1, bv(1, 1));
  ASSERT_EQ(canon(at, bv(1, 0), stores), expected);
}

// Small FP domain (card 15: +0/-0 are distinct, all NaN bit patterns collapse
// to one value): drives the domain materialization path and checks that two
// extensionally-equal representations still collapse.
TEST_F(TestArrayCanonicalize, fp_small_domain_materializes_and_collapses)
{
  Type fp_type = d_nm.mk_fp_type(2, 2);  // value cardinality 15
  Type at      = d_nm.mk_array_type(fp_type, d_nm.mk_bv_type(1));
  uint64_t w   = fp_type.fp_ieee_bv_size();

  // The 15 distinct values (two NaN bit patterns collapse to one node).
  std::vector<Node> fv;
  std::set<Node> seen;
  for (uint64_t k = 0; k < (uint64_t{1} << w); ++k)
  {
    Node v = d_nm.mk_value(FloatingPoint(2, 2, BitVector::from_ui(w, k)));
    if (seen.insert(v).second)
    {
      fv.push_back(v);
    }
  }
  ASSERT_EQ(fv.size(), 15u);

  // ext function: fv[0..7] -> #b1, fv[8..14] -> #b0.
  // rep A: default #b0, pin the 8 #b1 cells. The most frequent value #b1
  // displaces the default, so the 7 unpinned #b0 cells are materialized (FP
  // enumeration).
  std::map<Node, Node> a;
  for (int i = 0; i < 8; ++i)
  {
    a[fv[i]] = bv(1, 1);
  }
  Node ra = canon(at, bv(1, 0), a);

  // rep B: default #b1, pin the 7 #b0 cells directly (|stores|=7 => large
  // branch, default kept).
  std::map<Node, Node> b;
  for (int i = 8; i < 15; ++i)
  {
    b[fv[i]] = bv(1, 0);
  }
  Node rb = canon(at, bv(1, 1), b);

  ASSERT_EQ(ra, rb);

  // Canonical form: const #b1 with the 7 deviating cells fv[8..14] -> #b0.
  // Build via a node-id-ordered map to match the store-chain order.
  std::map<Node, Node> deviating;
  for (int i = 8; i < 15; ++i)
  {
    deviating.emplace(fv[i], bv(1, 0));
  }
  Node expected = d_nm.mk_const_array(at, bv(1, 1));
  for (const auto& [index, value] : deviating)
  {
    expected = store(expected, index, value);
  }
  ASSERT_EQ(ra, expected);
}

/* --- most-frequent default selection --------------------------------------- */

// The default's frequency combines the default region with explicit cells
// storing the default: #b0 occurs 2 (region) + 1 (RNE) = 3 times vs 2 for
// #b1, so it stays canonical.
TEST_F(TestArrayCanonicalize, default_seed_combines_with_explicit_cells)
{
  Type at  = d_nm.mk_array_type(d_nm.mk_rm_type(), d_nm.mk_bv_type(1));
  Node rne = d_nm.mk_value(RoundingMode::RNE);
  Node rtn = d_nm.mk_value(RoundingMode::RTN);
  Node rtp = d_nm.mk_value(RoundingMode::RTP);

  std::map<Node, Node> a{{rne, bv(1, 0)}, {rtn, bv(1, 1)}, {rtp, bv(1, 1)}};
  Node ra = canon(at, bv(1, 0), a);

  // Same function without the redundant RNE cell (default dominates).
  std::map<Node, Node> b{{rtn, bv(1, 1)}, {rtp, bv(1, 1)}};
  Node rb = canon(at, bv(1, 0), b);

  ASSERT_EQ(ra, rb);
  Node expected = store(
      store(d_nm.mk_const_array(at, bv(1, 0)), rtn, bv(1, 1)), rtp, bv(1, 1));
  ASSERT_EQ(ra, expected);
}

// Explicit cells storing the given default survive its displacement: the
// canonical form mixes them (RTZ) with materialized cells (RNA).
TEST_F(TestArrayCanonicalize, displaced_default_keeps_explicit_default_cells)
{
  Type at  = d_nm.mk_array_type(d_nm.mk_rm_type(), d_nm.mk_bv_type(1));
  Node rne = d_nm.mk_value(RoundingMode::RNE);
  Node rtn = d_nm.mk_value(RoundingMode::RTN);
  Node rtp = d_nm.mk_value(RoundingMode::RTP);
  Node rtz = d_nm.mk_value(RoundingMode::RTZ);
  Node rna = d_nm.mk_value(RoundingMode::RNA);

  // ext function: {RNE, RTN, RTP} -> #b1, {RTZ, RNA} -> #b0.
  // rep A: default #b0, RNA left to the default region; #b1 wins 3 to 2.
  std::map<Node, Node> a{
      {rne, bv(1, 1)}, {rtn, bv(1, 1)}, {rtp, bv(1, 1)}, {rtz, bv(1, 0)}};
  Node ra = canon(at, bv(1, 0), a);

  // rep B: default #b1, both #b0 cells explicit (default dominates).
  std::map<Node, Node> b{{rtz, bv(1, 0)}, {rna, bv(1, 0)}};
  Node rb = canon(at, bv(1, 1), b);

  ASSERT_EQ(ra, rb);
  Node expected = store(
      store(d_nm.mk_const_array(at, bv(1, 1)), rtz, bv(1, 0)), rna, bv(1, 0));
  ASSERT_EQ(ra, expected);
}

/* --- fully covered domain ------------------------------------------------- */

// A default value that occurs nowhere in a fully covered domain is irrelevant:
// the result must not depend on it.
TEST_F(TestArrayCanonicalize, full_cover_ignores_unused_default)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bv_type(2));

  // ext function {0 -> #b00, 1 -> #b01}; defaults #b10 / #b11 occur nowhere.
  std::map<Node, Node> s{{bv(1, 0), bv(2, 0)}, {bv(1, 1), bv(2, 1)}};
  Node ra = canon(at, bv(2, 2), s);
  Node rb = canon(at, bv(2, 3), s);

  // Same function with the in-map default #b00.
  std::map<Node, Node> c{{bv(1, 1), bv(2, 1)}};
  Node rc = canon(at, bv(2, 0), c);

  ASSERT_EQ(ra, rb);
  ASSERT_EQ(ra, rc);
}

// Frequency tie between two explicit values (the default occurs nowhere).
TEST_F(TestArrayCanonicalize, tie_between_two_explicit_values)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(2), d_nm.mk_bv_type(2));
  Node va = bv(2, 2);
  Node vb = bv(2, 3);

  // ext function {#b00, #b01 -> va; #b10, #b11 -> vb}: va and vb tie 2 to 2.
  std::map<Node, Node> s{
      {bv(2, 0), va}, {bv(2, 1), va}, {bv(2, 2), vb}, {bv(2, 3), vb}};
  Node ra = canon(at, va, s);
  Node rb = canon(at, vb, s);

  ASSERT_EQ(ra, rb);
  // Tie resolved to the value with the smaller node id (va, created first).
  Node expected =
      store(store(d_nm.mk_const_array(at, va), bv(2, 2), vb), bv(2, 3), vb);
  ASSERT_EQ(ra, expected);
}

/* --- non-bit-vector element sorts ----------------------------------------- */

// Boolean element values collapse like bit-vector ones.
TEST_F(TestArrayCanonicalize, bool_element_collapses)
{
  Type at = d_nm.mk_array_type(d_nm.mk_bv_type(1), d_nm.mk_bool_type());
  Node f  = d_nm.mk_value(false);
  Node t  = d_nm.mk_value(true);

  // ext function {0 -> false, 1 -> true}, built two ways.
  std::map<Node, Node> a{{bv(1, 0), f}};
  std::map<Node, Node> b{{bv(1, 1), t}};
  ASSERT_EQ(canon(at, t, a), canon(at, f, b));
}

// Array-typed element values are not value nodes; the node-id ordering still
// collapses extensionally-equal representations (nested constant arrays).
TEST_F(TestArrayCanonicalize, nested_array_elements_collapse)
{
  Type it  = d_nm.mk_bv_type(1);
  Type iat = d_nm.mk_array_type(it, it);
  Type at  = d_nm.mk_array_type(it, iat);
  Node ia0 = d_nm.mk_const_array(iat, bv(1, 0));
  Node ia1 = d_nm.mk_const_array(iat, bv(1, 1));

  // ext function {0 -> ia1, 1 -> ia0}, built two ways.
  std::map<Node, Node> a{{bv(1, 0), ia1}};
  std::map<Node, Node> b{{bv(1, 1), ia0}};
  ASSERT_EQ(canon(at, ia0, a), canon(at, ia1, b));
}

/* --- uninterpreted index sort --------------------------------------------- */

// Uninterpreted index sorts cannot be enumerated: the given default is kept
// and only redundant stores are dropped.
TEST_F(TestArrayCanonicalize, uninterpreted_index_keeps_default)
{
  Type ut = d_nm.mk_uninterpreted_type();
  Type at = d_nm.mk_array_type(ut, d_nm.mk_bv_type(1));
  Node u1 = d_nm.mk_const(ut);
  Node u2 = d_nm.mk_const(ut);

  std::map<Node, Node> stores{{u1, bv(1, 1)},   // real store
                              {u2, bv(1, 0)}};  // redundant (== default)
  Node expected = store(d_nm.mk_const_array(at, bv(1, 0)), u1, bv(1, 1));
  ASSERT_EQ(canon(at, bv(1, 0), stores), expected);
}

}  // namespace bzla::test
