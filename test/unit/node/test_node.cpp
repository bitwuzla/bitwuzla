/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include <utility>

#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::test {

using namespace bzla::node;

class TestNode : public ::testing::Test
{
};

TEST_F(TestNode, node_ctor_dtor)
{
  Node n;
  ASSERT_TRUE(n.is_null());
  ASSERT_EQ(n.kind(), Kind::NULL_NODE);
  ASSERT_EQ(n.id(), 0);
  ASSERT_EQ(n.num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
  // The kind predicates must be null-safe like the accessors above and report
  // false for a null node rather than dereferencing the null payload.
  ASSERT_FALSE(n.is_value());
  ASSERT_FALSE(n.is_const());
  ASSERT_FALSE(n.is_variable());
  ASSERT_FALSE(n.is_inverted());
}

TEST_F(TestNode, node_move)
{
  NodeManager nm;
  Node a      = nm.mk_const(nm.mk_bool_type(), "a");
  uint64_t id = a.id();

  // Move construction transfers ownership and nulls the source.
  Node b(std::move(a));
  ASSERT_TRUE(a.is_null());
  ASSERT_FALSE(b.is_null());
  ASSERT_EQ(b.id(), id);

  // Move assignment transfers ownership and nulls the source.
  Node c;
  c = std::move(b);
  ASSERT_TRUE(b.is_null());
  ASSERT_FALSE(c.is_null());
  ASSERT_EQ(c.id(), id);

  // Self-move assignment must leave the node intact (no use-after-free, not
  // nulled). The reference indirection avoids a -Wself-move warning.
  Node& ref = c;
  c         = std::move(ref);
  ASSERT_FALSE(c.is_null());
  ASSERT_EQ(c.id(), id);
}

TEST_F(TestNode, node_is_value)
{
  NodeManager nm;
  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  ASSERT_FALSE(nm.mk_const(bool_type).is_value());
  ASSERT_FALSE(nm.mk_const(bv_type).is_value());
  ASSERT_FALSE(nm.mk_const(fp_type).is_value());
  ASSERT_FALSE(nm.mk_const(rm_type).is_value());
  ASSERT_FALSE(nm.mk_const(array_type).is_value());
  ASSERT_FALSE(nm.mk_const(fun_type).is_value());

  ASSERT_TRUE(nm.mk_value(true).is_value());
  ASSERT_TRUE(nm.mk_value(false).is_value());

  ASSERT_TRUE(nm.mk_value(BitVector::from_ui(32, 1)).is_value());
  ASSERT_TRUE(
      nm.mk_value(FloatingPoint::fpzero(
                      fp_type.fp_exp_size(), fp_type.fp_sig_size(), true))
          .is_value());

  ASSERT_TRUE(nm.mk_value(RoundingMode::RNA).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RNE).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTN).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTP).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTZ).is_value());

  ASSERT_FALSE(
      nm.mk_node(Kind::AND, {nm.mk_const(bool_type), nm.mk_const(bool_type)})
          .is_value());
}

TEST_F(TestNode, rbegin_rend)
{
  NodeManager nm;
  Type bool_type  = nm.mk_bool_type();
  Node a          = nm.mk_const(bool_type, "a");
  Node b          = nm.mk_const(bool_type, "b");
  Node c          = nm.mk_const(bool_type, "c");
  Node d          = nm.mk_const(bool_type, "d");

  std::vector<Node> children = {a, b};
  Node a_and_b               = nm.mk_node(Kind::AND, children);
  auto itv                   = children.rbegin();
  auto itn                   = a_and_b.rbegin();
  for (; itv != children.rend(); ++itv, ++itn)
  {
    std::cout << *itv << " == " << *itn << std::endl;
    ASSERT_EQ(*itv, *itn);
  }

  Type fun_type =
      nm.mk_fun_type({bool_type, bool_type, bool_type, bool_type, bool_type});
  Node fun                   = nm.mk_const(fun_type);
  std::vector<Node> expected = {fun, a, b, c, d};
  Node app                   = nm.mk_node(Kind::APPLY, expected);
  itv                        = expected.rbegin();
  itn                        = app.rbegin();
  for (; itv != expected.rend(); ++itv, ++itn)
  {
    ASSERT_EQ(*itv, *itn);
  }
}

TEST_F(TestNode, operator_out)
{
  NodeManager nm;
  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  std::cout << nm.mk_const(bool_type) << std::endl;
  std::cout << nm.mk_const(bv_type) << std::endl;
  std::cout << nm.mk_const(fp_type) << std::endl;
  std::cout << nm.mk_const(rm_type) << std::endl;
  std::cout << nm.mk_const(array_type) << std::endl;
  std::cout << nm.mk_const(fun_type) << std::endl;

  std::cout << nm.mk_value(RoundingMode::RNA) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RNE) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTN) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTP) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTZ) << std::endl;

  std::cout << nm.mk_value(true) << std::endl;
  std::cout << nm.mk_value(false) << std::endl;

  std::cout << nm.mk_value(BitVector::from_ui(32, 1)) << std::endl;
  std::cout << nm.mk_value(
      FloatingPoint::fpzero(fp_type.fp_exp_size(), fp_type.fp_sig_size(), true))
            << std::endl;

  std::cout << nm.mk_node(Kind::AND,
                          {nm.mk_const(bool_type), nm.mk_const(bool_type)})
            << std::endl;
  std::cout << nm.mk_node(Kind::APPLY,
                          {nm.mk_const(fun_type, "fun"),
                           nm.mk_const(bool_type, "x"),
                           nm.mk_const(rm_type, "y")})
            << std::endl;
}

TEST_F(TestNode, payload_lifetime)
{
  // Regression test: NodeData::alloc() obtains raw, zero-initialized storage
  // from calloc() and must placement-new each payload member to start its
  // lifetime. Previously it assigned into the uninitialized storage, invoking
  // the copy assignment operator on objects whose lifetime never began (the
  // std::optional<std::string>, std::string, BitVector, FloatingPoint and Node
  // payload members) -- undefined behavior. This test exercises all three
  // alloc() overloads and checks that the payloads round-trip correctly.
  NodeManager nm;

  Type bool_type = nm.mk_bool_type();
  Type bv_type   = nm.mk_bv_type(32);
  Type un_type   = nm.mk_uninterpreted_type();

  // PayloadSymbol (std::optional<std::string>): constants and variables with
  // and without a symbol.
  Node c_sym = nm.mk_const(bv_type, "some_symbol");
  ASSERT_TRUE(c_sym.symbol().has_value());
  ASSERT_EQ(c_sym.symbol()->get(), "some_symbol");

  Node v_sym = nm.mk_var(bv_type, "var_symbol");
  ASSERT_TRUE(v_sym.symbol().has_value());
  ASSERT_EQ(v_sym.symbol()->get(), "var_symbol");

  Node c_nosym = nm.mk_const(bv_type);
  ASSERT_FALSE(c_nosym.symbol().has_value());

  // PayloadValue<std::string>: uninterpreted constant value. The empty-string
  // case is the one that writes through a null pointer on libstdc++ when
  // assigning into zeroed std::string storage.
  Node uval = nm.mk_value(un_type, "uval");
  ASSERT_EQ(uval.value<std::string>(), "uval");
  Node uval_empty = nm.mk_value(un_type, "");
  ASSERT_EQ(uval_empty.value<std::string>(), "");

  // PayloadValue<BitVector>.
  Node bvval = nm.mk_value(BitVector::from_ui(32, 42));
  ASSERT_EQ(bvval.value<BitVector>(), BitVector::from_ui(32, 42));

  // PayloadChildren (Node): assignment would dec_ref the uninitialized
  // previous value.
  Node a     = nm.mk_const(bool_type, "a");
  Node b     = nm.mk_const(bool_type, "b");
  Node a_and = nm.mk_node(Kind::AND, {a, b});
  ASSERT_EQ(a_and.num_children(), 2);
  ASSERT_EQ(a_and[0], a);
  ASSERT_EQ(a_and[1], b);
}

TEST_F(TestNode, indices)
{
  NodeManager nm;
  Type bv_type = nm.mk_bv_type(8);
  Node bv      = nm.mk_const(bv_type);

  // Indexed node: indices() returns a non-owning view of the stored indices.
  Node extract = nm.mk_node(Kind::BV_EXTRACT, {bv}, {5, 2});
  ASSERT_EQ(extract.num_indices(), 2);
  std::span<const uint64_t> indices = extract.indices();
  ASSERT_EQ(indices.size(), 2);
  ASSERT_EQ(indices[0], 5);
  ASSERT_EQ(indices[1], 2);

  // Non-indexed node: empty view.
  Node bvnot = nm.mk_node(Kind::BV_NOT, {bv});
  ASSERT_EQ(bvnot.num_indices(), 0);
  ASSERT_TRUE(bvnot.indices().empty());
}

}  // namespace bzla::test
