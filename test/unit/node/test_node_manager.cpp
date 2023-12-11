/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bv/bitvector.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace bzla::node;
using namespace bzla::type;

class TestNodeManager : public TestCommon
{
};

TEST_F(TestNodeManager, mk_const)
{
  NodeManager& nm = NodeManager::get();

  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  Node bool_const  = nm.mk_const(bool_type);
  Node bv_const    = nm.mk_const(bv_type);
  Node fp_const    = nm.mk_const(fp_type);
  Node rm_const    = nm.mk_const(rm_type);
  Node array_const = nm.mk_const(array_type);
  Node fun_const   = nm.mk_const(fun_type);

  ASSERT_NE(bool_const, nm.mk_const(bool_type));
  ASSERT_NE(bv_const, nm.mk_const(bv_type));
  ASSERT_NE(fp_const, nm.mk_const(fp_type));
  ASSERT_NE(rm_const, nm.mk_const(rm_type));
  ASSERT_NE(array_const, nm.mk_const(array_type));
  ASSERT_NE(fun_const, nm.mk_const(fun_type));

  ASSERT_EQ(bool_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(bool_const.num_children(), 0);
  ASSERT_TRUE(bool_const.type().is_bool());

  ASSERT_EQ(bv_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(bv_const.num_children(), 0);
  ASSERT_TRUE(bv_const.type().is_bv());

  ASSERT_EQ(fp_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(fp_const.num_children(), 0);
  ASSERT_TRUE(fp_const.type().is_fp());

  ASSERT_EQ(rm_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(rm_const.num_children(), 0);
  ASSERT_TRUE(rm_const.type().is_rm());

  ASSERT_EQ(array_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(array_const.num_children(), 0);
  ASSERT_TRUE(array_const.type().is_array());

  ASSERT_EQ(fun_const.kind(), Kind::CONSTANT);
  ASSERT_EQ(fun_const.num_children(), 0);
  ASSERT_TRUE(fun_const.type().is_fun());
}

TEST_F(TestNodeManager, mk_const_array)
{
  NodeManager& nm = NodeManager::get();

  Type bv32  = nm.mk_bv_type(32);
  Node value = nm.mk_const(bv32);
  Node const_array =
      nm.mk_const_array(nm.mk_array_type(nm.mk_bool_type(), bv32), value);
  ASSERT_EQ(const_array.kind(), Kind::CONST_ARRAY);
  ASSERT_TRUE(const_array.type().is_array());
  ASSERT_EQ(
      const_array,
      nm.mk_const_array(nm.mk_array_type(nm.mk_bool_type(), bv32), value));
  ASSERT_NE(const_array,
            nm.mk_const_array(nm.mk_array_type(bv32, bv32), value));
}

TEST_F(TestNodeManager, mk_value_bool)
{
  NodeManager& nm = NodeManager::get();

  Node val_true  = nm.mk_value(true);
  Node val_false = nm.mk_value(false);
  ASSERT_EQ(val_true.kind(), Kind::VALUE);
  ASSERT_EQ(val_false.kind(), Kind::VALUE);
  ASSERT_EQ(val_true.type(), nm.mk_bool_type());
  ASSERT_EQ(val_true.type(), val_false.type());
  ASSERT_EQ(val_true, nm.mk_value(true));
  ASSERT_EQ(val_false, nm.mk_value(false));
  ASSERT_EQ(val_true.value<bool>(), true);
  ASSERT_EQ(val_false.value<bool>(), false);
  ASSERT_NE(val_true, val_false);
}

TEST_F(TestNodeManager, mk_value_bv)
{
  NodeManager& nm = NodeManager::get();
  BitVector bv    = BitVector::from_ui(32, 1);

  Node val = nm.mk_value(bv);
  ASSERT_EQ(val.kind(), Kind::VALUE);
  ASSERT_EQ(val.type(), nm.mk_bv_type(32));
  ASSERT_EQ(val, nm.mk_value(BitVector::from_ui(32, 1)));
  ASSERT_EQ(val.value<BitVector>(), bv);
  ASSERT_EQ(val.value<BitVector>(), BitVector::from_ui(32, 1));
  ASSERT_NE(val, nm.mk_value(BitVector::from_ui(32, 2)));
}

TEST_F(TestNodeManager, mk_value_rm)
{
  NodeManager& nm = NodeManager::get();

  Node val_rna = nm.mk_value(RoundingMode::RNA);
  Node val_rne = nm.mk_value(RoundingMode::RNE);
  Node val_rtn = nm.mk_value(RoundingMode::RTN);
  Node val_rtp = nm.mk_value(RoundingMode::RTP);
  Node val_rtz = nm.mk_value(RoundingMode::RTZ);

  for (const auto& val : {val_rna, val_rne, val_rtn, val_rtp, val_rtz})
  {
    ASSERT_EQ(val.kind(), Kind::VALUE);
    ASSERT_EQ(val.type(), nm.mk_rm_type());
    ASSERT_EQ(val_rna.type(), val.type());
  }

  ASSERT_EQ(val_rna, nm.mk_value(RoundingMode::RNA));
  ASSERT_EQ(val_rne, nm.mk_value(RoundingMode::RNE));
  ASSERT_EQ(val_rtn, nm.mk_value(RoundingMode::RTN));
  ASSERT_EQ(val_rtp, nm.mk_value(RoundingMode::RTP));
  ASSERT_EQ(val_rtz, nm.mk_value(RoundingMode::RTZ));

  ASSERT_EQ(val_rna.value<RoundingMode>(), RoundingMode::RNA);
  ASSERT_EQ(val_rne.value<RoundingMode>(), RoundingMode::RNE);
  ASSERT_EQ(val_rtn.value<RoundingMode>(), RoundingMode::RTN);
  ASSERT_EQ(val_rtp.value<RoundingMode>(), RoundingMode::RTP);
  ASSERT_EQ(val_rtz.value<RoundingMode>(), RoundingMode::RTZ);

  for (const auto& val : {val_rne, val_rtn, val_rtp, val_rtz})
  {
    ASSERT_NE(val_rna, val);
  }
}

TEST_F(TestNodeManager, mk_value_fp)
{
  // TODO: after FloatingPoint refactor is done.
}

TEST_F(TestNodeManager, mk_node)
{
  NodeManager& nm = NodeManager::get();

  Type bool_type = nm.mk_bool_type();

  Node x = nm.mk_const(bool_type);
  Node y = nm.mk_const(bool_type);
  Node z = nm.mk_const(bool_type);

  Node x_and_y = nm.mk_node(Kind::AND, {x, y});

  ASSERT_EQ(x_and_y.num_children(), 2);
  ASSERT_NE(x_and_y.begin(), x_and_y.end());
  ASSERT_EQ(x_and_y[0], x);
  ASSERT_EQ(x_and_y[1], y);
  for (auto it = x_and_y.begin(); it != x_and_y.end(); ++it)
  {
    ASSERT_FALSE(it->is_null());
    ASSERT_TRUE(*it == x || *it == y);
  }
  for (const Node& c : x_and_y)
  {
    ASSERT_FALSE(c.is_null());
    ASSERT_TRUE(c == x || c == y);
  }

  Node or_z = nm.mk_node(Kind::OR, {x_and_y, z});

  ASSERT_EQ(x_and_y, nm.mk_node(Kind::AND, {x, y}));
  ASSERT_EQ(or_z, nm.mk_node(Kind::OR, {nm.mk_node(Kind::AND, {x, y}), z}));
}

TEST_F(TestNodeManager, mk_apply)
{
  NodeManager& nm = NodeManager::get();

  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fun_type   = nm.mk_fun_type({bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bool_type,
                                    bv_type});
  Node fun        = nm.mk_const(fun_type);
  Node bool_const = nm.mk_const(bool_type);
  Node apply      = nm.mk_node(Kind::APPLY,
                          {fun,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const,
                                bool_const});

  ASSERT_EQ(apply.num_children(), 7);
  ASSERT_EQ(apply[0], fun);
  for (size_t i = 1; i < apply.num_children(); ++i)
  {
    ASSERT_EQ(apply[i], bool_const);
  }
  ASSERT_EQ(apply.type(), bv_type);
  ASSERT_DEATH_DEBUG(nm.mk_node(Kind::APPLY, {fun}), "");
  ASSERT_DEATH_DEBUG(nm.mk_node(Kind::APPLY, {fun, bool_const}), "");
}

TEST_F(TestNodeManager, check_type)
{
  NodeManager& nm = NodeManager::get();

  // Test boolean operators
  Type bool_type   = nm.mk_bool_type();
  Node bool_const1 = nm.mk_const(bool_type);
  Node bool_const2 = nm.mk_const(bool_type);

  ASSERT_EQ(nm.mk_node(Kind::EQUAL, {bool_const1, bool_const2}).type(),
            bool_type);

  ASSERT_EQ(nm.mk_node(Kind::NOT, {bool_const1}).type(), bool_type);

  for (auto kind : {Kind::AND, Kind::OR})
  {
    ASSERT_EQ(nm.mk_node(kind, {bool_const1, bool_const2}).type(), bool_type);
  }

  // Test bit-vector operators
  Type bv_type   = nm.mk_bv_type(32);
  Node bv_const1 = nm.mk_const(bv_type);
  Node bv_const2 = nm.mk_const(bv_type);

  ASSERT_EQ(nm.mk_node(Kind::EQUAL, {bv_const1, bv_const2}).type(), bool_type);

  ASSERT_EQ(nm.mk_node(Kind::BV_NOT, {bv_const1}).type(), bv_type);

  for (auto kind : {Kind::BV_SLT, Kind::BV_ULT})
  {
    ASSERT_EQ(nm.mk_node(kind, {bv_const1, bv_const2}).type(), bool_type);
  }

  for (auto kind : {Kind::BV_AND,
                    Kind::BV_ADD,
                    Kind::BV_MUL,
                    Kind::BV_SHL,
                    Kind::BV_SHR,
                    Kind::BV_ASHR,
                    Kind::BV_UDIV,
                    Kind::BV_UREM})
  {
    ASSERT_EQ(nm.mk_node(kind, {bv_const1, bv_const2}).type(), bv_type);
  }

  ASSERT_EQ(nm.mk_node(Kind::BV_CONCAT, {bv_const1, bv_const2}).type(),
            nm.mk_bv_type(64));
  ASSERT_EQ(nm.mk_node(Kind::BV_EXTRACT, {bv_const1}, {5, 0}).type(),
            nm.mk_bv_type(6));

  // Test floating-point operators
  Type fp_type   = nm.mk_fp_type(5, 11);
  Type rm_type   = nm.mk_rm_type();
  Node fp_const1 = nm.mk_const(fp_type);
  Node fp_const2 = nm.mk_const(fp_type);
  Node fp_const3 = nm.mk_const(fp_type);
  Node rm_const  = nm.mk_const(rm_type);

  ASSERT_EQ(nm.mk_node(Kind::EQUAL, {fp_const1, fp_const2}).type(), bool_type);

  ASSERT_EQ(nm.mk_node(Kind::EQUAL, {rm_const, nm.mk_const(rm_type)}).type(),
            bool_type);

  for (auto kind : {Kind::FP_ABS, Kind::FP_NEG})
  {
    ASSERT_EQ(nm.mk_node(kind, {fp_const1}).type(), fp_type);
  }

  for (auto kind : {
           Kind::FP_IS_INF,
           Kind::FP_IS_NAN,
           Kind::FP_IS_NEG,
           Kind::FP_IS_NORMAL,
           Kind::FP_IS_POS,
           Kind::FP_IS_SUBNORMAL,
           Kind::FP_IS_ZERO,
       })
  {
    ASSERT_EQ(nm.mk_node(kind, {fp_const1}).type(), bool_type);
  }

  ASSERT_EQ(nm.mk_node(Kind::FP_TO_FP_FROM_BV, {bv_const1}, {8, 24}).type(),
            nm.mk_fp_type(8, 24));

  for (auto kind : {Kind::FP_EQUAL, Kind::FP_LEQ, Kind::FP_LT})
  {
    ASSERT_EQ(nm.mk_node(kind, {fp_const1, fp_const2}).type(), bool_type);
  }

  for (auto kind : {Kind::FP_MIN, Kind::FP_MAX, Kind::FP_REM})
  {
    ASSERT_EQ(nm.mk_node(kind, {fp_const1, fp_const2}).type(), fp_type);
  }

  for (auto kind : {Kind::FP_SQRT, Kind::FP_RTI})
  {
    ASSERT_EQ(nm.mk_node(kind, {rm_const, fp_const1}).type(), fp_type);
  }

  for (auto kind : {Kind::FP_TO_SBV, Kind::FP_TO_UBV})
  {
    ASSERT_EQ(nm.mk_node(kind, {rm_const, fp_const1}, {32}).type(),
              nm.mk_bv_type(32));
  }

  ASSERT_EQ(
      nm.mk_node(Kind::FP_TO_FP_FROM_FP, {rm_const, fp_const1}, {8, 24}).type(),
      nm.mk_fp_type(8, 24));

  for (auto kind : {Kind::FP_TO_FP_FROM_SBV, Kind::FP_TO_FP_FROM_UBV})
  {
    ASSERT_EQ(nm.mk_node(kind, {rm_const, bv_const1}, {5, 11}).type(),
              nm.mk_fp_type(5, 11));
  }

  for (auto kind : {Kind::FP_ADD, Kind::FP_MUL, Kind::FP_DIV})
  {
    ASSERT_EQ(nm.mk_node(kind, {rm_const, fp_const1, fp_const2}).type(),
              fp_type);
  }

  ASSERT_EQ(
      nm.mk_node(Kind::FP_FMA, {rm_const, fp_const1, fp_const2, fp_const3})
          .type(),
      fp_type);

  // Test array operators
  Type array_type  = nm.mk_array_type(bv_type, fp_type);
  Node array_const = nm.mk_const(array_type);

  ASSERT_EQ(
      nm.mk_node(Kind::EQUAL, {array_const, nm.mk_const(array_type)}).type(),
      bool_type);

  ASSERT_EQ(nm.mk_node(Kind::SELECT, {array_const, bv_const1}).type(), fp_type);
  ASSERT_EQ(nm.mk_node(Kind::STORE, {array_const, bv_const1, fp_const1}).type(),
            array_type);

  // Test functions
  Type fun_type  = nm.mk_fun_type({bool_type, rm_type, array_type});
  Node fun_const = nm.mk_const(fun_type);

  ASSERT_EQ(nm.mk_node(Kind::APPLY, {fun_const, bool_const1, rm_const}).type(),
            array_type);

  Node x  = nm.mk_var(bv_type);
  Node y  = nm.mk_var(fp_type);
  Node l1 = nm.mk_node(Kind::LAMBDA,
                       {y, nm.mk_node(Kind::STORE, {array_const, x, y})});
  Node l2 = nm.mk_node(Kind::LAMBDA, {x, l1});

  ASSERT_EQ(nm.mk_node(Kind::EQUAL, {l2, l2}).type(), bool_type);

  ASSERT_EQ(l2.type(), nm.mk_fun_type({bv_type, fp_type, array_type}));

  ASSERT_EQ(nm.mk_node(Kind::APPLY, {l2, bv_const1, fp_const1}).type(),
            array_type);

  // Test quantifiers
  Node var = nm.mk_var(bv_type);
  for (auto kind : {Kind::FORALL, Kind::EXISTS})
  {
    ASSERT_EQ(nm.mk_node(kind, {var, nm.mk_node(Kind::EQUAL, {var, bv_const1})})
                  .type(),
              bool_type);
  }

  // Test ITE
  ASSERT_EQ(
      nm.mk_node(Kind::ITE, {bool_const1, bool_const1, bool_const2}).type(),
      bool_type);
  ASSERT_EQ(nm.mk_node(Kind::ITE, {bool_const1, bv_const1, bv_const2}).type(),
            bv_type);
  ASSERT_EQ(nm.mk_node(Kind::ITE, {bool_const1, fp_const1, fp_const2}).type(),
            fp_type);
  ASSERT_EQ(nm.mk_node(Kind::ITE, {bool_const1, rm_const, rm_const}).type(),
            rm_type);
  ASSERT_EQ(
      nm.mk_node(Kind::ITE, {bool_const1, array_const, array_const}).type(),
      array_type);
  ASSERT_EQ(nm.mk_node(Kind::ITE, {bool_const1, l2, l2}).type(),
            nm.mk_fun_type({bv_type, fp_type, array_type}));
}

}  // namespace bzla::test
