#include "bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "rewrite/rewriter.h"
#include "rewrite/test_rewriter.h"
#include "solver/fp/floating_point.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBv : public TestRewriter
{
  void SetUp() override
  {
    d_bv4_type = d_nm.mk_bv_type(4);
    d_bv1_type = d_nm.mk_bv_type(1);
    d_bv4_zero = d_nm.mk_value(BitVector::mk_zero(4));
    d_bv1_zero = d_nm.mk_value(BitVector::mk_zero(1));
    d_bv4_one  = d_nm.mk_value(BitVector::mk_one(4));
    d_bv1_one  = d_nm.mk_value(BitVector::mk_one(1));
    d_bv4_ones = d_nm.mk_value(BitVector::mk_ones(4));
    d_bv1_ones = d_nm.mk_value(BitVector::mk_ones(1));
    d_false   = d_nm.mk_value(false);
    d_true     = d_nm.mk_value(true);
    d_a4       = d_nm.mk_const(d_bv4_type);
    d_a1       = d_nm.mk_const(d_bv1_type);
  }

 protected:
  void test_elim_rule_bv(Kind kind)
  {
    test_elim_rule(kind, d_nm.mk_bv_type(8));
  }

  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Type d_bv4_type;
  Type d_bv1_type;
  Node d_bv4_zero;
  Node d_bv1_zero;
  Node d_bv1_one;
  Node d_bv4_one;
  Node d_bv1_ones;
  Node d_bv4_ones;
  Node d_false;
  Node d_true;
  Node d_a1;
  Node d_a4;
};

/* bvadd -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_add_eval)
{
  //// applies
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0111")), d_rewriter.rewrite(bvadd0));
  Node bvadd1 =
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_value(BitVector(4, "1001")), bvadd0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvadd1));
  Node bvadd1_1 =
      d_nm.mk_node(Kind::BV_ADD, {bvadd1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvadd1_1));
  Node bvadd1_2 = d_nm.mk_node(Kind::BV_ADD, {bvadd1, bvadd1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvadd1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvadd1_2));
  //// does not apply
  Node bvadd2 = d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd2, d_rewriter.rewrite(bvadd2));
  Node bvadd3 =
      d_nm.mk_node(Kind::BV_ADD, {bvadd2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd3, d_rewriter.rewrite(bvadd3));
}

TEST_F(TestRewriterBv, bv_add_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvadd0 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd0));
    Node bvadd1 = d_nm.mk_node(Kind::BV_ADD, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd1));
    Node bvadd0_1 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, bvadd0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd0_1));
    Node bvadd0_2 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, bvadd1});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd0_2));
    Node bvadd1_1 = d_nm.mk_node(Kind::BV_ADD, {bvadd0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd1_1));
    Node bvadd1_2 = d_nm.mk_node(Kind::BV_ADD, {bvadd1, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd1_2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvadd1_2));
    //// does not apply
    Node bvadd2 = d_nm.mk_node(
        Kind::BV_ADD, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvadd2, d_rewriter.rewrite(bvadd2));
    Node bvadd3 = d_nm.mk_node(
        Kind::BV_ADD,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvadd3, d_rewriter.rewrite(bvadd3));
    Node bvadd4 = d_nm.mk_node(
        Kind::BV_ADD,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvadd4, d_rewriter.rewrite(bvadd4));
  }
}

/* bvand -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_and_eval)
{
  //// applies
  Node bvand0 = d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand0));
  Node bvand1 =
      d_nm.mk_node(Kind::BV_AND, {d_nm.mk_value(BitVector(4, "1001")), bvand0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1));
  Node bvand1_1 =
      d_nm.mk_node(Kind::BV_AND, {bvand1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1_1));
  Node bvand1_2 = d_nm.mk_node(Kind::BV_AND, {bvand1, bvand1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), Rewriter().rewrite(bvand1_2));
  //// does not apply
  Node bvand2 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand2, d_rewriter.rewrite(bvand2));
  Node bvand3 =
      d_nm.mk_node(Kind::BV_AND, {bvand2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand3, d_rewriter.rewrite(bvand3));
}

TEST_F(TestRewriterBv, bv_and_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvand0 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand0));
    Node bvand1 = d_nm.mk_node(Kind::BV_AND, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand1));
    Node bvand0_1 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, bvand0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand0_1));
    Node bvand0_2 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, bvand1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand0_2));
    Node bvand0_3 = d_nm.mk_node(Kind::BV_AND, {d_a4, bvand1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand0_3));
    Node bvand1_1 = d_nm.mk_node(Kind::BV_AND, {bvand0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand1_1));
    Node bvand1_2 = d_nm.mk_node(Kind::BV_AND, {bvand1, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand1_2));
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvand0_3));
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvand1_2));
    //// does not apply
    Node bvand2 = d_nm.mk_node(
        Kind::BV_AND, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvand2, d_rewriter.rewrite(bvand2));
    Node bvand3 = d_nm.mk_node(
        Kind::BV_AND,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvand3, d_rewriter.rewrite(bvand3));
    Node bvand4 = d_nm.mk_node(
        Kind::BV_AND,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvand4, d_rewriter.rewrite(bvand4));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvand0 = d_nm.mk_node(Kind::BV_AND, {d_bv1_one, d_a1});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvand0));
    //// does not apply
    Node bvand1 = d_nm.mk_node(Kind::BV_AND, {d_bv4_one, d_a4});
    ASSERT_EQ(bvand1, d_rewriter.rewrite(bvand1));
  }
  ////// special const ones
  {
    //// applies
    // lhs ones
    Node bvand0 = d_nm.mk_node(Kind::BV_AND, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvand0));
  }
}

/* bvashr ------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_ashr_eval)
{
  //// applies
  Node bvashr0 = d_nm.mk_node(Kind::BV_ASHR,
                              {d_nm.mk_value(BitVector(4, "1101")),
                               d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvashr0));
  Node bvashr1 = d_nm.mk_node(Kind::BV_ASHR,
                              {d_nm.mk_value(BitVector(4, "0111")), bvashr0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1));
  Node bvashr1_1 = d_nm.mk_node(Kind::BV_ASHR,
                                {bvashr1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1_1));
  Node bvashr1_2 = d_nm.mk_node(Kind::BV_ASHR, {bvashr1, bvashr1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvashr1_2));
  //// does not apply
  Node bvashr2 = d_nm.mk_node(
      Kind::BV_ASHR,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvashr2, d_rewriter.rewrite(bvashr2));
  Node bvashr3 = d_nm.mk_node(Kind::BV_ASHR,
                              {bvashr2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvashr3, d_rewriter.rewrite(bvashr3));
}

TEST_F(TestRewriterBv, bv_ashr_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvashr0 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr0));
    Node bvashr1 = d_nm.mk_node(Kind::BV_ASHR, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr1));
    Node bvashr0_1 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, bvashr0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr0_1));
    Node bvashr0_2 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, bvashr1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr0_2));
    Node bvashr0_3 = d_nm.mk_node(Kind::BV_ASHR, {d_a4, bvashr0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr0_3));
    Node bvashr1_1 = d_nm.mk_node(Kind::BV_ASHR, {bvashr0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr1_1));
    Node bvashr1_2 = d_nm.mk_node(Kind::BV_ASHR, {bvashr1, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr1_2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvashr0_3));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvashr1_2));
    //// does not apply
    Node bvashr2 = d_nm.mk_node(
        Kind::BV_ASHR, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvashr2, d_rewriter.rewrite(bvashr2));
    Node bvashr3 = d_nm.mk_node(
        Kind::BV_ASHR,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvashr3, d_rewriter.rewrite(bvashr3));
    Node bvashr4 = d_nm.mk_node(
        Kind::BV_ASHR,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvashr4, d_rewriter.rewrite(bvashr4));
  }
}

/* bvconcat ----------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_concat_eval)
{
  //// applies
  Node bvconcat0 = d_nm.mk_node(Kind::BV_CONCAT,
                                {d_nm.mk_value(BitVector(4, "1001")),
                                 d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(8, "10011110")),
            d_rewriter.rewrite(bvconcat0));
  Node bvconcat1 = d_nm.mk_node(
      Kind::BV_CONCAT, {d_nm.mk_value(BitVector(4, "1001")), bvconcat0});
  ASSERT_EQ(d_nm.mk_value(BitVector(12, "100110011110")),
            d_rewriter.rewrite(bvconcat1));
  Node bvconcat1_1 = d_nm.mk_node(
      Kind::BV_CONCAT, {bvconcat1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(16, "1001100111101110")),
            d_rewriter.rewrite(bvconcat1_1));
  Node bvconcat1_2 = d_nm.mk_node(Kind::BV_CONCAT, {bvconcat1, bvconcat1});
  ASSERT_EQ(d_nm.mk_value(BitVector(24, "100110011110100110011110")),
            d_rewriter.rewrite(bvconcat1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(24, "100110011110100110011110")),
            Rewriter().rewrite(bvconcat1_2));
  //// does not apply
  Node bvconcat2 = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat2, d_rewriter.rewrite(bvconcat2));
  Node bvconcat3 = d_nm.mk_node(
      Kind::BV_CONCAT, {bvconcat2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat3, d_rewriter.rewrite(bvconcat3));
}

/* bvmul -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_mul_eval)
{
  //// applies
  Node bvmul0 = d_nm.mk_node(Kind::BV_MUL,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvmul0));
  Node bvmul1 =
      d_nm.mk_node(Kind::BV_MUL, {d_nm.mk_value(BitVector(4, "1001")), bvmul0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvmul1));
  Node bvmul1_1 =
      d_nm.mk_node(Kind::BV_MUL, {bvmul1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), d_rewriter.rewrite(bvmul1_1));
  Node bvmul1_2 = d_nm.mk_node(Kind::BV_MUL, {bvmul1, bvmul1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), d_rewriter.rewrite(bvmul1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), Rewriter().rewrite(bvmul1_2));
  //// does not apply
  Node bvmul2 = d_nm.mk_node(
      Kind::BV_MUL,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul2, d_rewriter.rewrite(bvmul2));
  Node bvmul3 =
      d_nm.mk_node(Kind::BV_MUL, {bvmul2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul3, d_rewriter.rewrite(bvmul3));
}

TEST_F(TestRewriterBv, bv_mul_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvmul0 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul0));
    Node bvmul1 = d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul1));
    Node bvmul0_1 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, bvmul0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul0_1));
    Node bvmul0_2 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, bvmul1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul0_2));
    Node bvmul0_3 = d_nm.mk_node(Kind::BV_MUL, {d_a4, bvmul0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul0_3));
    Node bvmul0_4 = d_nm.mk_node(Kind::BV_MUL, {bvmul0, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul0_4));
    Node bvmul1_1 = d_nm.mk_node(Kind::BV_MUL, {bvmul0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul1_1));
    Node bvmul1_2 = d_nm.mk_node(Kind::BV_MUL, {bvmul1, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul1_2));
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvmul0_4));
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvmul1_2));
    //// does not apply
    Node bvmul2 = d_nm.mk_node(
        Kind::BV_MUL, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvmul2, d_rewriter.rewrite(bvmul2));
    Node bvmul3 = d_nm.mk_node(
        Kind::BV_MUL,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvmul3, d_rewriter.rewrite(bvmul3));
    Node bvmul4 = d_nm.mk_node(
        Kind::BV_MUL,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvmul4, d_rewriter.rewrite(bvmul4));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvmul0 = d_nm.mk_node(Kind::BV_MUL, {d_bv1_one, d_a1});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvmul0));
    Node bvmul1 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_one, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvmul1));
  }
  ////// special const ones
  {
    //// applies
    // lhs ones
    Node bvmul0 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_rewriter.rewrite(d_nm.mk_node(Kind::BV_NEG, {d_a4})),
              d_rewriter.rewrite(bvmul0));
  }
}

/* bvnot -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_not_eval)
{
  //// applies
  Node bvnot0 =
      d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_value(BitVector(4, "1001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), d_rewriter.rewrite(bvnot0));
  Node bvnot1 = d_nm.mk_node(Kind::BV_NOT, {bvnot0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1001")), d_rewriter.rewrite(bvnot1));
  Node bvnot2 = d_nm.mk_node(Kind::BV_NOT, {bvnot1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), d_rewriter.rewrite(bvnot2));

  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), Rewriter().rewrite(bvnot2));
  //// does not apply
  Node bvnot3 = d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_const(d_bv4_type)});
  ASSERT_EQ(bvnot3, d_rewriter.rewrite(bvnot3));
}

/* bvshl -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_shl_eval)
{
  //// applies
  Node bvshl0 = d_nm.mk_node(Kind::BV_SHL,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0010")), d_rewriter.rewrite(bvshl0));
  Node bvshl1 =
      d_nm.mk_node(Kind::BV_SHL, {d_nm.mk_value(BitVector(4, "1111")), bvshl0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1100")), d_rewriter.rewrite(bvshl1));
  Node bvshl1_1 =
      d_nm.mk_node(Kind::BV_SHL, {bvshl1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshl1_1));
  Node bvshl1_2 = d_nm.mk_node(Kind::BV_SHL, {bvshl1, bvshl1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshl1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvshl1_2));
  //// does not apply
  Node bvshl2 = d_nm.mk_node(
      Kind::BV_SHL,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshl2, d_rewriter.rewrite(bvshl2));
  Node bvshl3 =
      d_nm.mk_node(Kind::BV_SHL, {bvshl2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshl3, d_rewriter.rewrite(bvshl3));
}

TEST_F(TestRewriterBv, bv_shl_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvshl0 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl0));
    Node bvshl1 = d_nm.mk_node(Kind::BV_SHL, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl1));
    Node bvshl0_1 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, bvshl0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl0_1));
    Node bvshl0_2 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, bvshl1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl0_2));
    Node bvshl0_3 = d_nm.mk_node(Kind::BV_SHL, {d_a4, bvshl0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl0_3));
    Node bvshl1_1 = d_nm.mk_node(Kind::BV_SHL, {bvshl0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl1_1));
    Node bvshl1_2 = d_nm.mk_node(Kind::BV_SHL, {bvshl1, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl1_2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshl0_3));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshl1_2));
    //// does not apply
    Node bvshl2 = d_nm.mk_node(
        Kind::BV_SHL, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshl2, d_rewriter.rewrite(bvshl2));
    Node bvshl3 = d_nm.mk_node(
        Kind::BV_SHL,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshl3, d_rewriter.rewrite(bvshl3));
    Node bvshl4 = d_nm.mk_node(
        Kind::BV_SHL,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvshl4, d_rewriter.rewrite(bvshl4));
  }
}

/* bvshr -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_shr_eval)
{
  //// applies
  Node bvshr0 = d_nm.mk_node(Kind::BV_SHR,
                             {d_nm.mk_value(BitVector(4, "1101")),
                              d_nm.mk_value(BitVector(4, "0011"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvshr0));
  Node bvshr1 =
      d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_value(BitVector(4, "1111")), bvshr0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0111")), d_rewriter.rewrite(bvshr1));
  Node bvshr1_1 =
      d_nm.mk_node(Kind::BV_SHR, {bvshr1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvshr1_1));
  Node bvshr1_2 = d_nm.mk_node(Kind::BV_SHR, {bvshr1, bvshr1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshr1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvshr1_2));
  //// does not apply
  Node bvshr2 = d_nm.mk_node(
      Kind::BV_SHR,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshr2, d_rewriter.rewrite(bvshr2));
  Node bvshr3 =
      d_nm.mk_node(Kind::BV_SHR, {bvshr2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshr3, d_rewriter.rewrite(bvshr3));
}

TEST_F(TestRewriterBv, bv_shr_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvshr0 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr0));
    Node bvshr1 = d_nm.mk_node(Kind::BV_SHR, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr1));
    Node bvshr0_1 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, bvshr0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr0_1));
    Node bvshr0_2 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, bvshr1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr0_2));
    Node bvshr0_3 = d_nm.mk_node(Kind::BV_SHR, {d_a4, bvshr0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr0_3));
    Node bvshr1_1 = d_nm.mk_node(Kind::BV_SHR, {bvshr0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr1_1));
    Node bvshr1_2 = d_nm.mk_node(Kind::BV_SHR, {bvshr1, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr1_2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshr0_3));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshr1_2));
    //// does not apply
    Node bvshr2 = d_nm.mk_node(
        Kind::BV_SHR, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshr2, d_rewriter.rewrite(bvshr2));
    Node bvshr3 = d_nm.mk_node(
        Kind::BV_SHR,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshr3, d_rewriter.rewrite(bvshr3));
    Node bvshr4 = d_nm.mk_node(
        Kind::BV_SHR,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvshr4, d_rewriter.rewrite(bvshr4));
  }
}

/* bvslt -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_slt_eval)
{
  //// applies
  Node bvslt0 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_true, d_rewriter.rewrite(bvslt0));
  Node bvslt1 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "0001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt1));
  // with empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(bvslt1));
  //// does not apply
  Node bvslt2 = d_nm.mk_node(
      Kind::BV_SLT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvslt2, d_rewriter.rewrite(bvslt2));
}

TEST_F(TestRewriterBv, bv_slt_special_const)
{
  Type bv1_type = d_nm.mk_bv_type(1);
  Node a        = d_nm.mk_const(bv1_type);
  Node b        = d_nm.mk_const(d_bv4_type);
  Node zero     = d_nm.mk_value(BitVector::mk_zero(1));
  Node dis    = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {a, zero})});
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_node(Kind::BV_ADD,
                                           {d_nm.mk_value(BitVector(1, "1")),
                                            d_nm.mk_value(BitVector(1, "0"))}),
                              d_nm.mk_value(BitVector(1, "1"))});
  ////// special const 0
  {
    //// applies
    Node bvslt0 = d_nm.mk_node(Kind::BV_SLT, {zero, a});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt0));
    Node bvslt1 = d_nm.mk_node(Kind::BV_SLT, {a, zero});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvslt1));
    Node bvslt0_1 = d_nm.mk_node(Kind::BV_SLT, {bvadd0, a});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt0_1));
    Node bvslt1_1 = d_nm.mk_node(Kind::BV_SLT, {a, bvadd0});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvslt1_1));
    // with empty cache
    ASSERT_EQ(d_false, Rewriter().rewrite(bvslt0_1));
    ASSERT_EQ(dis, Rewriter().rewrite(bvslt1_1));
    //// does not apply
    Node bvslt2 = d_nm.mk_node(
        Kind::BV_SLT, {d_nm.mk_const(bv1_type), d_nm.mk_const(bv1_type)});
    ASSERT_EQ(bvslt2, d_rewriter.rewrite(bvslt2));
    Node bvslt3 =
        d_nm.mk_node(Kind::BV_SLT, {d_nm.mk_const(d_bv4_type), d_bv4_zero});
    ASSERT_EQ(bvslt3, d_rewriter.rewrite(bvslt3));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvslt0 = d_nm.mk_node(Kind::BV_SLT, {d_bv1_one, d_a1});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_a1})}),
        d_rewriter.rewrite(bvslt0));
    Node bvslt1 = d_nm.mk_node(Kind::BV_SLT,
                               {d_nm.mk_value(BitVector::mk_one(2)),
                                d_nm.mk_const(d_nm.mk_bv_type(2))});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt1));
    //// does not apply
    Node bvslt2 = d_nm.mk_node(Kind::BV_SLT, {d_bv4_one, d_a4});
    ASSERT_EQ(bvslt2, d_rewriter.rewrite(bvslt2));
  }
  ////// special const ones
  {
    //// applies
    // lhs 1
    Node bvslt0 = d_nm.mk_node(Kind::BV_SLT, {d_bv1_ones, d_a1});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_a1})}),
        d_rewriter.rewrite(bvslt0));
    //// does not apply
    Node bvslt2 = d_nm.mk_node(Kind::BV_SLT, {d_bv4_ones, d_a4});
    ASSERT_EQ(bvslt2, d_rewriter.rewrite(bvslt2));
    Node bvslt1 = d_nm.mk_node(Kind::BV_SLT,
                               {d_nm.mk_value(BitVector::mk_ones(2)),
                                d_nm.mk_const(d_nm.mk_bv_type(2))});
    ASSERT_EQ(bvslt1, d_rewriter.rewrite(bvslt1));
  }
}

/* bvudiv-------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_udiv_eval)
{
  //// applies
  Node bvudiv0 = d_nm.mk_node(Kind::BV_UDIV,
                              {d_nm.mk_value(BitVector(4, "1001")),
                               d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvudiv0));
  Node bvudiv1 = d_nm.mk_node(Kind::BV_UDIV,
                              {d_nm.mk_value(BitVector(4, "1001")), bvudiv0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1111")), d_rewriter.rewrite(bvudiv1));
  Node bvudiv1_1 = d_nm.mk_node(Kind::BV_UDIV,
                                {bvudiv1, d_nm.mk_value(BitVector(4, "0110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0010")), d_rewriter.rewrite(bvudiv1_1));
  Node bvudiv1_2 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv1, bvudiv1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvudiv1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), Rewriter().rewrite(bvudiv1_2));
  //// does not apply
  Node bvudiv2 = d_nm.mk_node(
      Kind::BV_UDIV,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv2, d_rewriter.rewrite(bvudiv2));
  Node bvudiv3 = d_nm.mk_node(Kind::BV_UDIV,
                              {bvudiv2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv3, d_rewriter.rewrite(bvudiv3));
}

TEST_F(TestRewriterBv, bv_udiv_special_const)
{
  ////// special const 0
  {
    Node a    = d_nm.mk_const(d_bv4_type);
    Node ones = d_nm.mk_value(BitVector::mk_ones(4));
    Node ite  = d_nm.mk_node(
        Kind::ITE,
        {d_nm.mk_node(Kind::EQUAL, {a, d_bv4_zero}), ones, d_bv4_zero});
    Node ite2 = d_nm.mk_node(
        Kind::ITE,
        {d_nm.mk_node(Kind::EQUAL, {ite, d_bv4_zero}), ones, d_bv4_zero});
    //// applies
    Node bvudiv0 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, a});
    ASSERT_EQ(ite, d_rewriter.rewrite(bvudiv0));
    Node bvudiv1 = d_nm.mk_node(Kind::BV_UDIV, {a, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv1));
    Node bvudiv0_1 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, bvudiv0});
    ASSERT_EQ(ite2, d_rewriter.rewrite(bvudiv0_1));
    Node bvudiv0_2 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, bvudiv1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvudiv0_2));
    Node bvudiv0_3 = d_nm.mk_node(Kind::BV_UDIV, {a, bvudiv0});
    ASSERT_EQ(d_nm.mk_node(Kind::BV_UDIV, {a, ite}),
              d_rewriter.rewrite(bvudiv0_3));
    Node bvudiv1_1 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv0, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv1_1));
    Node bvudiv1_2 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv1, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv1_2));
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvudiv0_2));
    ASSERT_EQ(ones, Rewriter().rewrite(bvudiv1_2));
    //// does not apply
    Node bvudiv2 = d_nm.mk_node(
        Kind::BV_UDIV, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvudiv2, d_rewriter.rewrite(bvudiv2));
    Node bvudiv3 = d_nm.mk_node(
        Kind::BV_UDIV,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvudiv3, d_rewriter.rewrite(bvudiv3));
    Node bvudiv4 = d_nm.mk_node(
        Kind::BV_UDIV,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvudiv4, d_rewriter.rewrite(bvudiv4));
  }
}

/* bvult -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_ult_eval)
{
  //// applies
  Node bvult0 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_true, d_rewriter.rewrite(bvult0));
  Node bvult1 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1110")),
                              d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(bvult1));
  // with empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(bvult1));
  //// does not apply
  Node bvult2 = d_nm.mk_node(
      Kind::BV_ULT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvult2, d_rewriter.rewrite(bvult2));
}

TEST_F(TestRewriterBv, bv_ult_special_const)
{
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_node(Kind::BV_ADD,
                                           {d_nm.mk_value(BitVector(1, "1")),
                                            d_nm.mk_value(BitVector(1, "0"))}),
                              d_nm.mk_value(BitVector(1, "1"))});
  ////// special const 0
  {
    Node dis = d_nm.mk_node(Kind::NOT,
                            {d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, d_a1})});
    //// applies
    Node bvult0 = d_nm.mk_node(Kind::BV_ULT, {d_bv1_zero, d_a1});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvult0));
    Node bvult1 = d_nm.mk_node(Kind::BV_ULT, {d_a1, d_bv1_zero});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult1));
    Node bvult0_1 = d_nm.mk_node(Kind::BV_ULT, {bvadd0, d_a1});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvult0_1));
    Node bvult1_1 = d_nm.mk_node(Kind::BV_ULT, {d_a1, bvadd0});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult1_1));
    // with empty cache
    ASSERT_EQ(dis, Rewriter().rewrite(bvult0_1));
    ASSERT_EQ(d_false, Rewriter().rewrite(bvult1_1));
    //// does not apply
    Node bvult2 = d_nm.mk_node(
        Kind::BV_ULT, {d_nm.mk_const(d_bv1_type), d_nm.mk_const(d_bv1_type)});
    ASSERT_EQ(bvult2, d_rewriter.rewrite(bvult2));
    Node bvult3 =
        d_nm.mk_node(Kind::BV_ULT, {d_nm.mk_const(d_bv4_type), d_bv4_zero});
    ASSERT_EQ(bvult3, d_rewriter.rewrite(bvult3));
  }
  ////// special const 1
  {
    Node dis1 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv1_ones, d_a1})});
    Node dis4 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, d_a4})});
    //// applies
    // lhs 1
    Node bvult0 = d_nm.mk_node(Kind::BV_ULT, {d_bv1_one, d_a1});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult0));
    //// does not apply
    Node bvult1 = d_nm.mk_node(Kind::BV_ULT, {d_bv4_one, d_a4});
    ASSERT_EQ(bvult1, d_rewriter.rewrite(bvult1));
  }
  ////// special const ones
  {
    Node bvult0 = d_nm.mk_node(Kind::BV_ULT, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult0));
  }
}

/* bvudiv-------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_urem_eval)
{
  //// applies
  Node bvurem0 = d_nm.mk_node(Kind::BV_UREM,
                              {d_nm.mk_value(BitVector(4, "1001")),
                               d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1001")), d_rewriter.rewrite(bvurem0));
  Node bvurem1 = d_nm.mk_node(Kind::BV_UREM,
                              {d_nm.mk_value(BitVector(4, "1001")), bvurem0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1));
  Node bvurem1_1 = d_nm.mk_node(Kind::BV_UREM,
                                {bvurem1, d_nm.mk_value(BitVector(4, "0110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1_1));
  Node bvurem1_2 = d_nm.mk_node(Kind::BV_UREM, {bvurem1, bvurem1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvurem1_2));
  //// does not apply
  Node bvurem2 = d_nm.mk_node(
      Kind::BV_UREM,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem2, d_rewriter.rewrite(bvurem2));
  Node bvurem3 = d_nm.mk_node(Kind::BV_UREM,
                              {bvurem2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem3, d_rewriter.rewrite(bvurem3));
}

TEST_F(TestRewriterBv, bv_urem_special_const)
{
  ////// special const 0
  {
    //// applies
    Node bvurem0 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem0));
    Node bvurem1 = d_nm.mk_node(Kind::BV_UREM, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem1));
    Node bvurem0_1 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, bvurem0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem0_1));
    Node bvurem0_2 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, bvurem1});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem0_2));
    Node bvurem0_3 = d_nm.mk_node(Kind::BV_UREM, {d_a4, bvurem0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem0_3));
    Node bvurem1_1 = d_nm.mk_node(Kind::BV_UREM, {bvurem0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem1_1));
    Node bvurem1_2 = d_nm.mk_node(Kind::BV_UREM, {bvurem1, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem1_2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvurem0_3));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvurem1_2));
    //// does not apply
    Node bvurem2 = d_nm.mk_node(
        Kind::BV_UREM, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvurem2, d_rewriter.rewrite(bvurem2));
    Node bvurem3 = d_nm.mk_node(
        Kind::BV_UREM,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvurem3, d_rewriter.rewrite(bvurem3));
    Node bvurem4 = d_nm.mk_node(
        Kind::BV_UREM,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvurem4, d_rewriter.rewrite(bvurem4));
  }
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterBv, bv_nand_elim) { test_elim_rule_bv(Kind::BV_NAND); }

TEST_F(TestRewriterBv, bv_neg_elim) { test_elim_rule_bv(Kind::BV_NEG); }

TEST_F(TestRewriterBv, bv_nor_elim) { test_elim_rule_bv(Kind::BV_NOR); }

TEST_F(TestRewriterBv, bv_or_elim) { test_elim_rule_bv(Kind::BV_OR); }

TEST_F(TestRewriterBv, bv_redand_elim) { test_elim_rule_bv(Kind::BV_REDAND); }

TEST_F(TestRewriterBv, bv_redor_elim) { test_elim_rule_bv(Kind::BV_REDOR); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_redxor_elim) { test_elim_rule_bv(Kind::BV_REDXOR);
// }

TEST_F(TestRewriterBv, bv_roli_elim) { test_elim_rule_bv(Kind::BV_ROLI); }

TEST_F(TestRewriterBv, bv_rori_elim) { test_elim_rule_bv(Kind::BV_RORI); }

TEST_F(TestRewriterBv, bv_repeat_elim) { test_elim_rule_bv(Kind::BV_REPEAT); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_saddo_elim) { test_elim_rule_bv(Kind::BV_SADDO); }

TEST_F(TestRewriterBv, bv_sdiv_elim) { test_elim_rule_bv(Kind::BV_SDIV); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_sdivo_elim) { test_elim_rule_bv(Kind::BV_SDIVO); }

TEST_F(TestRewriterBv, bv_sge_elim) { test_elim_rule_bv(Kind::BV_SGE); }

TEST_F(TestRewriterBv, bv_sgt_elim) { test_elim_rule_bv(Kind::BV_SGT); }

TEST_F(TestRewriterBv, bv_sign_extend_elim)
{
  test_elim_rule_bv(Kind::BV_SIGN_EXTEND);
}

TEST_F(TestRewriterBv, bv_sle_elim) { test_elim_rule_bv(Kind::BV_SLE); }

TEST_F(TestRewriterBv, bv_smod_elim) { test_elim_rule_bv(Kind::BV_SMOD); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_smulo_elim) { test_elim_rule_bv(Kind::BV_SMULO); }

TEST_F(TestRewriterBv, bv_srem_elim) { test_elim_rule_bv(Kind::BV_SREM); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_ssubo_elim) { test_elim_rule_bv(Kind::BV_SSUBO); }

TEST_F(TestRewriterBv, bv_sub_elim) { test_elim_rule_bv(Kind::BV_SUB); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_uaddo_elim) { test_elim_rule_bv(Kind::BV_UADDO); }

TEST_F(TestRewriterBv, bv_uge_elim) { test_elim_rule_bv(Kind::BV_UGE); }

TEST_F(TestRewriterBv, bv_ugt_elim) { test_elim_rule_bv(Kind::BV_UGT); }

TEST_F(TestRewriterBv, bv_ule_elim) { test_elim_rule_bv(Kind::BV_ULE); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_umulo_elim) { test_elim_rule_bv(Kind::BV_UMULO); }
// TEST_F(TestRewriterBv, bv_usubo_elim) { test_elim_rule_bv(Kind::BV_USUBO); }

TEST_F(TestRewriterBv, bv_xnor_elim) { test_elim_rule_bv(Kind::BV_XNOR); }

TEST_F(TestRewriterBv, bv_xor_elim) { test_elim_rule_bv(Kind::BV_XOR); }

TEST_F(TestRewriterBv, bv_zero_extend_elim)
{
  test_elim_rule_bv(Kind::BV_ZERO_EXTEND);
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
