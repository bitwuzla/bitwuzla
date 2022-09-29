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
  Node bvadd_x0 = d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd_x0, d_rewriter.rewrite(bvadd_x0));
  Node bvadd_x1 = d_nm.mk_node(Kind::BV_ADD,
                               {bvadd_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd_x1, d_rewriter.rewrite(bvadd_x1));
}

TEST_F(TestRewriterBv, bv_add_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvadd_lhs0 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_lhs0));
    Node bvadd_lhs1 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, bvadd_lhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_lhs1));
    // rhs 0
    Node bvadd_rhs0 = d_nm.mk_node(Kind::BV_ADD, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_rhs0));
    Node bvadd_rhs1 = d_nm.mk_node(Kind::BV_ADD, {bvadd_lhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_rhs1));
    Node bvadd_rhs2 = d_nm.mk_node(Kind::BV_ADD, {bvadd_rhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_rhs2));
    // lhs 0
    Node bvadd_lhs2 = d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, bvadd_rhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvadd_lhs2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvadd_rhs1));
    //// does not apply
    Node bvadd_x0 = d_nm.mk_node(
        Kind::BV_ADD, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvadd_x0, d_rewriter.rewrite(bvadd_x0));
    Node bvadd_x1 = d_nm.mk_node(
        Kind::BV_ADD,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvadd_x1, d_rewriter.rewrite(bvadd_x1));
    Node bvadd_x2 = d_nm.mk_node(
        Kind::BV_ADD,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvadd_x2, d_rewriter.rewrite(bvadd_x2));
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
  Node bvand_x0 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand_x0, d_rewriter.rewrite(bvand_x0));
  Node bvand_x1 = d_nm.mk_node(Kind::BV_AND,
                               {bvand_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand_x1, d_rewriter.rewrite(bvand_x1));
}

TEST_F(TestRewriterBv, bv_and_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvand_lhs0 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_lhs0));
    Node bvand_lhs1 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, bvand_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_lhs1));
    // rhs 0
    Node bvand_rhs0 = d_nm.mk_node(Kind::BV_AND, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_rhs0));
    Node bvand_rhs1 = d_nm.mk_node(Kind::BV_AND, {bvand_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_rhs1));
    Node bvand_rhs2 = d_nm.mk_node(Kind::BV_AND, {bvand_rhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_rhs2));
    Node bvand_rhs3 = d_nm.mk_node(Kind::BV_AND, {d_a4, bvand_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_rhs3));
    // lhs 0
    Node bvand_lhs2 = d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, bvand_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvand_lhs2));
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvand_rhs3));
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvand_rhs2));
    //// does not apply
    Node bvand_x0 = d_nm.mk_node(Kind::BV_AND, {d_a4, d_a4});
    ASSERT_EQ(bvand_x0, d_rewriter.rewrite(bvand_x0));
    Node bvand_x1 =
        d_nm.mk_node(Kind::BV_AND, {d_nm.mk_value(BitVector(4, "1110")), d_a4});
    ASSERT_EQ(bvand_x1, d_rewriter.rewrite(bvand_x1));
    Node bvand_x2 =
        d_nm.mk_node(Kind::BV_AND, {d_a4, d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvand_x2, d_rewriter.rewrite(bvand_x2));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvand_lhs0 = d_nm.mk_node(Kind::BV_AND, {d_bv1_one, d_a1});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvand_lhs0));
    // rhs 1
    Node bvand_rhs0 = d_nm.mk_node(Kind::BV_AND, {d_a1, d_bv1_one});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvand_rhs0));
    //// does not apply
    Node bvand_x0 = d_nm.mk_node(Kind::BV_AND, {d_bv4_one, d_a4});
    ASSERT_EQ(bvand_x0, d_rewriter.rewrite(bvand_x0));
  }
  ////// special const ones
  {
    //// applies
    // lhs ones
    Node bvand_lhs0 = d_nm.mk_node(Kind::BV_AND, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvand_lhs0));
    //// does not apply
    Node bvand_x0 = d_nm.mk_node(Kind::BV_AND, {d_a4, d_bv4_ones});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvand_x0));
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
  Node bvashr_x0 = d_nm.mk_node(
      Kind::BV_ASHR,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvashr_x0, d_rewriter.rewrite(bvashr_x0));
  Node bvashr_x1 = d_nm.mk_node(
      Kind::BV_ASHR, {bvashr_x0, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvashr_x1, d_rewriter.rewrite(bvashr_x1));
}

TEST_F(TestRewriterBv, bv_ashr_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvashr_lhs0 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr_lhs0));
    Node bvashr_lhs1 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, bvashr_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr_lhs1));
    // rhs 0
    Node bvashr_rhs0 = d_nm.mk_node(Kind::BV_ASHR, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr_rhs0));
    Node bvashr_rhs1 = d_nm.mk_node(Kind::BV_ASHR, {d_a4, bvashr_lhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr_rhs1));
    Node bvashr_rhs2 = d_nm.mk_node(Kind::BV_ASHR, {bvashr_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr_rhs2));
    Node bvashr_rhs3 = d_nm.mk_node(Kind::BV_ASHR, {bvashr_rhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvashr_rhs3));
    // lhs 0
    Node bvashr_lhs2 = d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, bvashr_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvashr_lhs2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvashr_rhs1));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvashr_rhs3));
    //// does not apply
    Node bvashr_x0 = d_nm.mk_node(
        Kind::BV_ASHR, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvashr_x0, d_rewriter.rewrite(bvashr_x0));
    Node bvashr_x1 = d_nm.mk_node(
        Kind::BV_ASHR,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvashr_x1, d_rewriter.rewrite(bvashr_x1));
    Node bvashr_x2 = d_nm.mk_node(
        Kind::BV_ASHR,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvashr_x2, d_rewriter.rewrite(bvashr_x2));
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
  Node bvconcat_x0 = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat_x0, d_rewriter.rewrite(bvconcat_x0));
  Node bvconcat_x1 = d_nm.mk_node(
      Kind::BV_CONCAT, {bvconcat_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat_x1, d_rewriter.rewrite(bvconcat_x1));
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
  Node bvmul_x0 = d_nm.mk_node(
      Kind::BV_MUL,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul_x0, d_rewriter.rewrite(bvmul_x0));
  Node bvmul_x1 = d_nm.mk_node(Kind::BV_MUL,
                               {bvmul_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul_x1, d_rewriter.rewrite(bvmul_x1));
}

TEST_F(TestRewriterBv, bv_mul_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvmul_lhs0 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_lhs0));
    Node bvmul_lhs1 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, bvmul_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_lhs1));
    Node bvmul_lhs3 = d_nm.mk_node(Kind::BV_MUL, {bvmul_lhs0, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_lhs3));
    // rhs 0
    Node bvmul_rhs0 = d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_rhs0));
    Node bvmul_rhs1 = d_nm.mk_node(Kind::BV_MUL, {d_a4, bvmul_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_rhs1));
    Node bvmul_rhs2 = d_nm.mk_node(Kind::BV_MUL, {bvmul_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_rhs2));
    Node bvmul_rhs3 = d_nm.mk_node(Kind::BV_MUL, {bvmul_rhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_rhs3));
    // lhs 0
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvmul_lhs1));
    Node bvmul_lhs2 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, bvmul_rhs0});
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvmul_lhs3));
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvmul_rhs3));
    //// does not apply
    Node bvmul_x0 = d_nm.mk_node(
        Kind::BV_MUL, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvmul_x0, d_rewriter.rewrite(bvmul_x0));
    Node bvmul_x1 = d_nm.mk_node(
        Kind::BV_MUL,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvmul_x1, d_rewriter.rewrite(bvmul_x1));
    Node bvmul_x2 = d_nm.mk_node(
        Kind::BV_MUL,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvmul_x2, d_rewriter.rewrite(bvmul_x2));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvmul_lhs0 = d_nm.mk_node(Kind::BV_MUL, {d_bv1_one, d_a1});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvmul_lhs0));
    Node bvmul_lhs1 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_one, d_a4});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvmul_lhs1));
    // rhs 1
    Node bvmul_rhs0 = d_nm.mk_node(Kind::BV_MUL, {d_a1, d_bv1_one});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvmul_rhs0));
    Node bvmul_rhs1 = d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_one});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvmul_rhs1));
  }
  ////// special const ones
  {
    //// applies
    // lhs ones
    Node bvmul_lhs0 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_rewriter.rewrite(d_nm.mk_node(Kind::BV_NEG, {d_a4})),
              d_rewriter.rewrite(bvmul_lhs0));
    // rhs ones
    Node bvmul_rhs0 = d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_ones});
    ASSERT_EQ(d_rewriter.rewrite(d_nm.mk_node(Kind::BV_NEG, {d_a4})),
              d_rewriter.rewrite(bvmul_rhs0));
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
  Node bvnot_x0 = d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_const(d_bv4_type)});
  ASSERT_EQ(bvnot_x0, d_rewriter.rewrite(bvnot_x0));
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
  Node bvshl_x0 = d_nm.mk_node(
      Kind::BV_SHL,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshl_x0, d_rewriter.rewrite(bvshl_x0));
  Node bvshl_x1 = d_nm.mk_node(Kind::BV_SHL,
                               {bvshl_x0, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshl_x1, d_rewriter.rewrite(bvshl_x1));
}

TEST_F(TestRewriterBv, bv_shl_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvshl_lhs0 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl_lhs0));
    Node bvshl_lhs1 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, bvshl_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl_lhs1));
    // rhs 0
    Node bvshl_rhs0 = d_nm.mk_node(Kind::BV_SHL, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl_rhs0));
    Node bvshl_rhs1 = d_nm.mk_node(Kind::BV_SHL, {d_a4, bvshl_lhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl_rhs1));
    Node bvshl_rhs2 = d_nm.mk_node(Kind::BV_SHL, {bvshl_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl_rhs2));
    Node bvshl_rhs3 = d_nm.mk_node(Kind::BV_SHL, {bvshl_rhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshl_rhs3));
    // lhs 0
    Node bvshl_lhs2 = d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, bvshl_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshl_lhs2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshl_rhs1));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshl_rhs3));
    //// does not apply
    Node bvshl_x0 = d_nm.mk_node(
        Kind::BV_SHL, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshl_x0, d_rewriter.rewrite(bvshl_x0));
    Node bvshl_x1 = d_nm.mk_node(
        Kind::BV_SHL,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshl_x1, d_rewriter.rewrite(bvshl_x1));
    Node bvshl_x2 = d_nm.mk_node(
        Kind::BV_SHL,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvshl_x2, d_rewriter.rewrite(bvshl_x2));
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
  Node bvshr_x0 = d_nm.mk_node(
      Kind::BV_SHR,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshr_x0, d_rewriter.rewrite(bvshr_x0));
  Node bvshr_x1 = d_nm.mk_node(Kind::BV_SHR,
                               {bvshr_x0, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshr_x1, d_rewriter.rewrite(bvshr_x1));
}

TEST_F(TestRewriterBv, bv_shr_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvshr_lhs0 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr_lhs0));
    Node bvshr_lhs1 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, bvshr_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr_lhs1));
    // rhs 0
    Node bvshr_rhs0 = d_nm.mk_node(Kind::BV_SHR, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr_rhs0));
    Node bvshr_rhs1 = d_nm.mk_node(Kind::BV_SHR, {d_a4, bvshr_lhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr_rhs1));
    Node bvshr_rhs2 = d_nm.mk_node(Kind::BV_SHR, {bvshr_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr_rhs2));
    Node bvshr_rhs4 = d_nm.mk_node(Kind::BV_SHR, {bvshr_rhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvshr_rhs4));
    // lhs 0
    Node bvshr_lhs2 = d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, bvshr_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvshr_lhs2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshr_rhs1));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvshr_rhs4));
    //// does not apply
    Node bvshr_x0 = d_nm.mk_node(
        Kind::BV_SHR, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshr_x0, d_rewriter.rewrite(bvshr_x0));
    Node bvshr_x1 = d_nm.mk_node(
        Kind::BV_SHR,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvshr_x1, d_rewriter.rewrite(bvshr_x1));
    Node bvshr_x2 = d_nm.mk_node(
        Kind::BV_SHR,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvshr_x2, d_rewriter.rewrite(bvshr_x2));
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
  Node bvslt_x0 = d_nm.mk_node(
      Kind::BV_SLT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvslt_x0, d_rewriter.rewrite(bvslt_x0));
}

TEST_F(TestRewriterBv, bv_slt_special_const)
{
  Node a2      = d_nm.mk_const(d_nm.mk_bv_type(2));
  Node bv2_one = d_nm.mk_value(BitVector::mk_one(2));
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_node(Kind::BV_ADD,
                                           {d_nm.mk_value(BitVector(1, "1")),
                                            d_nm.mk_value(BitVector(1, "0"))}),
                              d_nm.mk_value(BitVector(1, "1"))});
  ////// special const 0
  {
    Node dis = d_nm.mk_node(Kind::NOT,
                            {d_nm.mk_node(Kind::EQUAL, {d_a1, d_bv1_zero})});
    //// applies
    // lhs 0
    Node bvslt_lhs0 = d_nm.mk_node(Kind::BV_SLT, {d_bv1_zero, d_a1});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_lhs0));
    Node bvslt_lhs1 = d_nm.mk_node(Kind::BV_SLT, {bvadd0, d_a1});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_lhs1));
    // rhs 0
    Node bvslt_rhs0 = d_nm.mk_node(Kind::BV_SLT, {d_a1, d_bv1_zero});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvslt_rhs0));
    Node bvslt_rhs1 = d_nm.mk_node(Kind::BV_SLT, {d_a1, bvadd0});
    ASSERT_EQ(dis, d_rewriter.rewrite(bvslt_rhs1));
    // with empty cache
    ASSERT_EQ(d_false, Rewriter().rewrite(bvslt_lhs1));
    ASSERT_EQ(dis, Rewriter().rewrite(bvslt_rhs1));
    //// does not apply
    Node bvslt_x0 = d_nm.mk_node(
        Kind::BV_SLT, {d_nm.mk_const(d_bv1_type), d_nm.mk_const(d_bv1_type)});
    ASSERT_EQ(bvslt_x0, d_rewriter.rewrite(bvslt_x0));
    Node bvslt_x1 =
        d_nm.mk_node(Kind::BV_SLT, {d_nm.mk_const(d_bv4_type), d_bv4_zero});
    ASSERT_EQ(bvslt_x1, d_rewriter.rewrite(bvslt_x1));
  }
  ////// special const 1
  {
    //// applies
    // lhs 1
    Node bvslt_lhs0 = d_nm.mk_node(Kind::BV_SLT, {d_bv1_one, d_a1});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_a1})}),
        d_rewriter.rewrite(bvslt_lhs0));
    Node bvslt_lhs1 = d_nm.mk_node(Kind::BV_SLT, {bv2_one, a2});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_lhs1));
    // rhs 1
    Node bvslt_rhs0 = d_nm.mk_node(Kind::BV_SLT, {d_a1, d_bv1_one});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_rhs0));
    Node bvslt_rhs1 = d_nm.mk_node(Kind::BV_SLT, {a2, bv2_one});
    ASSERT_EQ(Rewriter().rewrite(d_nm.mk_node(Kind::DISTINCT, {a2, bv2_one})),
              d_rewriter.rewrite(bvslt_rhs1));
    //// does not apply
    Node bvslt_x0 = d_nm.mk_node(Kind::BV_SLT, {d_bv4_one, d_a4});
    ASSERT_EQ(bvslt_x0, d_rewriter.rewrite(bvslt_x0));
    Node bvslt_x1 = d_nm.mk_node(Kind::BV_SLT, {d_a4, d_bv4_one});
    ASSERT_EQ(bvslt_x1, d_rewriter.rewrite(bvslt_x1));
  }
  ////// special const ones
  {
    //// applies
    // lhs 1
    Node bvslt_lhs0 = d_nm.mk_node(Kind::BV_SLT, {d_bv1_ones, d_a1});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_a1})}),
        d_rewriter.rewrite(bvslt_lhs0));
    //// does not apply
    Node bvslt_x0 = d_nm.mk_node(Kind::BV_SLT, {d_bv4_ones, d_a4});
    ASSERT_EQ(bvslt_x0, d_rewriter.rewrite(bvslt_x0));
    Node bvslt_x1 = d_nm.mk_node(Kind::BV_SLT,
                                 {d_nm.mk_value(BitVector::mk_ones(2)),
                                  d_nm.mk_const(d_nm.mk_bv_type(2))});
    ASSERT_EQ(bvslt_x1, d_rewriter.rewrite(bvslt_x1));
  }
  ////// special const min_signed
  {
    Node min1_s = d_nm.mk_value(BitVector::mk_min_signed(1));
    Node min4_s = d_nm.mk_value(BitVector::mk_min_signed(4));
    //// applies
    // lhs min_signed
    Node bvslt_lhs0 = d_nm.mk_node(Kind::BV_SLT, {min1_s, d_a1});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {min1_s, d_a1})}),
        d_rewriter.rewrite(bvslt_lhs0));
    Node bvslt_lhs1 = d_nm.mk_node(Kind::BV_SLT, {min4_s, d_a4});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {min4_s, d_a4})}),
        d_rewriter.rewrite(bvslt_lhs1));
    // rhs min_signed
    Node bvslt_rhs0 = d_nm.mk_node(Kind::BV_SLT, {d_a1, min1_s});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_rhs0));
    Node bvslt_rhs1 = d_nm.mk_node(Kind::BV_SLT, {d_a4, min4_s});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_rhs1));
  }
  ////// special const max_signed
  {
    Node max1_s = d_nm.mk_value(BitVector::mk_max_signed(1));
    Node max4_s = d_nm.mk_value(BitVector::mk_max_signed(4));
    //// applies
    // lhs max_signed
    Node bvslt_lhs0 = d_nm.mk_node(Kind::BV_SLT, {max1_s, d_a1});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_lhs0));
    Node bvslt_lhs1 = d_nm.mk_node(Kind::BV_SLT, {max4_s, d_a4});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt_lhs1));
    // rhs max_signed
    Node bvslt_rhs0 = d_nm.mk_node(Kind::BV_SLT, {d_a1, max1_s});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_a1, max1_s})}),
        d_rewriter.rewrite(bvslt_rhs0));
    Node bvslt_rhs1 = d_nm.mk_node(Kind::BV_SLT, {d_a4, max4_s});
    ASSERT_EQ(
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {d_a4, max4_s})}),
        d_rewriter.rewrite(bvslt_rhs1));
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
  Node bvudiv_x0 = d_nm.mk_node(
      Kind::BV_UDIV,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv_x0, d_rewriter.rewrite(bvudiv_x0));
  Node bvudiv_x1 = d_nm.mk_node(
      Kind::BV_UDIV, {bvudiv_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv_x1, d_rewriter.rewrite(bvudiv_x1));
}

TEST_F(TestRewriterBv, bv_udiv_special_const)
{
  ////// special const 0
  {
    Node ones = d_nm.mk_value(BitVector::mk_ones(4));
    Node ite  = d_nm.mk_node(
        Kind::ITE,
        {d_nm.mk_node(Kind::EQUAL, {d_a4, d_bv4_zero}), ones, d_bv4_zero});
    Node ite2 = d_nm.mk_node(
        Kind::ITE,
        {d_nm.mk_node(Kind::EQUAL, {ite, d_bv4_zero}), ones, d_bv4_zero});
    //// applies
    // lhs 0
    Node bvudiv_lhs0 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, d_a4});
    ASSERT_EQ(ite, d_rewriter.rewrite(bvudiv_lhs0));
    Node bvudiv_lhs1 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, bvudiv_lhs0});
    ASSERT_EQ(ite2, d_rewriter.rewrite(bvudiv_lhs1));
    // rhs 0
    Node bvudiv_rhs0 = d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv_rhs0));
    Node bvudiv_rhs1 = d_nm.mk_node(Kind::BV_UDIV, {d_a4, bvudiv_lhs0});
    ASSERT_EQ(d_nm.mk_node(Kind::BV_UDIV, {d_a4, ite}),
              d_rewriter.rewrite(bvudiv_rhs1));
    Node bvudiv_rhs2 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv_lhs0, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv_rhs2));
    Node bvudiv_rhs3 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv_rhs0, d_bv4_zero});
    ASSERT_EQ(ones, d_rewriter.rewrite(bvudiv_rhs3));
    // lhs 0
    Node bvudiv_lhs2 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, bvudiv_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvudiv_lhs2));
    // with empty cache
    ASSERT_EQ(d_bv4_zero, Rewriter().rewrite(bvudiv_lhs2));
    ASSERT_EQ(ones, Rewriter().rewrite(bvudiv_rhs3));
    //// does not apply
    Node bvudiv_x0 = d_nm.mk_node(
        Kind::BV_UDIV, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvudiv_x0, d_rewriter.rewrite(bvudiv_x0));
    Node bvudiv_x1 = d_nm.mk_node(
        Kind::BV_UDIV,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvudiv_x1, d_rewriter.rewrite(bvudiv_x1));
    Node bvudiv_x2 = d_nm.mk_node(
        Kind::BV_UDIV,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvudiv_x2, d_rewriter.rewrite(bvudiv_x2));
  }
  ////// special const 1
  {
    //// applies
    // rhs 1
    Node bvudiv_rhs0 = d_nm.mk_node(Kind::BV_UDIV, {d_a1, d_bv1_one});
    ASSERT_EQ(d_a1, d_rewriter.rewrite(bvudiv_rhs0));
    Node bvudiv_rhs1 = d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_bv4_one});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvudiv_rhs1));
    //// does not apply
    Node bvudiv_x0 = d_nm.mk_node(Kind::BV_UDIV, {d_bv1_one, d_a1});
    ASSERT_EQ(bvudiv_x0, d_rewriter.rewrite(bvudiv_x0));
    Node bvudiv_x1 = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_one, d_a4});
    ASSERT_EQ(bvudiv_x1, d_rewriter.rewrite(bvudiv_x1));
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
  Node bvult_x0 = d_nm.mk_node(
      Kind::BV_ULT,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvult_x0, d_rewriter.rewrite(bvult_x0));
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
    Node dis1 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, d_a1})});
    Node dis4 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_a4})});
    //// applies
    // lhs 0
    Node bvult_lhs0 = d_nm.mk_node(Kind::BV_ULT, {d_bv1_zero, d_a1});
    ASSERT_EQ(dis1, d_rewriter.rewrite(bvult_lhs0));
    Node bvult_lhs1 = d_nm.mk_node(Kind::BV_ULT, {bvadd0, d_a1});
    ASSERT_EQ(dis1, d_rewriter.rewrite(bvult_lhs1));
    Node bvult_lhs2 = d_nm.mk_node(Kind::BV_ULT, {d_bv4_zero, d_a4});
    ASSERT_EQ(dis4, d_rewriter.rewrite(bvult_lhs2));
    // rhs 0
    Node bvult_rhs0 = d_nm.mk_node(Kind::BV_ULT, {d_a1, d_bv1_zero});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult_rhs0));
    Node bvult_rhs1 = d_nm.mk_node(Kind::BV_ULT, {d_a1, bvadd0});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult_rhs1));
    Node bvult_rhs2 = d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult_rhs2));
    // with empty cache
    ASSERT_EQ(dis1, Rewriter().rewrite(bvult_lhs1));
    ASSERT_EQ(d_false, Rewriter().rewrite(bvult_rhs1));
    //// does not apply
    Node bvult_x0 = d_nm.mk_node(
        Kind::BV_ULT, {d_nm.mk_const(d_bv1_type), d_nm.mk_const(d_bv1_type)});
    ASSERT_EQ(bvult_x0, d_rewriter.rewrite(bvult_x0));
  }
  ////// special const 1
  {
    Node dis1 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv1_ones, d_a1})});
    Node dis4 = d_nm.mk_node(Kind::NOT,
                             {d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, d_a4})});
    //// applies
    // lhs 1
    Node bvult_lhs0 = d_nm.mk_node(Kind::BV_ULT, {d_bv1_one, d_a1});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult_lhs0));
    // rhs 1
    Node bvult_rhs0 = d_nm.mk_node(Kind::BV_ULT, {d_a1, d_bv1_one});
    ASSERT_EQ(d_nm.mk_node(Kind::EQUAL, {d_a1, d_bv1_zero}),
              d_rewriter.rewrite(bvult_rhs0));
    Node bvult_rhs1 = d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_one});
    ASSERT_EQ(d_nm.mk_node(Kind::EQUAL, {d_a4, d_bv4_zero}),
              d_rewriter.rewrite(bvult_rhs1));
    //// does not apply
    Node bvult_x0 = d_nm.mk_node(Kind::BV_ULT, {d_bv4_one, d_a4});
    ASSERT_EQ(bvult_x0, d_rewriter.rewrite(bvult_x0));
  }
  ////// special const ones
  {
    //// applies
    // lhs ones
    Node bvult_lhs0 = d_nm.mk_node(Kind::BV_ULT, {d_bv4_ones, d_a4});
    ASSERT_EQ(d_false, d_rewriter.rewrite(bvult_lhs0));
    //// does not apply
    Node bvult_x0 = d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_ones});
    ASSERT_EQ(
        Rewriter().rewrite(d_nm.mk_node(Kind::DISTINCT, {d_a4, d_bv4_ones})),
        d_rewriter.rewrite(bvult_x0));
  }
}

/* bvurem ------------------------------------------------------------------- */

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
  Node bvurem_x0 = d_nm.mk_node(
      Kind::BV_UREM,
      {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem_x0, d_rewriter.rewrite(bvurem_x0));
  Node bvurem_x1 = d_nm.mk_node(
      Kind::BV_UREM, {bvurem_x0, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem_x1, d_rewriter.rewrite(bvurem_x1));
}

TEST_F(TestRewriterBv, bv_urem_special_const)
{
  ////// special const 0
  {
    //// applies
    // lhs 0
    Node bvurem_lhs0 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, d_a4});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem_lhs0));
    Node bvurem_lhs1 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, bvurem_lhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem_lhs1));
    // rhs 0
    Node bvurem_rhs0 = d_nm.mk_node(Kind::BV_UREM, {d_a4, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem_rhs0));
    Node bvurem_rhs1 = d_nm.mk_node(Kind::BV_UREM, {d_a4, bvurem_lhs0});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem_rhs1));
    Node bvurem_rhs2 = d_nm.mk_node(Kind::BV_UREM, {bvurem_lhs0, d_bv4_zero});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem_rhs2));
    Node bvurem_rhs3 = d_nm.mk_node(Kind::BV_UREM, {bvurem_rhs0, d_bv4_zero});
    ASSERT_EQ(d_a4, d_rewriter.rewrite(bvurem_rhs3));
    // lhs 0
    Node bvurem_lhs2 = d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, bvurem_rhs0});
    ASSERT_EQ(d_bv4_zero, d_rewriter.rewrite(bvurem_lhs2));
    // with empty cache
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvurem_rhs1));
    ASSERT_EQ(d_a4, Rewriter().rewrite(bvurem_rhs3));
    //// does not apply
    Node bvurem_x0 = d_nm.mk_node(
        Kind::BV_UREM, {d_nm.mk_const(d_bv4_type), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvurem_x0, d_rewriter.rewrite(bvurem_x0));
    Node bvurem_x1 = d_nm.mk_node(
        Kind::BV_UREM,
        {d_nm.mk_value(BitVector(4, "1110")), d_nm.mk_const(d_bv4_type)});
    ASSERT_EQ(bvurem_x1, d_rewriter.rewrite(bvurem_x1));
    Node bvurem_x2 = d_nm.mk_node(
        Kind::BV_UREM,
        {d_nm.mk_const(d_bv4_type), d_nm.mk_value(BitVector(4, "1110"))});
    ASSERT_EQ(bvurem_x2, d_rewriter.rewrite(bvurem_x2));
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
