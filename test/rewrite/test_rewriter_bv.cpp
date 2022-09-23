#include "bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "rewrite/rewriter.h"
#include "solver/fp/floating_point.h"

namespace bzla::test {

static const char* s_solver_binary = std::getenv("SOLVER_BINARY");

using namespace bzla::node;

class TestRewriter : public ::testing::Test
{
  void SetUp() override { d_bv_type = d_nm.mk_bv_type(4); }

 protected:
  static std::string check_sat(std::stringstream& ss)
  {
    std::stringstream bench;
    bench << "(set-logic QF_BV)\n";
    bench << "(set-option :produce-models true)\n";
    bench << ss.str();
    bench << "(check-sat)\n";
    bench << "(get-model)\n";

    char filename[] = "bzlarwtest-XXXXXX";
    int fd          = mkstemp(filename);
    assert(fd != -1);

    FILE* file = fdopen(fd, "w");
    fputs(bench.str().c_str(), file);
    fflush(file);

    std::stringstream cmd;
    cmd << s_solver_binary << " " << filename;

    // Execute solver and read output.
    FILE* fp = popen(cmd.str().c_str(), "r");
    char buf[1024];
    std::stringstream output;
    while (fgets(buf, 1024, fp))
    {
      output << buf;
    }
    remove(filename);
    fclose(file);

    std::string result = output.str();
    size_t newline_pos = result.find_last_of('\n');
    return result.substr(0, newline_pos);
  }

  void test_elim_rule(Kind kind)
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }

    size_t num_children = s_node_kind_info[kind].num_children;
    size_t num_indices  = s_node_kind_info[kind].num_indices;

    NodeManager& nm = NodeManager::get();
    Type bv8        = nm.mk_bv_type(8);
    std::vector<Node> children;
    std::vector<uint64_t> indices;
    if (num_children >= 1)
    {
      children.push_back(nm.mk_const(bv8, "a"));
    }
    if (num_children >= 2)
    {
      children.push_back(nm.mk_const(bv8, "b"));
    }

    if (num_indices == 1)
    {
      indices.push_back(7);
    }
    if (num_indices == 2)
    {
      indices.push_back(1);
    }

    Node node = nm.mk_node(kind, children, indices);

    std::stringstream ss;
    for (const Node& child : children)
    {
      ss << "(declare-const " << child << " " << child.type() << ")\n";
    }
    ss << "(assert (distinct " << node << " " << d_rewriter.rewrite(node)
       << "))\n";
    ASSERT_EQ(check_sat(ss), "unsat");
  }

  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Type d_bv_type;
};

/* bvadd -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_add_eval)
{
  // applies
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
  // does not apply
  Node bvadd2 = d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd2, d_rewriter.rewrite(bvadd2));
  Node bvadd3 =
      d_nm.mk_node(Kind::BV_ADD, {bvadd2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvadd3, d_rewriter.rewrite(bvadd3));
}

/* bvand -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_and_eval)
{
  // applies
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
  // does not apply
  Node bvand2 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand2, d_rewriter.rewrite(bvand2));
  Node bvand3 =
      d_nm.mk_node(Kind::BV_AND, {bvand2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand3, d_rewriter.rewrite(bvand3));
}

/* bvashr ------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_ashr_eval)
{
  // applies
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
  // does not apply
  Node bvashr2 = d_nm.mk_node(
      Kind::BV_ASHR,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvashr2, d_rewriter.rewrite(bvashr2));
  Node bvashr3 = d_nm.mk_node(Kind::BV_ASHR,
                              {bvashr2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvashr3, d_rewriter.rewrite(bvashr3));
}

/* bvconcat ----------------------------------------------------------------- */

TEST_F(TestRewriter, bv_concat_eval)
{
  // applies
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
  // does not apply
  Node bvconcat2 = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat2, d_rewriter.rewrite(bvconcat2));
  Node bvconcat3 = d_nm.mk_node(
      Kind::BV_CONCAT, {bvconcat2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvconcat3, d_rewriter.rewrite(bvconcat3));
}

/* bvmul -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_mul_eval)
{
  // applies
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
  // does not apply
  Node bvmul2 = d_nm.mk_node(
      Kind::BV_MUL,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul2, d_rewriter.rewrite(bvmul2));
  Node bvmul3 =
      d_nm.mk_node(Kind::BV_MUL, {bvmul2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvmul3, d_rewriter.rewrite(bvmul3));
}

/* bvshl -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_shl_eval)
{
  // applies
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
  // does not apply
  Node bvshl2 = d_nm.mk_node(
      Kind::BV_SHL,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshl2, d_rewriter.rewrite(bvshl2));
  Node bvshl3 =
      d_nm.mk_node(Kind::BV_SHL, {bvshl2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshl3, d_rewriter.rewrite(bvshl3));
}

/* bvshr -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_shr_eval)
{
  // applies
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
  // does not apply
  Node bvshr2 = d_nm.mk_node(
      Kind::BV_SHR,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(bvshr2, d_rewriter.rewrite(bvshr2));
  Node bvshr3 =
      d_nm.mk_node(Kind::BV_SHR, {bvshr2, d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(bvshr3, d_rewriter.rewrite(bvshr3));
}

/* bvslt -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_slt_eval)
{
  // applies
  Node bvslt0 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(bvslt0));
  Node bvslt1 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "0001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(bvslt1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(bvslt1));
  // does not apply
  Node bvslt2 = d_nm.mk_node(
      Kind::BV_SLT,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvslt2, d_rewriter.rewrite(bvslt2));
}

/* bvudiv-------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_udiv_eval)
{
  // applies
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
  // does not apply
  Node bvudiv2 = d_nm.mk_node(
      Kind::BV_UDIV,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv2, d_rewriter.rewrite(bvudiv2));
  Node bvudiv3 = d_nm.mk_node(Kind::BV_UDIV,
                              {bvudiv2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvudiv3, d_rewriter.rewrite(bvudiv3));
}

/* bvult -------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_ult_eval)
{
  // applies
  Node bvult0 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(bvult0));
  Node bvult1 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1110")),
                              d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(bvult1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(bvult1));
  // does not apply
  Node bvult2 = d_nm.mk_node(
      Kind::BV_ULT,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvult2, d_rewriter.rewrite(bvult2));
}

/* bvudiv-------------------------------------------------------------------- */

TEST_F(TestRewriter, bv_urem_eval)
{
  // applies
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
  // does not apply
  Node bvurem2 = d_nm.mk_node(
      Kind::BV_UREM,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem2, d_rewriter.rewrite(bvurem2));
  Node bvurem3 = d_nm.mk_node(Kind::BV_UREM,
                              {bvurem2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvurem3, d_rewriter.rewrite(bvurem3));
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
