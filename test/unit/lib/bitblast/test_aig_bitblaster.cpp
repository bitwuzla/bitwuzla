/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <chrono>
#include <cstdlib>
#include <filesystem>

#include "bitblast/aig/aig_printer.h"
#include "bitblast/aig_bitblaster.h"
#include "test_lib.h"

static const char* s_solver_binary = std::getenv("SOLVER_BINARY");

namespace bzla::test {

namespace {
void
print_smt2(std::stringstream& ss, const bitblast::AigNode& n)
{
  bool negate = n.is_negated() && !n.is_true() && !n.is_false();
  if (negate)
  {
    ss << "(bvnot ";
  }
  if (n.is_false())
  {
    ss << "#b0";
  }
  else if (n.is_true())
  {
    ss << "#b1";
  }
  else if (n.is_const())
  {
    ss << "x" << std::labs(n.get_id());
  }
  else
  {
    assert(n.is_and());
    ss << "a" << std::labs(n.get_id());
  }
  if (negate)
  {
    ss << ")";
  }
}

void
print_smt2(std::stringstream& ss, const std::vector<bitblast::AigNode>& bits)
{
  std::vector<bitblast::AigNode> visit{bits.begin(), bits.end()};
  std::unordered_map<int64_t, bool> cache;

  do
  {
    bitblast::AigNode n = visit.back();
    visit.pop_back();
    int64_t id = std::labs(n.get_id());

    auto it = cache.find(id);
    if (it == cache.end())
    {
      cache.emplace(id, false);
      if (n.is_and())
      {
        visit.push_back(n);
        visit.push_back(n[0]);
        visit.push_back(n[1]);
      }
    }
    else if (!it->second)
    {
      it->second = true;
      if (n.is_and())
      {
        ss << "(define-fun a" << id << "() (_ BitVec 1) ";
        ss << "(bvand ";
        print_smt2(ss, n[0]);
        ss << " ";
        print_smt2(ss, n[1]);
        ss << ")";
        ss << ")\n";
      }
    }
  } while (!visit.empty());
}
}  // namespace

class TestAigBitblaster : public TestCommon
{
 public:
  static std::string check_sat(std::stringstream& ss)
  {
    std::stringstream bench;
    bench << "(set-logic QF_BV)\n";
    bench << "(set-option :produce-models true)\n";
    bench << ss.str();
    bench << "(check-sat)\n";
    bench << "(get-model)\n";

    char filename[] = "bzlabbtest-XXXXXX";
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
    pclose(fp);
    remove(filename);
    fclose(file);

    std::string result = output.str();
    size_t newline_pos = result.find_last_of('\n');
    return result.substr(0, newline_pos);
  }

  static void test_binary(const std::string& op,
                          const std::vector<bitblast::AigNode>& res,
                          const std::vector<bitblast::AigNode>& a,
                          const std::vector<bitblast::AigNode>& b)
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }
    std::stringstream ss;
    declare_const(ss, a);
    declare_const(ss, b);
    print_smt2(ss, res);
    define_const(ss, "a", a);
    define_const(ss, "b", b);
    define_const(ss, "res", res);
    ss << "(declare-const expected (_ BitVec " << res.size() << "))\n";
    ss << "(assert (= expected (" << op << " a b)))\n";
    ss << "(assert (distinct res expected))\n";
    ASSERT_EQ("unsat", check_sat(ss));
  }

  static void test_bv_mul_square(const std::vector<bitblast::AigNode>& res,
                                 const std::vector<bitblast::AigNode>& a)
  {
    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }
    std::stringstream ss;
    declare_const(ss, a);
    print_smt2(ss, res);
    define_const(ss, "a", a);
    define_const(ss, "res", res);
    ss << "(declare-const expected (_ BitVec " << res.size() << "))\n";
    ss << "(assert (= expected (bvmul a a)))\n";
    ss << "(assert (distinct res expected))\n";
    ASSERT_EQ("unsat", check_sat(ss));
  }
  static void declare_const(std::stringstream& ss,
                            const std::vector<bitblast::AigNode>& bits)
  {
    for (size_t i = 0; i < bits.size(); ++i)
    {
      ss << "(declare-const ";
      print_smt2(ss, bits[i]);
      ss << " (_ BitVec 1))\n";
    }
  }

  static void define_const(std::stringstream& ss,
                           const std::string& name,
                           const std::vector<bitblast::AigNode>& bits)
  {
    ss << "(declare-const " << name << " (_ BitVec " << bits.size() << "))\n";
    for (size_t i = 0; i < bits.size(); ++i)
    {
      size_t pos = bits.size() - 1 - i;
      ss << "(assert (= ((_ extract " << pos << " " << pos << ") " << name
         << ") ";
      print_smt2(ss, bits[i]);
      ss << "))\n";
    }
  }
};

#define TEST_BIN_OP(size, op, func)  \
  {                                  \
    bitblast::AigBitblaster bb;      \
    auto a   = bb.bv_constant(size); \
    auto b   = bb.bv_constant(size); \
    auto res = bb.func(a, b);        \
    test_binary(op, res, a, b);      \
  }

TEST_F(TestAigBitblaster, ctor_dtor) { bitblast::AigBitblaster bb; }

TEST_F(TestAigBitblaster, bv_value)
{
  BitVector zero = BitVector::from_ui(32, 0);
  BitVector ones = zero.bvnot();
  BitVector val  = BitVector::from_ui(32, 2863311530);  // 101010...

  bitblast::AigBitblaster bb;
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
  bitblast::AigBitblaster bb;

  auto bits = bb.bv_constant(12);
  ASSERT_EQ(bits.size(), 12);
}

TEST_F(TestAigBitblaster, bv_not)
{
  BitVector zero = BitVector::from_ui(32, 0);
  BitVector ones = zero.bvnot();

  bitblast::AigBitblaster bb;
  auto bb_zero  = bb.bv_value(zero);
  auto bb_ones  = bb.bv_value(ones);
  auto bb_const = bb.bv_constant(8);

  ASSERT_EQ(bb_zero, bb.bv_not(bb_ones));
  ASSERT_EQ(bb_ones, bb.bv_not(bb_zero));
  ASSERT_EQ(bb_const, bb.bv_not(bb.bv_not(bb_const)));
}

TEST_F(TestAigBitblaster, bv_and)
{
  bitblast::AigBitblaster bb;
  auto a      = bb.bv_constant(32);
  auto b      = bb.bv_constant(32);
  auto bb_and = bb.bv_and(a, b);

  ASSERT_EQ(bb_and.size(), a.size());
  ASSERT_EQ(bb_and, bb.bv_and(b, a));
  ASSERT_EQ(bb_and, bb.bv_not(bb.bv_not(bb_and)));
}

TEST_F(TestAigBitblaster, bv_and1) { TEST_BIN_OP(1, "bvand", bv_and); }

TEST_F(TestAigBitblaster, bv_and16) { TEST_BIN_OP(16, "bvand", bv_and); }

TEST_F(TestAigBitblaster, bv_and32) { TEST_BIN_OP(32, "bvand", bv_and); }

TEST_F(TestAigBitblaster, bv_or)
{
  bitblast::AigBitblaster bb;
  auto a     = bb.bv_constant(32);
  auto b     = bb.bv_constant(32);
  auto bb_or = bb.bv_or(a, b);

  ASSERT_EQ(bb_or.size(), a.size());
  ASSERT_EQ(bb_or, bb.bv_or(b, a));
  ASSERT_EQ(bb_or, bb.bv_not(bb.bv_not(bb_or)));
}

TEST_F(TestAigBitblaster, bv_or1) { TEST_BIN_OP(1, "bvor", bv_or); }

TEST_F(TestAigBitblaster, bv_or16) { TEST_BIN_OP(16, "bvor", bv_or); }

TEST_F(TestAigBitblaster, bv_or32) { TEST_BIN_OP(32, "bvor", bv_or); }

TEST_F(TestAigBitblaster, bv_shl1) { TEST_BIN_OP(1, "bvshl", bv_shl); }

TEST_F(TestAigBitblaster, bv_shl16) { TEST_BIN_OP(16, "bvshl", bv_shl); }

TEST_F(TestAigBitblaster, bv_shl32) { TEST_BIN_OP(32, "bvshl", bv_shl); }

TEST_F(TestAigBitblaster, bv_shr1) { TEST_BIN_OP(1, "bvlshr", bv_shr); }

TEST_F(TestAigBitblaster, bv_shr16) { TEST_BIN_OP(16, "bvlshr", bv_shr); }

TEST_F(TestAigBitblaster, bv_shr32) { TEST_BIN_OP(32, "bvlshr", bv_shr); }

TEST_F(TestAigBitblaster, bv_ashr1) { TEST_BIN_OP(1, "bvashr", bv_ashr); }

TEST_F(TestAigBitblaster, bv_ashr16) { TEST_BIN_OP(16, "bvashr", bv_ashr); }

TEST_F(TestAigBitblaster, bv_ashr32) { TEST_BIN_OP(32, "bvashr", bv_ashr); }

TEST_F(TestAigBitblaster, bv_extract)
{
  bitblast::AigBitblaster bb;

  auto a = bb.bv_constant(12);
  auto b = bb.bv_extract(a, 11, 0);
  ASSERT_EQ(a, b);
  for (size_t i = 0; i < a.size(); ++i)
  {
    auto bit = bb.bv_extract(a, i, i);
    ASSERT_EQ(bit[0], a[a.size() - 1 - i]);
  }
  b = bb.bv_extract(a, 6, 0);
  ASSERT_EQ(b.size(), 7);
}

TEST_F(TestAigBitblaster, bv_concat)
{
  bitblast::AigBitblaster bb;
  auto a         = bb.bv_constant(8);
  auto b         = bb.bv_constant(24);
  auto bb_concat = bb.bv_concat(a, b);

  ASSERT_EQ(a.size() + b.size(), bb_concat.size());
  ASSERT_EQ(bb.bv_extract(bb_concat, 31, 24), a);
  ASSERT_EQ(bb.bv_extract(bb_concat, 23, 0), b);
}

TEST_F(TestAigBitblaster, bv_eq)
{
  bitblast::AigBitblaster bb;
  auto a     = bb.bv_constant(32);
  auto b     = bb.bv_constant(32);
  auto bb_eq = bb.bv_eq(a, b);

  ASSERT_EQ(bb_eq, bb.bv_eq(b, a));
}

TEST_F(TestAigBitblaster, bv_eq1) { TEST_BIN_OP(1, "=", bv_eq); }

TEST_F(TestAigBitblaster, bv_eq16) { TEST_BIN_OP(16, "=", bv_eq); }

TEST_F(TestAigBitblaster, bv_eq32) { TEST_BIN_OP(32, "=", bv_eq); }

TEST_F(TestAigBitblaster, bv_ult1) { TEST_BIN_OP(1, "bvult", bv_ult); }

TEST_F(TestAigBitblaster, bv_ult16) { TEST_BIN_OP(16, "bvult", bv_ult); }

TEST_F(TestAigBitblaster, bv_ult32) { TEST_BIN_OP(32, "bvult", bv_ult); }

TEST_F(TestAigBitblaster, bv_slt1) { TEST_BIN_OP(1, "bvslt", bv_slt); }

TEST_F(TestAigBitblaster, bv_slt16) { TEST_BIN_OP(16, "bvslt", bv_slt); }

TEST_F(TestAigBitblaster, bv_slt32) { TEST_BIN_OP(32, "bvslt", bv_slt); }

TEST_F(TestAigBitblaster, bv_add)
{
  bitblast::AigBitblaster bb;
  auto a      = bb.bv_constant(32);
  auto b      = bb.bv_constant(32);
  auto bb_add = bb.bv_add(a, b);

  ASSERT_EQ(bb_add, bb.bv_add(b, a));
}

TEST_F(TestAigBitblaster, bv_add1) { TEST_BIN_OP(1, "bvadd", bv_add); }

TEST_F(TestAigBitblaster, bv_add16) { TEST_BIN_OP(16, "bvadd", bv_add); }

TEST_F(TestAigBitblaster, bv_add32) { TEST_BIN_OP(32, "bvadd", bv_add); }

TEST_F(TestAigBitblaster, bv_mul)
{
  bitblast::AigBitblaster bb;
  auto a      = bb.bv_constant(32);
  auto b      = bb.bv_constant(32);
  auto bb_mul = bb.bv_mul(a, b);

  //ASSERT_EQ(bb_mul, bb.bv_mul(b, a));
}

TEST_F(TestAigBitblaster, bv_mul1) { TEST_BIN_OP(1, "bvmul", bv_mul); }

TEST_F(TestAigBitblaster, bv_mul2) { TEST_BIN_OP(2, "bvmul", bv_mul); }

TEST_F(TestAigBitblaster, bv_mul3) { TEST_BIN_OP(3, "bvmul", bv_mul); }

TEST_F(TestAigBitblaster, bv_mul4) { TEST_BIN_OP(4, "bvmul", bv_mul); }

TEST_F(TestAigBitblaster, bv_mul8) { TEST_BIN_OP(8, "bvmul", bv_mul); }

TEST_F(TestAigBitblaster, bv_mul_square)
{
  for (size_t i = 1; i < 17; ++i)
  {
    bitblast::AigBitblaster bb;
    auto a   = bb.bv_constant(i);
    auto res = bb.bv_mul_square(a);
    test_bv_mul_square(res, a);
  }
}

TEST_F(TestAigBitblaster, bv_udiv)
{
  bitblast::AigBitblaster bb;
  auto a       = bb.bv_constant(32);
  auto b       = bb.bv_constant(32);
  auto bb_udiv = bb.bv_udiv(a, b);
}

TEST_F(TestAigBitblaster, bv_udiv1) { TEST_BIN_OP(1, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv2) { TEST_BIN_OP(2, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv3) { TEST_BIN_OP(3, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv4) { TEST_BIN_OP(4, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv8) { TEST_BIN_OP(8, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv9) { TEST_BIN_OP(9, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_udiv10) { TEST_BIN_OP(10, "bvudiv", bv_udiv); }

TEST_F(TestAigBitblaster, bv_urem)
{
  bitblast::AigBitblaster bb;
  auto a       = bb.bv_constant(32);
  auto b       = bb.bv_constant(32);
  auto bb_urem = bb.bv_urem(a, b);
}

TEST_F(TestAigBitblaster, bv_urem1) { TEST_BIN_OP(1, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem2) { TEST_BIN_OP(2, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem3) { TEST_BIN_OP(3, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem4) { TEST_BIN_OP(4, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem8) { TEST_BIN_OP(8, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem9) { TEST_BIN_OP(9, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_urem10) { TEST_BIN_OP(10, "bvurem", bv_urem); }

TEST_F(TestAigBitblaster, bv_ite) {
  bitblast::AigBitblaster bb;
  auto a      = bb.bv_constant(32);
  auto b      = bb.bv_constant(32);
  auto c      = bb.bv_constant(1);
  auto bb_ite = bb.bv_ite(c[0], a, b);

    if (s_solver_binary == nullptr)
    {
      GTEST_SKIP_("SOLVER_BINARY environment variable not set.");
    }
    std::stringstream ss;
    declare_const(ss, a);
    declare_const(ss, b);
    declare_const(ss, c);
    print_smt2(ss, bb_ite);
    define_const(ss, "a", a);
    define_const(ss, "b", b);
    define_const(ss, "c", c);
    define_const(ss, "res", bb_ite);
    ss << "(assert (distinct res (ite c a b)))\n";
    ASSERT_EQ("unsat", check_sat(ss));
}

#if 0
TEST_F(TestAigBitblaster, bv_udiv1024)
{
  std::chrono::system_clock::time_point stop_before_cleanup;
  auto start = std::chrono::high_resolution_clock::now();
  {
    bitblast::AigBitblaster bb;
    auto a              = bb.bv_constant(1024);
    auto b              = bb.bv_constant(1024);
    auto bb_udiv        = bb.bv_udiv(a, b);
    stop_before_cleanup = std::chrono::high_resolution_clock::now();
  }
  auto stop        = std::chrono::high_resolution_clock::now();
  auto constr_time = std::chrono::duration_cast<std::chrono::microseconds>(
                         stop_before_cleanup - start)
                         .count();
  auto total_time =
      std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
          .count();
  std::cout << "construction time: " << constr_time << std::endl;
  std::cout << "cleanup time:      " << total_time - constr_time << std::endl;
}

TEST_F(TestAigBitblaster, bv_add1024)
{
  std::chrono::system_clock::time_point stop_before_cleanup;
  auto start = std::chrono::high_resolution_clock::now();
  {
    bitblast::AigBitblaster bb;
    auto a              = bb.bv_constant(1024);
    auto b              = bb.bv_constant(1024);
    auto bb_udiv        = bb.bv_add(a, b);
    stop_before_cleanup = std::chrono::high_resolution_clock::now();
  }
  auto stop        = std::chrono::high_resolution_clock::now();
  auto constr_time = std::chrono::duration_cast<std::chrono::microseconds>(
                         stop_before_cleanup - start)
                         .count();
  auto total_time =
      std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
          .count();
  std::cout << "construction time: " << constr_time << std::endl;
  std::cout << "cleanup time:      " << total_time - constr_time << std::endl;
}

TEST_F(TestAigBitblaster, bv_mul1024)
{
  std::chrono::system_clock::time_point stop_before_cleanup;
  auto start = std::chrono::high_resolution_clock::now();
  {
    bitblast::AigBitblaster bb;
    auto a              = bb.bv_constant(1024);
    auto b              = bb.bv_constant(1024);
    auto bb_udiv        = bb.bv_mul(a, b);
    stop_before_cleanup = std::chrono::high_resolution_clock::now();
  }
  auto stop        = std::chrono::high_resolution_clock::now();
  auto constr_time = std::chrono::duration_cast<std::chrono::microseconds>(
                         stop_before_cleanup - start)
                         .count();
  auto total_time =
      std::chrono::duration_cast<std::chrono::microseconds>(stop - start)
          .count();
  std::cout << "construction time: " << constr_time << std::endl;
  std::cout << "cleanup time:      " << total_time - constr_time << std::endl;
}

// TEST_F(TestAigBitblaster, bv_muludiv1024)
//{
//   std::chrono::system_clock::time_point stop_before_cleanup;
//   auto start = std::chrono::high_resolution_clock::now();
//   {
//   bitblast::AigBitblaster bb;
//   auto a       = bb.bv_constant(1024);
//   auto b       = bb.bv_constant(1024);
//   auto bb_udiv = bb.bv_udiv(a, b);
//   auto bb_mul = bb.bv_mul(a, b);
//   stop_before_cleanup = std::chrono::high_resolution_clock::now();
//   }
//   auto stop = std::chrono::high_resolution_clock::now();
//   auto constr_time =
//   std::chrono::duration_cast<std::chrono::microseconds>(stop_before_cleanup -
//   start).count(); auto total_time =
//   std::chrono::duration_cast<std::chrono::microseconds>(stop -
//   start).count(); std::cout << "construction time: " << constr_time <<
//   std::endl; std::cout << "cleanup time:      " << total_time - constr_time
//   << std::endl;
// }
//
// TEST_F(TestAigBitblaster, bv_udivudiv1024)
//{
//   std::chrono::system_clock::time_point stop_before_cleanup;
//   auto start = std::chrono::high_resolution_clock::now();
//   {
//   bitblast::AigBitblaster bb;
//   auto a       = bb.bv_constant(1024);
//   auto b       = bb.bv_constant(1024);
//   auto bb_udiv = bb.bv_udiv(a, b);
//   auto bb_mul = bb.bv_udiv(a, b);
//   stop_before_cleanup = std::chrono::high_resolution_clock::now();
//   }
//   auto stop = std::chrono::high_resolution_clock::now();
//   auto constr_time =
//   std::chrono::duration_cast<std::chrono::microseconds>(stop_before_cleanup -
//   start).count(); auto total_time =
//   std::chrono::duration_cast<std::chrono::microseconds>(stop -
//   start).count(); std::cout << "construction time: " << constr_time <<
//   std::endl; std::cout << "cleanup time:      " << total_time - constr_time
//   << std::endl;
// }
#endif
}  // namespace bzla::test
