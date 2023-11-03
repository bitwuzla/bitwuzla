/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <iostream>

#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig_bitblaster.h"
#include "test_lib.h"

namespace bzla::test {

static const char* s_binary_cadical = std::getenv("CADICAL");
static const char* s_binary_kissat  = std::getenv("KISSAT");

using ClauseList = std::vector<std::vector<int64_t>>;

class DummySatSolver : public bb::SatInterface
{
 public:
  void add(int64_t lit) override
  {
    if (std::abs(lit) > d_max_var)
    {
      d_max_var = std::abs(lit);
    }
    // std::cout << lit << ((lit == 0) ? "\n" : " ");
    if (lit == 0)
    {
      d_clauses.emplace_back(d_clause);
      d_clause.clear();
    }
    else
    {
      d_clause.push_back(lit);
    }
  }
  void add_clause(const std::initializer_list<int64_t>& literals) override
  {
    for (auto lit : literals)
    {
      add(lit);
    }
    add(0);
  }

  bool value(int64_t lit) override
  {
    (void) lit;
    return false;
  }

  std::string to_dimacs() const
  {
    std::stringstream ss;

    ss << "p cnf " << d_max_var << " " << d_clauses.size() << "\n";
    std::cout << ss.str() << std::flush;
    for (auto& clause : d_clauses)
    {
      for (auto lit : clause)
      {
        ss << lit << " ";
      }
      ss << "0\n";
    }

    return ss.str();
  }

  std::vector<std::vector<int64_t>>& get_clauses() { return d_clauses; }

 private:
  int64_t d_max_var = 0;
  std::vector<int64_t> d_clause;
  ClauseList d_clauses;
};

class TestAigCnf : public TestCommon
{
 public:
  static std::string check_sat(const std::string& cnf,
                               const std::string& sat_solver)
  {
    char filename[] = "bzlacnftest-XXXXXX";
    int fd          = mkstemp(filename);
    assert(fd != -1);

    FILE* file = fdopen(fd, "w");
    fputs(cnf.c_str(), file);
    fflush(file);

    std::stringstream cmd;
    cmd << sat_solver << " " << filename;

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

    std::string line;
    while(std::getline(output, line))
    {
      if (!line.empty() && line[0] == 's')
      {
        if (line == "s SATISFIABLE")
        {
          return "sat";
        }
        else if (line == "s UNSATISFIABLE")
        {
          return "unsat";
        }
      }
    }
    return "unknown";
  }

  // a * -1 != ~a + 1
  static std::string perf_test1(size_t bw)
  {
    bb::AigManager aigmgr;
    bb::AigBitblaster bb;
    DummySatSolver solver;
    bb::AigCnfEncoder enc(solver);

    auto a       = bb.bv_constant(bw);
    auto one     = bb.bv_value(BitVector(bw, "1", 10));
    auto neg_one = bb.bv_value(BitVector(bw, "-1", 10));

    auto neg_a1 = bb.bv_mul(a, neg_one);
    auto not_a  = bb.bv_not(a);
    auto neg_a2 = bb.bv_add(not_a, one);

    auto neq = bb.bv_not(bb.bv_eq(neg_a1, neg_a2));

    enc.encode(neq[0], true);
    return solver.to_dimacs();
  }

  // a + b + c != c + b + a
  static std::string perf_test2(size_t bw)
  {
    bb::AigManager aigmgr;
    bb::AigBitblaster bb;
    DummySatSolver solver;
    bb::AigCnfEncoder enc(solver);

    auto a = bb.bv_constant(bw);
    auto b = bb.bv_constant(bw);
    auto c = bb.bv_constant(bw);

    auto a_add_b = bb.bv_add(a, b);
    auto add_c   = bb.bv_add(a_add_b, c);

    auto c_add_b = bb.bv_add(c, b);
    auto add_a   = bb.bv_add(c_add_b, a);

    auto neq = bb.bv_not(bb.bv_eq(add_c, add_a));

    enc.encode(neq[0], true);
    return solver.to_dimacs();
  }

  // x * (a + b) != x * a + x * b
  static std::string perf_test3(size_t bw)
  {
    bb::AigManager aigmgr;
    bb::AigBitblaster bb;
    DummySatSolver solver;
    bb::AigCnfEncoder enc(solver);

    auto a = bb.bv_constant(bw);
    auto b = bb.bv_constant(bw);
    auto x = bb.bv_constant(bw);

    auto a_add_b = bb.bv_add(a, b);
    auto mul     = bb.bv_mul(x, a_add_b);

    auto x_mul_a = bb.bv_mul(x, a);
    auto x_mul_b = bb.bv_mul(x, b);
    auto add     = bb.bv_add(x_mul_a, x_mul_b);

    auto neq = bb.bv_not(bb.bv_eq(mul, add));

    enc.encode(neq[0], true);
    return solver.to_dimacs();
  }
};

TEST_F(TestAigCnf, ctor_dtor)
{
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);
}

TEST_F(TestAigCnf, enc_false)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode false_aig = aigmgr.mk_false();
  enc.encode(false_aig);
  ASSERT_EQ(solver.get_clauses().size(), 1);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{1}}));
}

TEST_F(TestAigCnf, enc_true)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode false_aig = aigmgr.mk_true();
  enc.encode(false_aig);
  ASSERT_EQ(solver.get_clauses().size(), 1);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{1}}));
}

TEST_F(TestAigCnf, enc_const)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode aig = aigmgr.mk_bit();
  enc.encode(aig);
  ASSERT_TRUE(solver.get_clauses().empty());
}

TEST_F(TestAigCnf, enc_and)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a       = aigmgr.mk_bit();
  bb::AigNode b       = aigmgr.mk_bit();
  bb::AigNode and_aig = aigmgr.mk_and(a, b);
  enc.encode(and_aig);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-and_aig.get_id(), a.get_id()},
                        {-and_aig.get_id(), b.get_id()},
                        {and_aig.get_id(), -a.get_id(), -b.get_id()}}));
}

TEST_F(TestAigCnf, enc_and_top)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a       = aigmgr.mk_bit();
  bb::AigNode b       = aigmgr.mk_bit();
  bb::AigNode and_aig = aigmgr.mk_and(a, b);
  enc.encode(and_aig, true);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{a.get_id()}, {b.get_id()}}));
}

TEST_F(TestAigCnf, enc_and_top2)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a        = aigmgr.mk_bit();
  bb::AigNode b        = aigmgr.mk_bit();
  bb::AigNode c        = aigmgr.mk_bit();
  bb::AigNode d        = aigmgr.mk_bit();
  bb::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bb::AigNode and_aig2 = aigmgr.mk_and(c, d);
  bb::AigNode and_aig3 = aigmgr.mk_and(and_aig1, and_aig2);
  enc.encode(and_aig3, true);
  ASSERT_EQ(
      solver.get_clauses(),
      ClauseList({{a.get_id()}, {b.get_id()}, {c.get_id()}, {d.get_id()}}));
}

TEST_F(TestAigCnf, enc_or)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a      = aigmgr.mk_bit();
  bb::AigNode b      = aigmgr.mk_bit();
  bb::AigNode or_aig = aigmgr.mk_or(a, b);
  auto or_id         = std::abs(or_aig.get_id());
  enc.encode(or_aig, false);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-or_id, -a.get_id()},
                        {-or_id, -b.get_id()},
                        {or_id, a.get_id(), b.get_id()}}));
}

#if 0
TEST_F(TestAigCnf, enc_or_top)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a      = aigmgr.mk_bit();
  bb::AigNode b      = aigmgr.mk_bit();
  bb::AigNode or_aig = aigmgr.mk_or(a, b);
  enc.encode(or_aig, true);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{a.get_id(), b.get_id()}}));
}

TEST_F(TestAigCnf, enc_or_top2)
{
  bb::AigManager aigmgr;
  DummySatSolver solver;
  bb::AigCnfEncoder enc(solver);

  bb::AigNode a       = aigmgr.mk_bit();
  bb::AigNode b       = aigmgr.mk_bit();
  bb::AigNode c       = aigmgr.mk_bit();
  bb::AigNode d       = aigmgr.mk_bit();
  bb::AigNode or_aig1 = aigmgr.mk_or(a, b);
  bb::AigNode or_aig2 = aigmgr.mk_or(c, d);
  bb::AigNode or_aig3 = aigmgr.mk_or(or_aig1, or_aig2);
  enc.encode(or_aig3, true);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{a.get_id(), b.get_id(), c.get_id(), d.get_id()}}));
}
#endif

TEST_F(TestAigCnf, perf1_cadical)
{
  if (s_binary_cadical == nullptr)
  {
    GTEST_SKIP_("CADICAL environment variable not set.");
  }
  auto res = check_sat(perf_test1(17), s_binary_cadical);
  ASSERT_EQ(res, "unsat");
}

TEST_F(TestAigCnf, perf2_cadical)
{
  if (s_binary_cadical == nullptr)
  {
    GTEST_SKIP_("CADICAL environment variable not set.");
  }
  auto res = check_sat(perf_test2(8), s_binary_cadical);
  ASSERT_EQ(res, "unsat");
}

TEST_F(TestAigCnf, perf3_cadical)
{
  if (s_binary_cadical == nullptr)
  {
    GTEST_SKIP_("CADICAL environment variable not set.");
  }
  auto res = check_sat(perf_test3(8), s_binary_cadical);
  ASSERT_EQ(res, "unsat");
}

TEST_F(TestAigCnf, perf1_kissat)
{
  if (s_binary_kissat == nullptr)
  {
    GTEST_SKIP_("KISSAT environment variable not set.");
  }
  auto res = check_sat(perf_test1(17), s_binary_kissat);
  ASSERT_EQ(res, "unsat");
}

TEST_F(TestAigCnf, perf2_kissat)
{
  if (s_binary_kissat == nullptr)
  {
    GTEST_SKIP_("KISSAT environment variable not set.");
  }
  auto res = check_sat(perf_test2(8), s_binary_kissat);
  ASSERT_EQ(res, "unsat");
}

TEST_F(TestAigCnf, perf3_kissat)
{
  if (s_binary_kissat == nullptr)
  {
    GTEST_SKIP_("KISSAT environment variable not set.");
  }
  auto res = check_sat(perf_test3(8), s_binary_kissat);
  ASSERT_EQ(res, "unsat");
}

}  // namespace bzla::test
