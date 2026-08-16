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
#include <unordered_map>

#include "bitblast/aig/aig_cnf.h"
#include "bitblast/aig_bitblaster.h"
#include "test_lib.h"

namespace bzla::test {

static const char* s_binary_cadical = std::getenv("CADICAL");
static const char* s_binary_kissat  = std::getenv("KISSAT");

using ClauseList = std::vector<std::vector<int64_t>>;

class DummySatSolver : public bitblast::SatInterface
{
 public:
  int32_t new_var() override { return d_max_var++; }

  void add(int64_t lit, int64_t aig_id = 0) override
  {
    (void) aig_id;
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
  void add_clause(const std::initializer_list<int64_t>& literals,
                  int64_t aig_id = 0) override
  {
    (void) aig_id;
    for (auto lit : literals)
    {
      add(lit);
    }
    add(0);
  }

  bool value(int64_t lit) override
  {
    auto it = d_values.find(lit);
    return it == d_values.end() ? false : it->second;
  }

  /** Set the value the solver reports for `lit`. */
  void set_value(int64_t lit, bool value) { d_values[lit] = value; }

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
  std::unordered_map<int64_t, bool> d_values;
  int64_t d_max_var = 1;
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
    bitblast::AigManager aigmgr;
    bitblast::AigBitblaster bb;
    DummySatSolver solver;
    bitblast::AigCnfEncoder enc(solver);

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
    bitblast::AigManager aigmgr;
    bitblast::AigBitblaster bb;
    DummySatSolver solver;
    bitblast::AigCnfEncoder enc(solver);

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
    bitblast::AigManager aigmgr;
    bitblast::AigBitblaster bb;
    DummySatSolver solver;
    bitblast::AigCnfEncoder enc(solver);

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
  bitblast::AigCnfEncoder enc(solver);
}

TEST_F(TestAigCnf, enc_false)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode false_aig = aigmgr.mk_false();
  enc.encode(false_aig);
  ASSERT_EQ(solver.get_clauses().size(), 1);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{1}}));
}

TEST_F(TestAigCnf, enc_true)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode false_aig = aigmgr.mk_true();
  enc.encode(false_aig);
  ASSERT_EQ(solver.get_clauses().size(), 1);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{1}}));
}

TEST_F(TestAigCnf, enc_const)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode aig = aigmgr.mk_bit();
  enc.encode(aig);
  ASSERT_TRUE(solver.get_clauses().empty());
}

TEST_F(TestAigCnf, enc_and)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a       = aigmgr.mk_bit();
  bitblast::AigNode b       = aigmgr.mk_bit();
  bitblast::AigNode and_aig = aigmgr.mk_and(a, b);
  enc.encode(and_aig);
  ASSERT_EQ(
      solver.get_clauses(),
      ClauseList({{-enc.cnf_lit(and_aig), enc.cnf_lit(a)},
                  {-enc.cnf_lit(and_aig), enc.cnf_lit(b)},
                  {enc.cnf_lit(and_aig), -enc.cnf_lit(a), -enc.cnf_lit(b)}}));
}

TEST_F(TestAigCnf, enc_and_top)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a       = aigmgr.mk_bit();
  bitblast::AigNode b       = aigmgr.mk_bit();
  bitblast::AigNode and_aig = aigmgr.mk_and(a, b);
  enc.encode(and_aig, true);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{a.get_id()}, {b.get_id()}}));
}

TEST_F(TestAigCnf, enc_and_top2)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode d        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(c, d);
  bitblast::AigNode and_aig3 = aigmgr.mk_and(and_aig1, and_aig2);
  enc.encode(and_aig3, true);
  ASSERT_EQ(
      solver.get_clauses(),
      ClauseList({{a.get_id()}, {b.get_id()}, {c.get_id()}, {d.get_id()}}));
}

TEST_F(TestAigCnf, enc_or)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a      = aigmgr.mk_bit();
  bitblast::AigNode b      = aigmgr.mk_bit();
  bitblast::AigNode or_aig = aigmgr.mk_or(a, b);
  enc.encode(or_aig, false);
  auto or_id = enc.cnf_var(or_aig);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-or_id, -enc.cnf_lit(a)},
                        {-or_id, -enc.cnf_lit(b)},
                        {or_id, enc.cnf_lit(a), enc.cnf_lit(b)}}));
}

TEST_F(TestAigCnf, enc_or_top)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a      = aigmgr.mk_bit();
  bitblast::AigNode b      = aigmgr.mk_bit();
  bitblast::AigNode or_aig = aigmgr.mk_or(a, b);
  enc.encode(or_aig, true);
  ASSERT_EQ(solver.get_clauses(), ClauseList({{a.get_id(), b.get_id()}}));
}

TEST_F(TestAigCnf, enc_or_top2)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a       = aigmgr.mk_bit();
  bitblast::AigNode b       = aigmgr.mk_bit();
  bitblast::AigNode c       = aigmgr.mk_bit();
  bitblast::AigNode d       = aigmgr.mk_bit();
  bitblast::AigNode or_aig1 = aigmgr.mk_or(a, b);
  bitblast::AigNode or_aig2 = aigmgr.mk_or(c, d);
  bitblast::AigNode or_aig3 = aigmgr.mk_or(or_aig1, or_aig2);
  enc.encode(or_aig3, true);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{a.get_id(), b.get_id(), c.get_id(), d.get_id()}}));
}

TEST_F(TestAigCnf, enc_nary_and)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(and_aig1, c);
  // and_aig1 is only used by and_aig2, thus both are encoded as one n-ary AND
  enc.encode(and_aig2, false);
  auto x = enc.cnf_var(and_aig2);
  ASSERT_FALSE(enc.is_encoded(and_aig1));
  ASSERT_EQ(
      solver.get_clauses(),
      ClauseList({{-x, enc.cnf_lit(c)},
                  {-x, enc.cnf_lit(a)},
                  {-x, enc.cnf_lit(b)},
                  {x, -enc.cnf_lit(c), -enc.cnf_lit(a), -enc.cnf_lit(b)}}));
}

TEST_F(TestAigCnf, enc_nary_and_encode_merged)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(and_aig1, c);
  enc.encode(and_aig2, false);
  ASSERT_FALSE(enc.is_encoded(and_aig1));
  // A node that was merged into its parent still gets its own definition if
  // it is encoded later on, e.g., because it occurs as an assumption.
  enc.encode(and_aig1, false);
  ASSERT_TRUE(enc.is_encoded(and_aig1));
  auto x1      = enc.cnf_var(and_aig1);
  auto clauses = solver.get_clauses();
  ASSERT_EQ(clauses.size(), 7);
  ASSERT_EQ(clauses[4], std::vector<int64_t>({-x1, enc.cnf_lit(a)}));
  ASSERT_EQ(clauses[5], std::vector<int64_t>({-x1, enc.cnf_lit(b)}));
  ASSERT_EQ(clauses[6],
            std::vector<int64_t>({x1, -enc.cnf_lit(a), -enc.cnf_lit(b)}));
}

TEST_F(TestAigCnf, enc_nary_and_shared)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(and_aig1, c);
  bitblast::AigNode and_aig3 = aigmgr.mk_and(and_aig1, aigmgr.mk_not(c));
  // and_aig1 is shared, thus it is encoded separately
  enc.encode(and_aig2, false);
  enc.encode(and_aig3, false);
  ASSERT_TRUE(enc.is_encoded(and_aig1));
  auto x1 = enc.cnf_var(and_aig1);
  auto x2 = enc.cnf_var(and_aig2);
  auto x3 = enc.cnf_var(and_aig3);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-x1, enc.cnf_lit(a)},
                        {-x1, enc.cnf_lit(b)},
                        {x1, -enc.cnf_lit(a), -enc.cnf_lit(b)},
                        {-x2, enc.cnf_lit(c)},
                        {-x2, x1},
                        {x2, -enc.cnf_lit(c), -x1},
                        {-x3, -enc.cnf_lit(c)},
                        {-x3, x1},
                        {x3, enc.cnf_lit(c), -x1}}));
}

TEST_F(TestAigCnf, enc_require_cnf_var_and)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(and_aig1, c);
  // A node that requires a CNF variable is not merged into its parent, even
  // though it has a single parent, i.e., it is encoded exactly as it was before
  // n-ary AND merging.
  and_aig1.require_cnf_var();
  enc.encode(and_aig2, false);
  ASSERT_TRUE(enc.is_encoded(and_aig1));
  auto x1 = enc.cnf_var(and_aig1);
  auto x2 = enc.cnf_var(and_aig2);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-x1, enc.cnf_lit(a)},
                        {-x1, enc.cnf_lit(b)},
                        {x1, -enc.cnf_lit(a), -enc.cnf_lit(b)},
                        {-x2, enc.cnf_lit(c)},
                        {-x2, x1},
                        {x2, -enc.cnf_lit(c), -x1}}));
}

TEST_F(TestAigCnf, enc_require_cnf_var_or_top)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a      = aigmgr.mk_bit();
  bitblast::AigNode b      = aigmgr.mk_bit();
  bitblast::AigNode or_aig = aigmgr.mk_or(a, b);
  // A top-level OR that requires a CNF variable gets a variable and a unit
  // clause instead of being emitted as a single clause over its leafs (cf.
  // enc_or_top).
  or_aig.require_cnf_var();
  enc.encode(or_aig, true);
  ASSERT_TRUE(enc.is_encoded(or_aig));
  auto or_id = enc.cnf_var(or_aig);
  ASSERT_EQ(solver.get_clauses(),
            ClauseList({{-or_id, -enc.cnf_lit(a)},
                        {-or_id, -enc.cnf_lit(b)},
                        {or_id, enc.cnf_lit(a), enc.cnf_lit(b)},
                        {enc.cnf_lit(or_aig)}}));
}

TEST_F(TestAigCnf, enc_require_cnf_var_ite_inner)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode c   = aigmgr.mk_bit();
  bitblast::AigNode a   = aigmgr.mk_bit();
  bitblast::AigNode b   = aigmgr.mk_bit();
  bitblast::AigNode z   = aigmgr.mk_bit();
  bitblast::AigNode l   = aigmgr.mk_and(c, aigmgr.mk_not(a));
  bitblast::AigNode r   = aigmgr.mk_and(aigmgr.mk_not(c), aigmgr.mk_not(b));
  bitblast::AigNode ite = aigmgr.mk_and(aigmgr.mk_not(l), aigmgr.mk_not(r));
  // Extracting the ITE would drop both inner AND nodes, so an inner node that
  // requires a CNF variable refuses it. `ite` is then encoded as a plain AND,
  // and is merged into its parent rather than keeping a variable it no longer
  // needs.
  l.require_cnf_var();
  enc.encode(aigmgr.mk_and(ite, z), false);
  ASSERT_EQ(enc.statistics().num_ites, 0u);
  ASSERT_FALSE(enc.is_encoded(ite));
  ASSERT_TRUE(enc.is_encoded(l));
  ASSERT_TRUE(enc.is_encoded(r));
}

TEST_F(TestAigCnf, enc_ite_inner_cnf_var_not_required)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode c   = aigmgr.mk_bit();
  bitblast::AigNode a   = aigmgr.mk_bit();
  bitblast::AigNode b   = aigmgr.mk_bit();
  bitblast::AigNode z   = aigmgr.mk_bit();
  bitblast::AigNode ite = aigmgr.mk_and(
      aigmgr.mk_not(aigmgr.mk_and(c, aigmgr.mk_not(a))),
      aigmgr.mk_not(aigmgr.mk_and(aigmgr.mk_not(c), aigmgr.mk_not(b))));
  // Without the required CNF variable of enc_require_cnf_var_ite_inner the
  // very same AIG is extracted.
  enc.encode(aigmgr.mk_and(ite, z), false);
  ASSERT_EQ(enc.statistics().num_ites, 1u);
  ASSERT_TRUE(enc.is_encoded(ite));
}

TEST_F(TestAigCnf, value_merged)
{
  bitblast::BitInterface<bitblast::AigNode> aigmgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  bitblast::AigNode a        = aigmgr.mk_bit();
  bitblast::AigNode b        = aigmgr.mk_bit();
  bitblast::AigNode c        = aigmgr.mk_bit();
  bitblast::AigNode and_aig1 = aigmgr.mk_and(a, b);
  bitblast::AigNode and_aig2 = aigmgr.mk_and(and_aig1, c);
  enc.encode(and_aig2, false);
  ASSERT_FALSE(enc.is_encoded(and_aig1));

  // The value of a merged node is determined by its children.
  solver.set_value(enc.cnf_var(a), true);
  solver.set_value(enc.cnf_var(b), true);
  solver.set_value(enc.cnf_var(c), false);
  ASSERT_EQ(enc.value(and_aig1), 1);
  ASSERT_EQ(enc.value(aigmgr.mk_not(and_aig1)), -1);
  ASSERT_EQ(enc.value(and_aig2), -1);

  solver.set_value(enc.cnf_var(b), false);
  ASSERT_EQ(enc.value(and_aig1), -1);
  ASSERT_EQ(enc.value(aigmgr.mk_not(and_aig1)), 1);
}

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
