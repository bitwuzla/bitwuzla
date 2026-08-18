/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <algorithm>
#include <array>
#include <functional>
#include <iostream>
#include <map>
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

/* -------------------------------------------------------------------------
 * Variant invariance
 *
 * The CNF the encoder emits has to depend on the function an AIG node computes,
 * not on which variant of it the input builds. The helpers below build a single
 * AIG node from a lambda and encode it in isolation, so that no node has more
 * than one parent and neither the ITE sharing guard nor a required CNF
 * variable interferes.
 * ------------------------------------------------------------------------- */
namespace {

using Mgr    = bitblast::BitInterface<bitblast::AigNode>;
using Aig    = bitblast::AigNode;
using Leaves = std::vector<Aig>;
/** Builds a single AIG node out of a number of fresh AIG constants. */
using Build = std::function<Aig(Mgr&, const Leaves&)>;

/** The observable size of the CNF produced for a single encoded AIG node. */
struct EncSize
{
  uint64_t vars = 0, clauses = 0, ites = 0, xors = 0, merged = 0;

  bool operator==(const EncSize& o) const
  {
    return vars == o.vars && clauses == o.clauses && ites == o.ites
           && xors == o.xors && merged == o.merged;
  }

  std::string str() const
  {
    std::stringstream ss;
    ss << "vars=" << vars << " clauses=" << clauses << " ites=" << ites
       << " xors=" << xors << " merged=" << merged;
    return ss.str();
  }
};

/** Everything the invariance and equivalence checks need about one variant. */
struct Encoded
{
  EncSize size;
  ClauseList clauses;
  /** CNF literal of the encoded root, 0 if the root needs no variable. */
  int64_t root_lit = 0;
  /** CNF literal per leaf, 0 if the leaf does not occur in the CNF. */
  std::vector<int64_t> leaf_lits;
  int64_t max_var = 0;
  /** Truth table of the root over the leaves, bit i = leaf assignment i. */
  uint32_t truth_table = 0;
  /** Whether the root collapsed to a constant / a leaf during rewriting. */
  bool root_is_and = false;
  /** Whether the root has the two-level shape is_ite() inspects. */
  bool two_level = false;
};

/** Evaluate an AIG node under an assignment of its leaves. */
bool
eval_aig(const Aig& n, const std::map<int64_t, bool>& env)
{
  int64_t id = std::abs(n.get_id());
  bool v;
  auto it = env.find(id);
  if (it != env.end())
  {
    v = it->second;
  }
  else if (n.is_and())
  {
    v = eval_aig(n[0], env) && eval_aig(n[1], env);
  }
  else
  {
    // The true/false node. Every leaf the builder was handed is bound in
    // `env`, so this is the only remaining case.
    v = true;
  }
  return n.is_negated() ? !v : v;
}

/** Build `build` over `nleaves` fresh AIG bits and encode it on its own. */
Encoded
encode_isolated(size_t nleaves, const Build& build)
{
  Mgr mgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  Leaves leaves;
  for (size_t i = 0; i < nleaves; ++i)
  {
    leaves.push_back(mgr.mk_bit());
  }
  assert(nleaves <= 5);  // `truth_table` below is 32 bits wide
  Aig root = build(mgr, leaves);
  enc.encode(root, false);

  Encoded res;
  const auto& st = enc.statistics();
  res.size       = {
      st.num_vars, st.num_clauses, st.num_ites, st.num_xors, st.num_merged};
  res.clauses     = solver.get_clauses();
  res.root_is_and = root.is_and();
  res.two_level   = root.is_and() && root[0].is_and() && root[0].is_negated()
                    && root[1].is_and() && root[1].is_negated();
  res.root_lit    = enc.is_encoded(root) ? enc.cnf_lit(root) : 0;
  for (const auto& c : res.clauses)
  {
    for (int64_t l : c)
    {
      res.max_var = std::max(res.max_var, std::abs(l));
    }
  }
  for (const Aig& l : leaves)
  {
    res.leaf_lits.push_back(enc.is_encoded(l) ? enc.cnf_lit(l) : 0);
  }
  for (uint32_t i = 0; i < (1u << nleaves); ++i)
  {
    std::map<int64_t, bool> env;
    for (size_t b = 0; b < nleaves; ++b)
    {
      env[std::abs(leaves[b].get_id())] = ((i >> b) & 1) != 0;
    }
    if (eval_aig(root, env)) res.truth_table |= 1u << i;
  }
  return res;
}

/**
 * Brute-force check that the emitted CNF really defines the root: for every
 * assignment of the leaf variables the CNF must be satisfiable with the root
 * literal true exactly when the AIG evaluates to true, and false exactly when
 * it evaluates to false. Catches a polarity error in an extracted gate, which
 * comparing clause counts cannot.
 */
bool
cnf_defines_root(const Encoded& e, size_t nleaves, std::string& err)
{
  if (e.root_lit == 0)
  {
    err = "root has no CNF variable";
    return false;
  }
  if (e.max_var > 20)
  {
    err = "too many CNF variables for brute force";
    return false;
  }
  // Leaves that do not occur in the CNF are don't-cares: any value of the
  // corresponding truth table index is consistent with the encoding.
  uint32_t dontcare = 0;
  for (size_t b = 0; b < nleaves; ++b)
  {
    if (e.leaf_lits[b] == 0) dontcare |= 1u << b;
  }
  // reachable[i] & 1: root can be true under leaf assignment i
  // reachable[i] & 2: root can be false under leaf assignment i
  std::vector<uint8_t> reachable(1u << nleaves, 0);
  uint64_t nassign = 1ull << e.max_var;
  for (uint64_t m = 0; m < nassign; ++m)
  {
    auto val = [&](int64_t lit) {
      bool v = ((m >> (std::abs(lit) - 1)) & 1) != 0;
      return lit < 0 ? !v : v;
    };
    bool sat = true;
    for (const auto& c : e.clauses)
    {
      bool cl = false;
      for (int64_t l : c)
      {
        if (val(l))
        {
          cl = true;
          break;
        }
      }
      if (!cl)
      {
        sat = false;
        break;
      }
    }
    if (!sat) continue;
    uint32_t idx = 0;
    for (size_t b = 0; b < nleaves; ++b)
    {
      if (e.leaf_lits[b] != 0 && val(e.leaf_lits[b])) idx |= 1u << b;
    }
    uint8_t bit = val(e.root_lit) ? 1 : 2;
    // Mark every truth table index that agrees with `idx` on the leaves that
    // actually occur in the CNF.
    for (uint32_t d = 0; d < (1u << nleaves); ++d)
    {
      if ((d & ~dontcare) == idx) reachable[d] |= bit;
    }
  }
  for (uint32_t i = 0; i < (1u << nleaves); ++i)
  {
    uint8_t want = ((e.truth_table >> i) & 1) ? 1 : 2;
    if (reachable[i] != want)
    {
      std::stringstream ss;
      ss << "leaf assignment " << i << ": expected root " << (want == 1)
         << " but CNF allows " << (reachable[i] == 3 ? "both" : "neither/other")
         << " (reachable=" << unsigned(reachable[i]) << ")";
      err = ss.str();
      return false;
    }
  }
  return true;
}

/**
 * NPN canonical form of a `k`-input truth table: the smallest table reachable
 * by negating inputs, permuting inputs and negating the output. Two nodes with
 * the same canonical form compute the same function up to that symmetry group.
 */
uint32_t
npn_canon(uint32_t tt, int k)
{
  int n         = 1 << k;
  uint32_t mask = static_cast<uint32_t>((1ull << n) - 1);
  std::vector<int> perm(static_cast<size_t>(k));
  for (int i = 0; i < k; ++i) perm[static_cast<size_t>(i)] = i;

  uint32_t best = mask;
  do
  {
    for (int neg = 0; neg < n; ++neg)
    {
      uint32_t r = 0;
      for (int i = 0; i < n; ++i)
      {
        int j = 0;
        for (int b = 0; b < k; ++b)
        {
          int bit = (i >> b) & 1;
          if ((neg >> b) & 1) bit ^= 1;
          if (bit) j |= 1 << perm[static_cast<size_t>(b)];
        }
        if ((tt >> j) & 1) r |= 1u << i;
      }
      best = std::min(best, r);
      best = std::min(best, ~r & mask);
    }
  } while (std::next_permutation(perm.begin(), perm.end()));
  return best;
}

/** Truth table of a 4-input function given as a callable over four bools. */
template <class F>
uint32_t
tt4(F f)
{
  uint32_t tt = 0;
  for (int i = 0; i < 16; ++i)
  {
    if (f((i >> 0) & 1, (i >> 1) & 1, (i >> 2) & 1, (i >> 3) & 1))
    {
      tt |= 1u << i;
    }
  }
  return tt;
}

/** Run one invariance family: all variants must encode to the same CNF. */
void
check_invariant(const std::string& family,
                size_t nleaves,
                const std::vector<std::pair<std::string, Build>>& variants)
{
  ASSERT_FALSE(variants.empty());
  Encoded ref = encode_isolated(nleaves, variants[0].second);
  std::string err;
  ASSERT_TRUE(cnf_defines_root(ref, nleaves, err))
      << family << "/" << variants[0].first << ": " << err;
  for (size_t i = 1; i < variants.size(); ++i)
  {
    Encoded cur = encode_isolated(nleaves, variants[i].second);
    // The variants must really denote the same function -- a typo in a variant
    // would otherwise silently weaken the test.
    ASSERT_EQ(cur.truth_table, ref.truth_table)
        << family << "/" << variants[i].first
        << " does not denote the same function as " << family << "/"
        << variants[0].first;
    ASSERT_TRUE(cnf_defines_root(cur, nleaves, err))
        << family << "/" << variants[i].first << ": " << err;
    ASSERT_EQ(cur.size, ref.size)
        << family << ": variant '" << variants[i].first << "' encodes to "
        << cur.size.str() << " but '" << variants[0].first << "' encodes to "
        << ref.size.str();
  }
}

}  // namespace

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

/* --- variant invariance -------------------------------------------------- */

TEST_F(TestAigCnf, invariance_xor2)
{
  check_invariant(
      "xor2",
      2,
      {
          {"pos",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_or(l[0], l[1]),
                             m.mk_not(m.mk_and(l[0], l[1])));
           }},
          {"pos_swap",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_not(m.mk_and(l[1], l[0])),
                             m.mk_or(l[1], l[0]));
           }},
          {"sop",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(l[0], m.mk_not(l[1])),
                            m.mk_and(m.mk_not(l[0]), l[1]));
           }},
          {"sop_swap",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(m.mk_not(l[0]), l[1]),
                            m.mk_and(l[0], m.mk_not(l[1])));
           }},
          {"nand_nand",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(
                 m.mk_not(m.mk_and(l[0], l[1])),
                 m.mk_not(m.mk_and(m.mk_not(l[0]), m.mk_not(l[1]))));
           }},
          {"and_or",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_or(l[0], l[1]),
                             m.mk_or(m.mk_not(l[0]), m.mk_not(l[1])));
           }},
          {"not_iff",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(m.mk_iff(l[0], l[1]));
           }},
          {"ite",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(l[0], m.mk_not(l[1]), l[1]);
           }},
          {"ite_negcond",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(m.mk_not(l[0]), l[1], m.mk_not(l[1]));
           }},
          {"both_operands_negated",
           [](Mgr& m, const Leaves& l) {
             // (~a) ^ (~b) == a ^ b
             return m.mk_and(
                 m.mk_or(m.mk_not(l[0]), m.mk_not(l[1])),
                 m.mk_not(m.mk_and(m.mk_not(l[0]), m.mk_not(l[1]))));
           }},
      });
}

TEST_F(TestAigCnf, invariance_xnor2)
{
  check_invariant(
      "xnor2",
      2,
      {
          {"iff", [](Mgr& m, const Leaves& l) { return m.mk_iff(l[0], l[1]); }},
          {"not_pos_xor",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(
                 m.mk_and(m.mk_or(l[0], l[1]), m.mk_not(m.mk_and(l[0], l[1]))));
           }},
          {"sop",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(l[0], l[1]),
                            m.mk_and(m.mk_not(l[0]), m.mk_not(l[1])));
           }},
          {"nand_nand",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_not(m.mk_and(l[0], m.mk_not(l[1]))),
                             m.mk_not(m.mk_and(m.mk_not(l[0]), l[1])));
           }},
          {"and_or",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_or(l[0], m.mk_not(l[1])),
                             m.mk_or(m.mk_not(l[0]), l[1]));
           }},
          {"ite",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(l[0], l[1], m.mk_not(l[1]));
           }},
          {"xor_with_negated_operand",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_or(l[0], m.mk_not(l[1])),
                             m.mk_not(m.mk_and(l[0], m.mk_not(l[1]))));
           }},
      });
}

TEST_F(TestAigCnf, invariance_mux)
{
  // Note: `mux_via_xor` (y ^ (c & (x ^ y))) is deliberately *not* in this list,
  // see the mux_via_xor_builds_a_different_aig test below.
  check_invariant(
      "mux",
      3,
      {
          {"native",
           [](Mgr& m, const Leaves& l) { return m.mk_ite(l[0], l[1], l[2]); }},
          {"sop",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(l[0], l[1]),
                            m.mk_and(m.mk_not(l[0]), l[2]));
           }},
          {"sop_swap",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(m.mk_not(l[0]), l[2]),
                            m.mk_and(l[0], l[1]));
           }},
          {"sop_cond_right",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(l[1], l[0]),
                            m.mk_and(l[2], m.mk_not(l[0])));
           }},
          {"nand_nand",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(
                 m.mk_and(m.mk_not(m.mk_and(l[0], l[1])),
                          m.mk_not(m.mk_and(m.mk_not(l[0]), l[2]))));
           }},
          {"implications",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_or(m.mk_not(l[0]), l[1]),
                             m.mk_or(l[0], l[2]));
           }},
          {"negated_cond",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(m.mk_not(l[0]), l[2], l[1]);
           }},
          {"double_negated_cond",
           [](Mgr& m, const Leaves& l) {
             return m.mk_or(m.mk_and(m.mk_not(m.mk_not(l[0])), l[1]),
                            m.mk_and(m.mk_not(l[0]), l[2]));
           }},
      });
}

TEST_F(TestAigCnf, invariance_mux_negated_branches)
{
  check_invariant(
      "nmux",
      3,
      {
          {"not_native",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(m.mk_ite(l[0], l[1], l[2]));
           }},
          {"negated_branches",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(l[0], m.mk_not(l[1]), m.mk_not(l[2]));
           }},
          {"nand_nand",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_not(m.mk_and(l[0], l[1])),
                             m.mk_not(m.mk_and(m.mk_not(l[0]), l[2])));
           }},
          {"not_implications",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(
                 m.mk_and(m.mk_or(m.mk_not(l[0]), l[1]), m.mk_or(l[0], l[2])));
           }},
      });
}

TEST_F(TestAigCnf, invariance_xor3)
{
  auto xor2 = [](Mgr& m, const Aig& a, const Aig& b) {
    return m.mk_and(m.mk_or(a, b), m.mk_not(m.mk_and(a, b)));
  };
  check_invariant("xor3",
                  3,
                  {
                      {"left",
                       [xor2](Mgr& m, const Leaves& l) {
                         return xor2(m, xor2(m, l[0], l[1]), l[2]);
                       }},
                      {"right",
                       [xor2](Mgr& m, const Leaves& l) {
                         return xor2(m, l[0], xor2(m, l[1], l[2]));
                       }},
                      {"middle",
                       [xor2](Mgr& m, const Leaves& l) {
                         return xor2(m, l[1], xor2(m, l[0], l[2]));
                       }},
                      {"reversed",
                       [xor2](Mgr& m, const Leaves& l) {
                         return xor2(m, l[2], xor2(m, l[1], l[0]));
                       }},
                      {"sop_xor2",
                       [](Mgr& m, const Leaves& l) {
                         // the sum-of-products variant of the inner xor
                         auto sop = m.mk_or(m.mk_and(l[0], m.mk_not(l[1])),
                                            m.mk_and(m.mk_not(l[0]), l[1]));
                         return m.mk_or(m.mk_and(sop, m.mk_not(l[2])),
                                        m.mk_and(m.mk_not(sop), l[2]));
                       }},
                      {"mux",
                       [xor2](Mgr& m, const Leaves& l) {
                         auto t = xor2(m, l[1], l[2]);
                         return m.mk_ite(l[0], m.mk_not(t), t);
                       }},
                      {"not_iff",
                       [xor2](Mgr& m, const Leaves& l) {
                         return m.mk_not(m.mk_iff(l[0], xor2(m, l[1], l[2])));
                       }},
                  });
}

/**
 * The XOR-based realisation of a multiplexer, y ^ (c & (x ^ y)), is a different
 * circuit: the AIG rewriter has no rule that turns it into the two-level
 * multiplexer shape, so it uses more AND nodes. The residual variance between
 * mux variants therefore lives in AIG construction, not in CNF gate extraction.
 * If mux recognition is added at the AIG level this test is expected to fail
 * and should then be folded into invariance_mux.
 */
TEST_F(TestAigCnf, mux_via_xor_builds_a_different_aig)
{
  auto xor2 = [](Mgr& m, const Aig& a, const Aig& b) {
    return m.mk_and(m.mk_or(a, b), m.mk_not(m.mk_and(a, b)));
  };
  Encoded canonical = encode_isolated(
      3, [](Mgr& m, const Leaves& l) { return m.mk_ite(l[0], l[1], l[2]); });
  Encoded via_xor = encode_isolated(3, [xor2](Mgr& m, const Leaves& l) {
    return xor2(m, l[2], m.mk_and(l[0], xor2(m, l[1], l[2])));
  });

  // Same function ...
  ASSERT_EQ(via_xor.truth_table, canonical.truth_table);
  // ... and a correct encoding ...
  std::string err;
  ASSERT_TRUE(cnf_defines_root(via_xor, 3, err)) << err;
  // ... but a bigger one, because the AIG is bigger.
  ASSERT_NE(via_xor.size, canonical.size);
  ASSERT_GT(via_xor.size.vars, canonical.size.vars);
}

/**
 * Exhaustively enumerate every AIG of the shape AND(~AND(g1,g2), ~AND(g3,g4))
 * -- the shape is_ite() inspects -- with the gi drawn from the eight literals
 * over four leaves, and require that extraction is decided by the function
 * computed. A two-level AND(~AND,~AND) is an ite exactly when two of its
 * grandchildren are complementary, so extraction must happen exactly for the
 * NPN class of a multiplexer or of a two-input XOR. A shape case that covers
 * only some permutations of a pattern breaks this equality.
 */
TEST_F(TestAigCnf, ite_extraction_is_decided_by_the_function)
{
  const uint32_t c_mux =
      npn_canon(tt4([](int a, int b, int c, int) { return a ? b : c; }), 4);
  const uint32_t c_xor2 =
      npn_canon(tt4([](int a, int b, int, int) { return a ^ b; }), 4);

  // canonical function -> (first shape seen, its CNF size)
  std::map<uint32_t, std::pair<std::string, EncSize>> seen;
  size_t nshapes = 0, nextracted = 0;
  for (int g = 0; g < 8 * 8 * 8 * 8; ++g)
  {
    const int idx[4] = {g & 7, (g >> 3) & 7, (g >> 6) & 7, (g >> 9) & 7};
    Build build      = [&idx](Mgr& m, const Leaves& l) {
      auto lit = [&](int i) {
        return (i & 1) ? m.mk_not(l[static_cast<size_t>(i >> 1)])
                       : l[static_cast<size_t>(i >> 1)];
      };
      Aig p = m.mk_and(lit(idx[0]), lit(idx[1]));
      Aig q = m.mk_and(lit(idx[2]), lit(idx[3]));
      return m.mk_and(m.mk_not(p), m.mk_not(q));
    };
    Encoded e = encode_isolated(4, build);
    // AIG rewriting collapses many of the combinations to something that is no
    // longer a two-level AND of two negated ANDs; those are out of scope here.
    if (!e.two_level) continue;
    ++nshapes;

    std::stringstream name;
    name << "g=(" << idx[0] << "," << idx[1] << "," << idx[2] << "," << idx[3]
         << ")";
    std::string err;
    ASSERT_TRUE(cnf_defines_root(e, 4, err)) << name.str() << ": " << err;

    uint32_t canon = npn_canon(e.truth_table, 4);
    bool want_xor  = (canon == c_xor2);
    bool want_ite  = (canon == c_mux || want_xor);
    // num_ites and num_xors are disjoint, so extraction shows up in exactly
    // one of them, and which one has to agree with the function's NPN class.
    bool extracted = (e.size.ites + e.size.xors) == 1;
    ASSERT_EQ(extracted, want_ite)
        << name.str() << ": extracted=" << extracted << " but the function "
        << (want_ite ? "is" : "is not") << " a multiplexer/XOR (canon=" << canon
        << ")";
    ASSERT_EQ(e.size.xors == 1, want_xor)
        << name.str() << ": counted as xor=" << (e.size.xors == 1)
        << " but the function " << (want_xor ? "is" : "is not")
        << " a XOR (canon=" << canon << ")";
    if (extracted) ++nextracted;

    auto [it, inserted] =
        seen.emplace(canon, std::make_pair(name.str(), e.size));
    if (!inserted)
    {
      ASSERT_EQ(e.size, it->second.second)
          << "shapes " << it->second.first << " and " << name.str()
          << " compute the same function but encode to "
          << it->second.second.str() << " and " << e.size.str();
    }
  }
  std::cout << "  [ ] " << nshapes << " two-level shapes, " << nextracted
            << " extracted, " << seen.size() << " distinct functions"
            << std::endl;
  // Guard against the enumeration silently degenerating to nothing.
  ASSERT_GT(nshapes, 500u);
  ASSERT_GT(nextracted, 100u);
}

TEST_F(TestAigCnf, invariance_nary_and)
{
  // Whatever way an n-ary AND is bracketed, collect_and() has to flatten it
  // into the same single gate.
  check_invariant(
      "and4",
      4,
      {
          {"left",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_and(m.mk_and(l[0], l[1]), l[2]), l[3]);
           }},
          {"right",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(l[0], m.mk_and(l[1], m.mk_and(l[2], l[3])));
           }},
          {"balanced",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(m.mk_and(l[0], l[1]), m.mk_and(l[2], l[3]));
           }},
          {"reversed",
           [](Mgr& m, const Leaves& l) {
             return m.mk_and(l[3], m.mk_and(l[2], m.mk_and(l[1], l[0])));
           }},
          {"de_morgan",
           [](Mgr& m, const Leaves& l) {
             return m.mk_not(m.mk_or(m.mk_or(m.mk_not(l[0]), m.mk_not(l[1])),
                                     m.mk_or(m.mk_not(l[2]), m.mk_not(l[3]))));
           }},
      });
}

TEST_F(TestAigCnf, invariance_nested_mux)
{
  check_invariant(
      "mux2",
      5,
      {
          {"native",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(l[0], l[1], m.mk_ite(l[2], l[3], l[4]));
           }},
          {"sop",
           [](Mgr& m, const Leaves& l) {
             auto inner =
                 m.mk_or(m.mk_and(l[2], l[3]), m.mk_and(m.mk_not(l[2]), l[4]));
             return m.mk_or(m.mk_and(l[0], l[1]),
                            m.mk_and(m.mk_not(l[0]), inner));
           }},
          {"mixed",
           [](Mgr& m, const Leaves& l) {
             auto inner =
                 m.mk_and(m.mk_or(m.mk_not(l[2]), l[3]), m.mk_or(l[2], l[4]));
             return m.mk_not(
                 m.mk_and(m.mk_not(m.mk_and(l[0], l[1])),
                          m.mk_not(m.mk_and(m.mk_not(l[0]), inner))));
           }},
          {"negated_conds",
           [](Mgr& m, const Leaves& l) {
             return m.mk_ite(
                 m.mk_not(l[0]), m.mk_ite(m.mk_not(l[2]), l[4], l[3]), l[1]);
           }},
      });
}

/**
 * Randomised correctness check: for a few thousand random AIGs the emitted CNF
 * must be equivalent to the AIG, checked by brute force against the truth
 * table. A gate extraction drops the inner AND nodes of the pattern it matched,
 * so a polarity mismatch produces a silently wrong encoding that no
 * clause-count comparison detects. This is the test a new matcher has to pass.
 */
TEST_F(TestAigCnf, encoding_matches_truth_table_random)
{
  // xorshift, so that the test is reproducible without <random> details
  uint64_t state = 0x9e3779b97f4a7c15ull;
  auto rnd       = [&state](uint32_t n) {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    return static_cast<uint32_t>(state % n);
  };

  constexpr size_t nleaves = 4;
  size_t nchecked          = 0;
  for (size_t iter = 0; iter < 4000; ++iter)
  {
    // Build a random AIG over `nleaves` leaves out of 2..8 AND gates. The
    // steps are precomputed so that the builder is a pure function.
    size_t nsteps = 2 + rnd(7);
    std::vector<std::array<uint32_t, 4>> steps;
    for (size_t s = 0; s < nsteps; ++s)
    {
      uint32_t navail = static_cast<uint32_t>(nleaves + s);
      steps.push_back({rnd(navail), rnd(2), rnd(navail), rnd(2)});
    }
    Build build = [&steps](Mgr& m, const Leaves& l) {
      std::vector<Aig> pool(l.begin(), l.end());
      for (const auto& s : steps)
      {
        Aig a = pool[s[0]];
        Aig b = pool[s[2]];
        if (s[1]) a = m.mk_not(a);
        if (s[3]) b = m.mk_not(b);
        pool.push_back(m.mk_and(a, b));
      }
      return pool.back();
    };
    Encoded e = encode_isolated(nleaves, build);
    // Nodes that rewriting collapsed to a leaf or a constant carry no gate.
    if (!e.root_is_and || e.root_lit == 0) continue;
    ++nchecked;
    std::string err;
    ASSERT_TRUE(cnf_defines_root(e, nleaves, err))
        << "iteration " << iter << ": " << err;
  }
  ASSERT_GT(nchecked, 2000u);
}

/**
 * The ITE sharing guard is context sensitive, not variant sensitive. Different
 * variants of the same function build different inner nodes, so a surrounding
 * formula can alias the inner nodes of one variant and not those of another,
 * which looks like a missed shape but is the cost model reacting to genuine
 * sharing.
 */
TEST_F(TestAigCnf, ite_sharing_guard_depends_on_context)
{
  Mgr mgr;
  DummySatSolver solver;
  bitblast::AigCnfEncoder enc(solver);

  Aig c = mgr.mk_bit(), x = mgr.mk_bit(), y = mgr.mk_bit(), z = mgr.mk_bit();

  // The two inner ANDs of the sum-of-products variant of ite(c,x,y) ...
  Aig then_ = mgr.mk_and(c, x);
  Aig else_ = mgr.mk_and(mgr.mk_not(c), y);
  Aig mux   = mgr.mk_or(then_, else_);
  // ... also occur elsewhere, so both have two parents.
  Aig other = mgr.mk_and(mgr.mk_and(then_, z), else_);
  ASSERT_GT(then_.parents(), 1u);
  ASSERT_GT(else_.parents(), 1u);

  enc.encode(mux, false);
  enc.encode(other, false);
  // The ITE is not extracted, and both inner nodes keep their variable.
  ASSERT_EQ(enc.statistics().num_ites, 0u);
  ASSERT_TRUE(enc.is_encoded(then_));
  ASSERT_TRUE(enc.is_encoded(else_));

  // With no other parent the very same variant is extracted.
  Mgr mgr2;
  DummySatSolver solver2;
  bitblast::AigCnfEncoder enc2(solver2);
  Aig c2 = mgr2.mk_bit(), x2 = mgr2.mk_bit(), y2 = mgr2.mk_bit();
  Aig mux2 = mgr2.mk_or(mgr2.mk_and(c2, x2), mgr2.mk_and(mgr2.mk_not(c2), y2));
  enc2.encode(mux2, false);
  ASSERT_EQ(enc2.statistics().num_ites, 1u);
}

/**
 * Characterisation of a real remaining variant sensitivity: a majority gate
 * encodes to a different CNF depending on which variant is built, because only
 * the multiplexer variant has two complementary grandchildren and is therefore
 * the only one is_ite() recognises. The two shapes the bit-blaster builds for a
 * carry out are the other ones, which encode larger.
 */
TEST_F(TestAigCnf, maj3_is_variant_sensitive)
{
  auto xor2 = [](Mgr& m, const Aig& a, const Aig& b) {
    return m.mk_and(m.mk_or(a, b), m.mk_not(m.mk_and(a, b)));
  };
  // (a & b) | ((a | b) & c)
  Encoded or_form = encode_isolated(3, [](Mgr& m, const Leaves& l) {
    return m.mk_or(m.mk_and(l[0], l[1]), m.mk_and(m.mk_or(l[0], l[1]), l[2]));
  });
  // ite(c, a | b, a & b)
  Encoded ite_form = encode_isolated(3, [](Mgr& m, const Leaves& l) {
    return m.mk_ite(l[2], m.mk_or(l[0], l[1]), m.mk_and(l[0], l[1]));
  });
  // (a & b) | ((a ^ b) & c), i.e. what full_adder() in bitblaster.h builds
  Encoded carry_form = encode_isolated(3, [xor2](Mgr& m, const Leaves& l) {
    return m.mk_or(m.mk_and(l[0], l[1]), m.mk_and(xor2(m, l[0], l[1]), l[2]));
  });

  ASSERT_EQ(or_form.truth_table, ite_form.truth_table);
  ASSERT_EQ(or_form.truth_table, carry_form.truth_table);
  std::string err;
  ASSERT_TRUE(cnf_defines_root(or_form, 3, err)) << err;
  ASSERT_TRUE(cnf_defines_root(ite_form, 3, err)) << err;
  ASSERT_TRUE(cnf_defines_root(carry_form, 3, err)) << err;

  // Only the multiplexer variant is recognised.
  ASSERT_EQ(or_form.size.ites, 0u);
  ASSERT_EQ(ite_form.size.ites, 1u);
  ASSERT_NE(or_form.size, ite_form.size);
  ASSERT_LT(ite_form.size.vars, or_form.size.vars);
  ASSERT_LT(ite_form.size.clauses, carry_form.size.clauses);
}

}  // namespace bzla::test
