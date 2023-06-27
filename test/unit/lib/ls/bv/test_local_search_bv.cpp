/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <map>

#include "ls/ls_bv.h"
#include "test_bvnode.h"

namespace bzla::ls::test {

class TestLsBv : public TestBvNodeCommon
{
 protected:
  /**
   * True to enable slow tests (of larger bit-width TEST_BW = 4), else use
   * TEST_BW_FAST = 3. This distinction is only used for tests that are slow
   * with TEST_BW, else TEST_BW is the default.
   */
  static constexpr bool TEST_SLOW = false;
  /**
   * The bit-width used for tests that are slow with TEST_BW when TEST_SLOW is
   * enabled.
   */
  static constexpr uint32_t TEST_BW_FAST = 3;
  /**
   * The maximum number of moves for test_move_binary() and test_ite()
   * when TEST_SLOW is enabled.
   */
  static constexpr uint32_t NMOVES_SLOW = 55;
  /**
   * The maximum number of moves for test_move_binary() and test_ite()
   * when TEST_SLOW is disabled.
   */
  static constexpr uint32_t NMOVES_FAST = 35;

  void SetUp() override
  {
    TestBvNodeCommon::SetUp();

    d_ls.reset(new LocalSearchBV(100, 100));

    d_two4  = BitVector(4, "0010");
    d_for4  = BitVector(4, "0100");
    d_fiv4  = BitVector(4, "0101");
    d_six4  = BitVector(4, "0110");
    d_sev4  = BitVector(4, "0111");
    d_ten4  = BitVector(4, "1010");
    d_ele4  = BitVector(4, "1011");
    d_egt4  = BitVector(4, "1000");
    d_twe4  = BitVector(4, "1100");
    d_thi4  = BitVector(4, "1101");
    d_zero4 = BitVector::mk_zero(4);
    d_zero1 = BitVector::mk_zero(1);
    d_ones4 = BitVector::mk_ones(4);
    d_one4  = BitVector::mk_one(4);
    d_one1  = BitVector::mk_one(1);

    d_c1 = d_ls->mk_node(d_ten4, BitVectorDomain(d_ten4));
    d_v1 = d_ls->mk_node(NodeKind::CONST, TEST_BW);
    d_v2 = d_ls->mk_node(NodeKind::CONST, TEST_BW);
    d_v3 = d_ls->mk_node(NodeKind::CONST, TEST_BW);

    d_ls->set_assignment(d_v2, d_ones4);
    d_ls->set_assignment(d_v3, d_six4);

    // v1 + c1
    d_v1pc1 = d_ls->mk_node(NodeKind::BV_ADD, TEST_BW, {d_v1, d_c1});
    // (v1 + c1) * v2
    d_v1pc1mv2 = d_ls->mk_node(NodeKind::BV_MUL, TEST_BW, {d_v1pc1, d_v2});
    // v1 + v2
    d_v1pv2 = d_ls->mk_node(NodeKind::BV_ADD, TEST_BW, {d_v1, d_v2});
    // (v1 + v2) & v2
    d_v1pv2av2 = d_ls->mk_node(NodeKind::BV_AND, TEST_BW, {d_v1pv2, d_v2});

    // v1[0:0]
    d_v1e = d_ls->mk_node(NodeKind::BV_EXTRACT, 1, {d_v1}, {0, 0});
    // v3[0:0]
    d_v3e = d_ls->mk_node(NodeKind::BV_EXTRACT, 1, {d_v3}, {0, 0});
    // v1[0:0] / v3[0:0]
    d_v1edv3e = d_ls->mk_node(NodeKind::BV_UDIV, 1, {d_v1e, d_v3e});
    // sext(v1[0:0] / v3[0:0], 3)
    d_v1edv3e_ext = d_ls->mk_node(NodeKind::BV_SEXT, TEST_BW, {d_v1edv3e}, {3});

    // v3 << c1
    d_v3sc1 = d_ls->mk_node(NodeKind::BV_SHL, TEST_BW, {d_v3, d_c1});
    // (v3 << c1) + v3
    d_v3sc1pv3 = d_ls->mk_node(NodeKind::BV_ADD, TEST_BW, {d_v3sc1, d_v3});
    // ((v3 << c1) + v3) + v1
    d_v3sc1pv3pv1 =
        d_ls->mk_node(NodeKind::BV_ADD, TEST_BW, {d_v3sc1pv3, d_v1});

    // root1: (v1 + c1) + v2 < (v1 + v2) & v2
    d_root1 = d_ls->mk_node(NodeKind::BV_SLT, 1, {d_v1pc1mv2, d_v1pv2av2});
    // root2: sext(v1[0:0] + v3[0:0], 3) = ((v3 + c1) + v3) + v1
    d_root2 = d_ls->mk_node(NodeKind::EQ, 1, {d_v1edv3e_ext, d_v3sc1pv3pv1});
  }

  /**
   * Create a mapping from nodes to their parents to compare against the
   * mapping created internally on node creation.
   */
  LocalSearchBV::ParentsMap get_expected_parents();
  /**
   * Get a reference of the parents map of the LocalSearchBV object.
   * Note: LocalSearchBV::d_parents is private and only the main test class has
   *       access to it.
   */
  const LocalSearchBV::ParentsMap& get_parents() { return d_ls->d_parents; }

  /**
   * Wrapper for LocalSearchBV::update_cone().
   * Note: LocalSearchBV::update_cone() is private and only the main test class
   * has access to it.
   */
  void update_cone(uint64_t id, const BitVector& assignment);

  void test_move_binary(NodeKind kind, uint32_t pos_x);
  void test_move_ite(uint32_t pos_x);
  void test_move_not();
  void test_move_extract();
  void test_move_sext();

  std::unique_ptr<LocalSearchBV> d_ls;

  BitVector d_two4, d_for4, d_fiv4, d_six4, d_sev4;
  BitVector d_egt4, d_ten4, d_ele4, d_twe4, d_thi4;
  BitVector d_zero4, d_zero1, d_ones4, d_one4, d_one1;

  uint64_t d_c1, d_v1, d_v2, d_v3;
  uint64_t d_v1pc1, d_v1pc1mv2;
  uint64_t d_v1pv2, d_v1pv2av2;
  uint64_t d_v1e, d_v3e;
  uint64_t d_v1edv3e, d_v1edv3e_ext;
  uint64_t d_v3sc1, d_v3sc1pv3;
  uint64_t d_v3sc1pv3pv1;
  uint64_t d_root1, d_root2;
};

LocalSearchBV::ParentsMap
TestLsBv::get_expected_parents()
{
  LocalSearchBV::ParentsMap parents;
  std::vector<uint64_t> to_visit = {d_root1, d_root2};
  while (!to_visit.empty())
  {
    uint64_t cur_id = to_visit.back();
    to_visit.pop_back();
    if (parents.find(cur_id) == parents.end())
    {
      parents[cur_id] = {};
    }
    for (uint32_t i = 0; i < d_ls->get_arity(cur_id); ++i)
    {
      uint64_t child_id = d_ls->get_child(cur_id, i);
      if (parents.find(child_id) == parents.end())
      {
        parents[child_id] = {};
      }
      if (parents.at(child_id).find(cur_id) == parents.at(child_id).end())
      {
        parents.at(child_id).insert(cur_id);
      }
      to_visit.push_back(child_id);
    }
  }
  return parents;
}

void
TestLsBv::update_cone(uint64_t id, const BitVector& assignment)
{
  d_ls->update_cone(d_ls->get_node(id), assignment);
}

void
TestLsBv::test_move_binary(NodeKind kind, uint32_t pos_x)
{
  std::vector<std::string> xvalues;
  if (TEST_SLOW)
  {
    xvalues = d_xvalues;
  }
  else
  {
    gen_xvalues(3, xvalues);
  }

  for (const std::string& s_domain_value : xvalues)
  {
    BitVectorDomain s(s_domain_value);
    BitVectorDomainGenerator gens(s);
    do
    {
      BitVector s_val = gens.has_next() ? gens.next() : s.lo();
      for (const std::string& x_domain_value : xvalues)
      {
        BitVectorDomain x(x_domain_value);
        BitVectorDomainGenerator genx(x);
        do
        {
          BitVector x_val = genx.has_next() ? genx.next() : x.lo();
          BitVector t_val = eval_op_binary(kind, x_val, s_val, pos_x);

          uint64_t bw_t = t_val.size();

          BitVectorDomainGenerator genrx(x, d_rng.get());
          BitVectorDomainGenerator genrs(s, d_rng.get());

          // s fix, x random, one move
          {
            BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();

            LocalSearchBV ls(1, 1);
            uint64_t op_s = ls.mk_node(s_val, s);
            uint64_t op_x = ls.mk_node(rx_val, x);
            uint64_t op =
                pos_x == 0
                    ? ls.mk_node(kind, BitVectorDomain(bw_t), {op_x, op_s})
                    : ls.mk_node(kind, BitVectorDomain(bw_t), {op_s, op_x});
            uint64_t t = ls.mk_node(t_val, BitVectorDomain(t_val));
            uint64_t root =
                ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
            ls.register_root(root);
            Result res = ls.move();
            assert(!ls.get_domain(root).is_fixed()
                   || !ls.get_assignment(root).is_false()
                   || res == Result::UNSAT);
            assert(res == Result::UNSAT || res == Result::SAT);
            assert(res == Result::UNSAT || ls.get_assignment(root).is_true());
            assert(ls.d_statistics.d_nmoves == 0
                   || (ls.d_statistics.d_nprops > 0
                       && ls.d_statistics.d_nprops
                              == 2 * ls.d_statistics.d_nmoves));
            assert(ls.d_statistics.d_nmoves == 0
                   || (ls.d_statistics.d_nupdates > 0
                       && ls.d_statistics.d_nupdates
                              <= 3 * ls.d_statistics.d_nmoves));
            (void) res;
          }

          // s random, x random, n moves
          {
            BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();
            BitVector rs_val = genrs.has_random() ? genrs.random() : s.lo();

            LocalSearchBV ls(100, 100);
            uint64_t op_s = ls.mk_node(rs_val, s);
            uint64_t op_x = ls.mk_node(rx_val, x);
            uint64_t op =
                pos_x == 0
                    ? ls.mk_node(kind, BitVectorDomain(bw_t), {op_x, op_s})
                    : ls.mk_node(kind, BitVectorDomain(bw_t), {op_s, op_x});
            uint64_t t = ls.mk_node(t_val, BitVectorDomain(t_val));
            uint64_t root =
                ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
            ls.register_root(root);
            Result res;
            do
            {
              res = ls.move();
            } while (res == Result::UNKNOWN
                     && ls.d_statistics.d_nmoves
                            < (TEST_SLOW ? NMOVES_SLOW : NMOVES_FAST));
            assert(!ls.get_domain(root).is_fixed()
                   || !ls.get_assignment(root).is_false()
                   || res == Result::UNSAT);
            assert(res == Result::UNSAT || res == Result::SAT);
            assert(res == Result::UNSAT || ls.get_assignment(root).is_true());
            assert(ls.d_statistics.d_nmoves == 0
                   || (ls.d_statistics.d_nprops > 0
                       && ls.d_statistics.d_nprops
                              >= 2 * ls.d_statistics.d_nmoves));
            assert(ls.d_statistics.d_nmoves == 0
                   || (ls.d_statistics.d_nupdates > 0
                       && ls.d_statistics.d_nupdates
                              <= 3 * ls.d_statistics.d_nmoves));
          }
        } while (genx.has_next());
      }
    } while (gens.has_next());
  }
}

void
TestLsBv::test_move_ite(uint32_t pos_x)
{
  std::vector<std::string> cond_values = {"x", "0", "1"};
  std::vector<std::string> xvalues, s0values, s1values;

  if (pos_x == 0)
  {
    xvalues = cond_values;
    if (TEST_SLOW)
    {
      s0values = d_xvalues;
      s1values = d_xvalues;
    }
    else
    {
      gen_xvalues(3, s0values);
      gen_xvalues(3, s1values);
    }
  }
  else
  {
    s0values = cond_values;
    if (TEST_SLOW)
    {
      xvalues  = d_xvalues;
      s1values = d_xvalues;
    }
    else
    {
      gen_xvalues(3, xvalues);
      gen_xvalues(3, s1values);
    }
  }

  for (const std::string& s0_domain_value : s0values)
  {
    BitVectorDomain s0(s0_domain_value);
    BitVectorDomainGenerator gens0(s0);
    do
    {
      BitVector s0_val = gens0.has_next() ? gens0.next() : s0.lo();
      for (const std::string& s1_domain_value : s1values)
      {
        BitVectorDomain s1(s1_domain_value);
        BitVectorDomainGenerator gens1(s1);
        do
        {
          BitVector s1_val = gens1.has_next() ? gens1.next() : s1.lo();
          for (const std::string& x_domain_value : xvalues)
          {
            BitVectorDomain x(x_domain_value);
            BitVectorDomainGenerator genx(x);
            do
            {
              BitVector x_val = genx.has_next() ? genx.next() : x.lo();
              BitVector t_val =
                  pos_x == 0
                      ? BitVector::bvite(x_val, s0_val, s1_val)
                      : (pos_x == 1 ? BitVector::bvite(s0_val, x_val, s1_val)
                                    : BitVector::bvite(s0_val, s1_val, x_val));
              uint64_t bw_t = t_val.size();

              BitVectorDomainGenerator genrx(x, d_rng.get());
              BitVectorDomainGenerator genrs0(s0, d_rng.get());
              BitVectorDomainGenerator genrs1(s1, d_rng.get());

              // s0 fix, , s1 fix, x random, one move
              {
                BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();

                LocalSearchBV ls(100, 100);
                uint64_t op_s0 = ls.mk_node(s0_val, s0);
                uint64_t op_s1 = ls.mk_node(s1_val, s1);
                uint64_t op_x  = ls.mk_node(rx_val, x);
                uint64_t op =
                    pos_x == 0
                        ? ls.mk_node(NodeKind::ITE,
                                     BitVectorDomain(bw_t),
                                     {op_x, op_s0, op_s1})
                        : (pos_x == 1 ? ls.mk_node(NodeKind::ITE,
                                                   BitVectorDomain(bw_t),
                                                   {op_s0, op_x, op_s1})
                                      : ls.mk_node(NodeKind::ITE,
                                                   BitVectorDomain(bw_t),
                                                   {op_s0, op_s1, op_x}));
                uint64_t t = ls.mk_node(t_val, BitVectorDomain(t_val));
                uint64_t root =
                    ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
                ls.register_root(root);
                Result res = ls.move();
                assert(!ls.get_domain(root).is_fixed()
                       || !ls.get_assignment(root).is_false()
                       || res == Result::UNSAT);
                assert(res == Result::UNSAT || res == Result::SAT);
                assert(res == Result::UNSAT
                       || ls.get_assignment(root).is_true());
                (void) res;
              }

              // s random, x random, n moves
              {
                BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();
                BitVector rs0_val =
                    genrs0.has_random() ? genrs0.random() : s0.lo();
                BitVector rs1_val =
                    genrs1.has_random() ? genrs1.random() : s1.lo();

                LocalSearchBV ls(100, 100);
                uint64_t op_s0 = ls.mk_node(rs0_val, s0);
                uint64_t op_s1 = ls.mk_node(rs1_val, s1);
                uint64_t op_x  = ls.mk_node(rx_val, x);
                uint64_t op =
                    pos_x == 0
                        ? ls.mk_node(NodeKind::ITE,
                                     BitVectorDomain(bw_t),
                                     {op_x, op_s0, op_s1})
                        : (pos_x == 1 ? ls.mk_node(NodeKind::ITE,
                                                   BitVectorDomain(bw_t),
                                                   {op_s0, op_x, op_s1})
                                      : ls.mk_node(NodeKind::ITE,
                                                   BitVectorDomain(bw_t),
                                                   {op_s0, op_s1, op_x}));
                uint64_t t = ls.mk_node(t_val, BitVectorDomain(t_val));
                uint64_t root =
                    ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
                ls.register_root(root);
                Result res;
                do
                {
                  res = ls.move();
                } while (res == Result::UNKNOWN
                         && ls.d_statistics.d_nmoves
                                < (TEST_SLOW ? NMOVES_SLOW : NMOVES_FAST));
                assert(!ls.get_domain(root).is_fixed()
                       || !ls.get_assignment(root).is_false()
                       || res == Result::UNSAT);
                assert(res == Result::UNSAT || res == Result::SAT);
                assert(res == Result::UNSAT
                       || ls.get_assignment(root).is_true());
              }
            } while (genx.has_next());
          }
        } while (gens1.has_next());
      }
    } while (gens0.has_next());
  }
}

void
TestLsBv::test_move_not()
{
  std::vector<std::string> xvalues;
  if (TEST_SLOW)
  {
    xvalues = d_xvalues;
  }
  else
  {
    gen_xvalues(3, xvalues);
  }

  for (const std::string& x_domain_value : xvalues)
  {
    BitVectorDomain x(x_domain_value);
    BitVectorDomainGenerator genx(x);
    do
    {
      BitVector x_val = genx.has_next() ? genx.next() : x.lo();
      BitVector t_val = x_val.bvnot();

      uint64_t bw_t = t_val.size();

      BitVectorDomainGenerator genrx(x, d_rng.get());
      BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();

      LocalSearchBV ls(100, 100);
      uint64_t op_x = ls.mk_node(rx_val, x);
      uint64_t op   = ls.mk_node(NodeKind::NOT, BitVectorDomain(bw_t), {op_x});
      uint64_t t    = ls.mk_node(t_val, BitVectorDomain(t_val));
      uint64_t root = ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
      ls.register_root(root);
      Result res = ls.move();
      assert(!ls.get_domain(root).is_fixed()
             || !ls.get_assignment(root).is_false() || res == Result::UNSAT);
      assert(res == Result::UNSAT || res == Result::SAT);
      assert(res == Result::UNSAT || ls.get_assignment(root).is_true());
      (void) res;
    } while (genx.has_next());
  }
}

void
TestLsBv::test_move_extract()
{
  std::vector<std::string> xvalues;
  if (TEST_SLOW)
  {
    xvalues = d_xvalues;
  }
  else
  {
    gen_xvalues(3, xvalues);
  }

  for (const std::string& x_domain_value : xvalues)
  {
    BitVectorDomain x(x_domain_value);
    uint64_t bw_x = x.size();
    BitVectorDomainGenerator genx(x);
    do
    {
      BitVector x_val = genx.has_next() ? genx.next() : x.lo();
      for (uint64_t lo = 0; lo < bw_x; ++lo)
      {
        for (uint64_t hi = lo; hi < bw_x; ++hi)
        {
          uint64_t bw_t = hi - lo + 1;
          for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
          {
            BitVector t_val = x_val.bvextract(hi, lo);

            BitVectorDomainGenerator genrx(x, d_rng.get());
            BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();

            LocalSearchBV ls(100, 100);
            uint64_t op_x = ls.mk_node(rx_val, x);
            uint64_t op   = ls.mk_node(
                NodeKind::BV_EXTRACT, BitVectorDomain(bw_t), {op_x}, {hi, lo});
            uint64_t t  = ls.mk_node(t_val, BitVectorDomain(t_val));
            uint64_t root =
                ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
            ls.register_root(root);
            Result res = ls.move();
            assert(!ls.get_domain(root).is_fixed()
                   || !ls.get_assignment(root).is_false()
                   || res == Result::UNSAT);
            assert(res == Result::UNSAT || res == Result::SAT);
            assert(res == Result::UNSAT || ls.get_assignment(root).is_true());
            (void) res;
          }
        }
      }
    } while (genx.has_next());
  }
}

void
TestLsBv::test_move_sext()
{
  std::vector<std::string> xvalues;
  if (TEST_SLOW)
  {
    xvalues = d_xvalues;
  }
  else
  {
    gen_xvalues(3, xvalues);
  }

  for (const std::string& x_domain_value : xvalues)
  {
    BitVectorDomain x(x_domain_value);
    uint64_t bw_x = x.size();
    BitVectorDomainGenerator genx(x);
    do
    {
      BitVector x_val = genx.has_next() ? genx.next() : x.lo();
      for (uint64_t n = 1; n <= bw_x; ++n)
      {
        BitVector t_val = x_val.bvsext(n);

        uint64_t bw_t = t_val.size();

        BitVectorDomainGenerator genrx(x, d_rng.get());
        BitVector rx_val = genrx.has_random() ? genrx.random() : x.lo();

        LocalSearchBV ls(100, 100);
        uint64_t op_x = ls.mk_node(rx_val, x);
        uint64_t op =
            ls.mk_node(NodeKind::BV_SEXT, BitVectorDomain(bw_t), {op_x}, {n});
        uint64_t t = ls.mk_node(t_val, BitVectorDomain(t_val));
        uint64_t root = ls.mk_node(NodeKind::EQ, BitVectorDomain(1), {op, t});
        ls.register_root(root);
        Result res = ls.move();
        assert(!ls.get_domain(root).is_fixed()
               || !ls.get_assignment(root).is_false() || res == Result::UNSAT);
        assert(res == Result::UNSAT || res == Result::SAT);
        assert(res == Result::UNSAT || ls.get_assignment(root).is_true());
        (void) res;
      }
    } while (genx.has_next());
  }
}

TEST_F(TestLsBv, parents)
{
  d_ls->register_root(d_root1);
  d_ls->register_root(d_root2);

  const LocalSearchBV::ParentsMap& parents   = get_parents();
  LocalSearchBV::ParentsMap parents_expected = get_expected_parents();

  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_c1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_c1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 2);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v3sc1) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 4);
    ASSERT_TRUE(p.find(d_v1pc1) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v3sc1pv3pv1) != p.end());
    ASSERT_TRUE(p.find(d_v1e) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v2);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v1pc1mv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2) != p.end());
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v3);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v3);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 3);
    ASSERT_TRUE(p.find(d_v3sc1) != p.end());
    ASSERT_TRUE(p.find(d_v3sc1pv3) != p.end());
    ASSERT_TRUE(p.find(d_v3e) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1pc1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1pc1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pc1mv2) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1pc1mv2);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1pc1mv2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1pv2);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1pv2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1pv2av2) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1pv2av2);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1pv2av2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root1) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1e);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1edv3e) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v3e);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v3e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1edv3e) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1edv3e);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1edv3e);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v1edv3e_ext) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v1edv3e_ext);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v1edv3e_ext);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v3sc1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v3sc1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3sc1pv3) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v3sc1pv3);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v3sc1pv3);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_v3sc1pv3pv1) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_v3sc1pv3pv1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_v3sc1pv3pv1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 1);
    ASSERT_TRUE(p.find(d_root2) != p.end());
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_root1);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_root1);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 0);
  }
  {
    const std::unordered_set<uint64_t>& p  = parents.at(d_root2);
    const std::unordered_set<uint64_t>& pe = parents_expected.at(d_root2);
    ASSERT_EQ(p, pe);
    ASSERT_TRUE(p.size() == 0);
  }
}

TEST_F(TestLsBv, update_cone)
{
  std::map<uint32_t, BitVector> ass_init = {
      {d_c1, d_ten4},            // 1010
      {d_v1, d_zero4},           // 0000
      {d_v2, d_ones4},           // 1111
      {d_v3, d_six4},            // 0110
      {d_v1pc1, d_ten4},         // 0000 + 1010 = 1010
      {d_v1pc1mv2, d_six4},      // 1010 * 1111 = 0110
      {d_v1pv2, d_ones4},        // 0000 + 1111 = 1111
      {d_v1pv2av2, d_ones4},     // 1111 & 1111 = 1111
      {d_v1e, d_zero1},          // 0000[0:0] = 0
      {d_v3e, d_zero1},          // 0110[0:0] = 0
      {d_v1edv3e, d_one1},       // 0 / 0 = 1
      {d_v1edv3e_ext, d_ones4},  // sext(1, 3) = 1111
      {d_v3sc1, d_zero4},        // 0110 << 1010 = 0000
      {d_v3sc1pv3, d_six4},      // 0000 + 0110 = 0110
      {d_v3sc1pv3pv1, d_six4},   // 0110 + 0000 = 0110
      {d_root1, d_zero1},        // 0110 <s 1111 = 0
      {d_root2, d_zero1},        // 0110 == 0000 = 0
  };

  for (auto& p : ass_init)
  {
    ASSERT_EQ(d_ls->get_assignment(p.first).compare(p.second), 0);
  }

  /* v1 -> 0001 */
  update_cone(d_v1, d_one4);
  std::map<uint32_t, BitVector> ass_up_v1 = {
      {d_c1, d_ten4},            // 1010
      {d_v1, d_one4},            // 0001
      {d_v2, d_ones4},           // 1111
      {d_v3, d_six4},            // 0110
      {d_v1pc1, d_ele4},         // 0001 + 1010 = 1011
      {d_v1pc1mv2, d_fiv4},      // 1011 * 1111 = 0101
      {d_v1pv2, d_zero4},        // 0001 + 1111 = 0000
      {d_v1pv2av2, d_zero4},     // 0000 & 1111 = 0000
      {d_v1e, d_one1},           // 0001[0:0] = 1
      {d_v3e, d_zero1},          // 0110[0:0] = 0 (not in COI)
      {d_v1edv3e, d_one1},       // 1 / 0 = 1
      {d_v1edv3e_ext, d_ones4},  // sext(1, 3) = 1111
      {d_v3sc1, d_zero4},        // 0110 << 1010 = 0000 (not in COI)
      {d_v3sc1pv3, d_six4},      // 0000 + 0110 = 0110  (not in COI)
      {d_v3sc1pv3pv1, d_sev4},   // 0110 + 0001 = 0111
      {d_root1, d_zero1},        // 0101 <s 0000 = 0
      {d_root2, d_zero1},        // 0111 == 1111 = 0
  };
  for (auto& p : ass_up_v1)
  {
    ASSERT_EQ(d_ls->get_assignment(p.first).compare(p.second), 0);
  }

  /* v2 -> 0111 */
  update_cone(d_v2, d_sev4);
  std::map<uint32_t, BitVector> ass_up_v2 = {
      {d_c1, d_ten4},            // 1010
      {d_v1, d_one4},            // 0001
      {d_v2, d_sev4},            // 0111
      {d_v3, d_six4},            // 0110
      {d_v1pc1, d_ele4},         // 0001 + 1010 = 1011 (not in COI)
      {d_v1pc1mv2, d_thi4},      // 1011 * 0111 = 1101
      {d_v1pv2, d_egt4},         // 0001 + 0111 = 1000
      {d_v1pv2av2, d_zero4},     // 1000 & 0111 = 0000
      {d_v1e, d_one1},           // 0001[0:0] = 1 (not in COI)
      {d_v3e, d_zero1},          // 0110[0:0] = 0 (not in COI)
      {d_v1edv3e, d_one1},       // 1 / 0 = 1 (not in COI)
      {d_v1edv3e_ext, d_ones4},  // sext(1, 3) = 1111 (not in COI)
      {d_v3sc1, d_zero4},        // 0110 << 1010 = 0000 (not in COI)
      {d_v3sc1pv3, d_six4},      // 0000 + 0110 = 0110  (not in COI)
      {d_v3sc1pv3pv1, d_sev4},   // 0110 + 0001 = 0111 (not in COI)
      {d_root1, d_one1},         // 1101 <s 0000 = 1
      {d_root2, d_zero1},        // 0111 == 1111 = 0 (not in COI)
  };
  for (auto& p : ass_up_v2)
  {
    ASSERT_EQ(d_ls->get_assignment(p.first).compare(p.second), 0);
  }

  /* v3 -> 0001 */
  update_cone(d_v3, d_one4);
  std::map<uint32_t, BitVector> ass_up_v3 = {
      {d_c1, d_ten4},            // 1010
      {d_v1, d_one4},            // 0001
      {d_v2, d_sev4},            // 0111
      {d_v3, d_one4},            // 0001
      {d_v1pc1, d_ele4},         // 0001 + 1010 = 1011 (not in COI)
      {d_v1pc1mv2, d_thi4},      // 1011 * 0111 = 1101 (not in COI)
      {d_v1pv2, d_egt4},         // 0001 + 0111 = 1000 (not in COI)
      {d_v1pv2av2, d_zero4},     // 1000 & 0111 = 0000 (not in COI)
      {d_v1e, d_one1},           // 0001[0:0] = 1 (not in COI)
      {d_v3e, d_one1},           // 0001[0:0] = 1
      {d_v1edv3e, d_one1},       // 1 / 1 = 1
      {d_v1edv3e_ext, d_ones4},  // sext(1, 3) = 1111
      {d_v3sc1, d_zero4},        // 0001 << 1010 = 0000
      {d_v3sc1pv3, d_one4},      // 0000 + 0001 = 0001
      {d_v3sc1pv3pv1, d_two4},   // 0001 + 0001 = 0010
      {d_root1, d_one1},         // 1101 <s 0000 = 1 (not in COI)
      {d_root2, d_zero1},        // 0010 == 1111 = 0
  };
  for (auto& p : ass_up_v3)
  {
    ASSERT_EQ(d_ls->get_assignment(p.first).compare(p.second), 0);
  }
}

TEST_F(TestLsBv, move_add)
{
  test_move_binary(NodeKind::BV_ADD, 0);
  test_move_binary(NodeKind::BV_ADD, 1);
}

TEST_F(TestLsBv, move_and)
{
  test_move_binary(NodeKind::BV_AND, 0);
  test_move_binary(NodeKind::BV_AND, 1);
}

TEST_F(TestLsBv, move_concat)
{
  test_move_binary(NodeKind::BV_CONCAT, 0);
  test_move_binary(NodeKind::BV_CONCAT, 1);
}

TEST_F(TestLsBv, move_eq)
{
  test_move_binary(NodeKind::EQ, 0);
  test_move_binary(NodeKind::EQ, 1);
}

TEST_F(TestLsBv, move_mul)
{
  test_move_binary(NodeKind::BV_MUL, 0);
  test_move_binary(NodeKind::BV_MUL, 1);
}

TEST_F(TestLsBv, move_shl)
{
  test_move_binary(NodeKind::BV_SHL, 0);
  test_move_binary(NodeKind::BV_SHL, 1);
}

TEST_F(TestLsBv, move_shr)
{
  test_move_binary(NodeKind::BV_SHR, 0);
  test_move_binary(NodeKind::BV_SHR, 1);
}

TEST_F(TestLsBv, move_ashr)
{
  test_move_binary(NodeKind::BV_ASHR, 0);
  test_move_binary(NodeKind::BV_ASHR, 1);
}

TEST_F(TestLsBv, move_udiv)
{
  test_move_binary(NodeKind::BV_UDIV, 0);
  test_move_binary(NodeKind::BV_UDIV, 1);
}

TEST_F(TestLsBv, move_ult)
{
  test_move_binary(NodeKind::BV_ULT, 0);
  test_move_binary(NodeKind::BV_ULT, 1);
}

TEST_F(TestLsBv, move_slt)
{
  test_move_binary(NodeKind::BV_SLT, 0);
  test_move_binary(NodeKind::BV_SLT, 1);
}

TEST_F(TestLsBv, move_urem)
{
  test_move_binary(NodeKind::BV_UREM, 0);
  test_move_binary(NodeKind::BV_UREM, 1);
}

TEST_F(TestLsBv, move_xor)
{
  test_move_binary(NodeKind::BV_XOR, 0);
  test_move_binary(NodeKind::BV_XOR, 1);
}

TEST_F(TestLsBv, ite)
{
  test_move_ite(0);
  test_move_ite(1);
  test_move_ite(2);
}

TEST_F(TestLsBv, not ) { test_move_not(); }

TEST_F(TestLsBv, extract) { test_move_extract(); }

TEST_F(TestLsBv, sext) { test_move_sext(); }

}  // namespace bzla::ls::test
