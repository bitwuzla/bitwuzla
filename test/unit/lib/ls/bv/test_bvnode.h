/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLALS__TEST__TEST_BVNODE_H
#define BZLALS__TEST__TEST_BVNODE_H

#include "bv/bitvector.h"
#include "ls/bv/bitvector_domain.h"
#include "ls/bv/bitvector_node.h"
#include "test_lib.h"

namespace bzla::ls::test {

class TestBvNodeCommon : public ::bzla::test::TestCommon
{
 protected:
  void SetUp() override
  {
    TestCommon::SetUp();
    gen_values(TEST_BW, d_values);
    gen_xvalues(TEST_BW, d_xvalues);
    d_rng.reset(new RNG(1234));
  }

  BitVector eval_op_binary(NodeKind op_kind,
                           const BitVector& x_val,
                           const BitVector& s_val,
                           uint32_t pos_x) const;

  static constexpr uint64_t TEST_BW = 4;
  std::vector<std::string> d_values;
  std::vector<std::string> d_xvalues;
  std::unique_ptr<RNG> d_rng;
  BitVector d_nullbv;
};

BitVector
TestBvNodeCommon::eval_op_binary(NodeKind op_kind,
                                 const BitVector& x_val,
                                 const BitVector& s_val,
                                 uint32_t pos_x) const
{
  BitVector res;
  switch (op_kind)
  {
    case NodeKind::BV_ADD:
      res = pos_x ? s_val.bvadd(x_val) : x_val.bvadd(s_val);
      break;
    case NodeKind::BV_AND:
      res = pos_x ? s_val.bvand(x_val) : x_val.bvand(s_val);
      break;
    case NodeKind::BV_ASHR:
      res = pos_x ? s_val.bvashr(x_val) : x_val.bvashr(s_val);
      break;
    case NodeKind::BV_CONCAT:
      res = pos_x ? s_val.bvconcat(x_val) : x_val.bvconcat(s_val);
      break;
    case NodeKind::EQ:
      res = pos_x ? s_val.bveq(x_val) : x_val.bveq(s_val);
      break;
    case NodeKind::BV_MUL:
      res = pos_x ? s_val.bvmul(x_val) : x_val.bvmul(s_val);
      break;
    case NodeKind::BV_SHL:
      res = pos_x ? s_val.bvshl(x_val) : x_val.bvshl(s_val);
      break;
    case NodeKind::BV_SHR:
      res = pos_x ? s_val.bvshr(x_val) : x_val.bvshr(s_val);
      break;
    case NodeKind::BV_SLT:
      res = pos_x ? s_val.bvslt(x_val) : x_val.bvslt(s_val);
      break;
    case NodeKind::BV_UDIV:
      res = pos_x ? s_val.bvudiv(x_val) : x_val.bvudiv(s_val);
      break;
    case NodeKind::BV_ULT:
      res = pos_x ? s_val.bvult(x_val) : x_val.bvult(s_val);
      break;
    case NodeKind::BV_UREM:
      res = pos_x ? s_val.bvurem(x_val) : x_val.bvurem(s_val);
      break;
    case NodeKind::BV_XOR:
      res = pos_x ? s_val.bvxor(x_val) : x_val.bvxor(s_val);
      break;
    default: assert(false);
  }
  return res;
}

/* -------------------------------------------------------------------------- */

class TestBvNode : public TestBvNodeCommon
{
 protected:
  enum Kind
  {
    CONS,
    INV,
    IS_CONS,
    IS_ESS,
    IS_INV,
  };
  enum BoundsKind
  {
    NONE,
    SIGNED,
    UNSIGNED,
    BOTH,
  };
  enum OptimizationKind
  {
    DEFAULT,
    CONCAT,
    SEXT,
  };

  bool check_sat_binary(Kind kind,
                        NodeKind op_kind,
                        BitVectorNode* op_x,
                        const BitVector& t,
                        const BitVector& s_val,
                        uint32_t pos_x,
                        OptimizationKind opt_kind = DEFAULT) const;
  bool check_sat_binary_cons(NodeKind op_kind,
                             const BitVector& x_val,
                             const BitVector& t,
                             uint64_t s_size,
                             uint32_t pos_x) const;
  bool check_sat_binary_is_ess(NodeKind op_kind,
                               const BitVector& x_val,
                               const BitVector& t,
                               const BitVectorDomain& s,
                               uint32_t pos_x) const;
  bool check_sat_ite(Kind kind,
                     const BitVectorDomain& x,
                     const BitVector& t,
                     const BitVector& s0_val,
                     const BitVector& s1_val,
                     uint32_t pos_x) const;
  bool check_sat_ite_cons(const BitVector& x_val,
                          const BitVector& t,
                          uint64_t s0_size,
                          uint64_t s1_size,
                          uint32_t pos_x) const;
  bool check_sat_ite_is_ess(const BitVector& x_val,
                            const BitVector& t,
                            const BitVectorDomain& s0,
                            const BitVector& s0_val_cur,
                            const BitVectorDomain& s1,
                            const BitVector& s1_val_cur,
                            uint32_t pos_x) const;
  bool check_sat_not(Kind kind,
                     const BitVectorDomain& x,
                     const BitVector& t) const;
  bool check_sat_extract(Kind kind,
                         const BitVectorDomain& x,
                         const BitVector& t,
                         uint64_t hi,
                         uint64_t lo) const;
  bool check_sat_sext(Kind kind,
                      const BitVectorDomain& x,
                      const BitVector& t,
                      uint64_t n) const;

  template <class T>
  void test_binary(Kind kind,
                   NodeKind op_kind,
                   uint32_t pos_x,
                   BoundsKind bounds_kind    = NONE,
                   OptimizationKind opt_kind = DEFAULT);
  void test_ite(Kind kind, uint32_t pos_x);
  void test_not(Kind kind);
  void test_extract(Kind kind);
  void test_sext(Kind kind);

  void test_normalize_bounds_no_u();
  void test_normalize_bounds_no_s();
  void test_normalize_bounds_only_hi();
  void test_normalize_bounds_only_lo();
  void test_normalize_bounds_both();

 protected:
  void test_normalize_bounds(const BitVector& min_u,
                             bool min_u_is_excl,
                             const BitVector& max_u,
                             bool max_u_is_excl,
                             const BitVector& min_s,
                             bool min_s_is_excl,
                             const BitVector& max_s,
                             bool max_s_is_excl,
                             const BitVector& min_lo_exp,
                             const BitVector& min_hi_exp,
                             const BitVector& max_lo_exp,
                             const BitVector& max_hi_exp);
};

bool
TestBvNode::check_sat_binary(Kind kind,
                             NodeKind op_kind,
                             BitVectorNode* op_x,
                             const BitVector& t,
                             const BitVector& s_val,
                             uint32_t pos_x,
                             OptimizationKind opt_kind) const
{
  BitVector* min_u = op_x->min_u();
  BitVector* max_u = op_x->max_u();
  BitVector* min_s = op_x->min_s();
  BitVector* max_s = op_x->max_s();

  assert(!min_u || max_u);
  assert(!min_s || max_s);

  const BitVectorDomain& x = op_x->domain();

  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector res;
    BitVector x_val = gen.has_next() ? gen.next() : x.lo();
    if (kind == IS_CONS)
    {
      assert(!min_u && !max_u && !min_s && !max_s);
      BitVectorDomainGenerator gens(s_val.size());
      while (gens.has_next())
      {
        res = eval_op_binary(op_kind, x_val, gens.next(), pos_x);
        if (t.compare(res) == 0) return true;
      }
    }
    else
    {
      assert(kind == IS_INV);
      if (opt_kind == OptimizationKind::SEXT)
      {
        uint64_t n = static_cast<BitVectorSignExtend*>(op_x)->get_n();
        if (n > 0)
        {
          uint64_t bw_x  = op_x->size();
          uint64_t bw_xx = bw_x - n;
          BitVector xn   = x_val.bvextract(bw_x - 1, bw_xx);
          BitVector xx   = x_val.bvextract(bw_xx - 1, 0);
          if (!xn.is_zero() && !xn.is_ones()) continue;
          if (xn.is_zero() && !xx.bvextract(bw_xx - 1, bw_xx - 1).is_zero())
            continue;
          if (xn.is_ones() && !xx.bvextract(bw_xx - 1, bw_xx - 1).is_ones())
            continue;
        }
      }
      res = eval_op_binary(op_kind, x_val, s_val, pos_x);
      if (t.compare(res) == 0)
      {
        if (min_u && max_u && min_s && max_s)
        {
          if (x_val.compare(*min_u) >= 0 && x_val.signed_compare(*min_s) >= 0
              && x_val.compare(*max_u) <= 0
              && x_val.signed_compare(*max_s) <= 0)
          {
            return true;
          }
        }
        else if (min_u && max_u)
        {
          if (x_val.compare(*min_u) >= 0 && x_val.compare(*max_u) <= 0)
          {
            return true;
          }
        }
        else if (min_s && max_s)
        {
          if (x_val.signed_compare(*min_s) >= 0
              && x_val.signed_compare(*max_s) <= 0)
          {
            return true;
          }
        }
        else
        {
          return true;
        }
      }
    }
  } while (gen.has_next());
  return false;
}

bool
TestBvNode::check_sat_binary_cons(NodeKind op_kind,
                                  const BitVector& x_val,
                                  const BitVector& t,
                                  uint64_t s_size,
                                  uint32_t pos_x) const
{
  BitVectorDomain s(s_size);
  BitVectorDomainGenerator gen(s);
  do
  {
    BitVector res;
    BitVector s_val = gen.next();
    res             = eval_op_binary(op_kind, x_val, s_val, pos_x);
    if (t.compare(res) == 0) return true;
  } while (gen.has_next());
  return false;
}

bool
TestBvNode::check_sat_binary_is_ess(NodeKind op_kind,
                                    const BitVector& x_val,
                                    const BitVector& t,
                                    const BitVectorDomain& s,
                                    uint32_t pos_x) const
{
  BitVectorDomainGenerator gen(s);
  do
  {
    BitVector s_val = gen.has_next() ? gen.next() : s.lo();
    BitVector res   = eval_op_binary(op_kind, x_val, s_val, pos_x);
    if (t.compare(res) == 0) return false;
  } while (gen.has_next());
  return true;
}

bool
TestBvNode::check_sat_ite(Kind kind,
                          const BitVectorDomain& x,
                          const BitVector& t,
                          const BitVector& s0_val,
                          const BitVector& s1_val,
                          uint32_t pos_x) const
{
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector x_val = gen.has_next() ? gen.next() : x.lo();
    if (pos_x == 0)
    {
      if (kind == IS_CONS)
      {
        BitVectorDomainGenerator gens0(s0_val.size());
        while (gens0.has_next())
        {
          BitVector s0val = gens0.next();
          BitVectorDomainGenerator gens1(s1_val.size());
          while (gens1.has_next())
          {
            BitVector res = BitVector::bvite(x_val, s0val, gens1.next());
            if (t.compare(res) == 0) return true;
          }
        }
      }
      else
      {
        assert(kind == IS_INV);
        BitVector res = BitVector::bvite(x_val, s0_val, s1_val);
        if (t.compare(res) == 0) return true;
      }
    }
    else if (pos_x == 1)
    {
      if (kind == IS_CONS)
      {
        BitVectorDomainGenerator gens0(s0_val.size());
        while (gens0.has_next())
        {
          BitVector s0val = gens0.next();
          BitVectorDomainGenerator gens1(s1_val.size());
          while (gens1.has_next())
          {
            BitVector res = BitVector::bvite(s0val, x_val, gens1.next());
            if (t.compare(res) == 0) return true;
          }
        }
      }
      else
      {
        assert(kind == IS_INV);
        if (s0_val.is_false() && s1_val.compare(t) != 0) return false;
        BitVector res = BitVector::bvite(s0_val, x_val, s1_val);
        if (t.compare(res) == 0) return true;
      }
    }
    else
    {
      if (kind == IS_CONS)
      {
        BitVectorDomainGenerator gens0(s0_val.size());
        while (gens0.has_next())
        {
          BitVector s0val = gens0.next();
          BitVectorDomainGenerator gens1(s1_val.size());
          while (gens1.has_next())
          {
            BitVector res = BitVector::bvite(s0val, gens1.next(), x_val);
            if (t.compare(res) == 0) return true;
          }
        }
      }
      else
      {
        assert(kind == IS_INV);
        if (s0_val.is_true() && s1_val.compare(t) != 0) return false;
        BitVector res = BitVector::bvite(s0_val, s1_val, x_val);
        if (t.compare(res) == 0) return true;
      }
    }
  } while (gen.has_next());
  return false;
}

bool
TestBvNode::check_sat_ite_is_ess(const BitVector& x_val,
                                 const BitVector& t,
                                 const BitVectorDomain& s0,
                                 const BitVector& s0_val_cur,
                                 const BitVectorDomain& s1,
                                 const BitVector& s1_val_cur,
                                 uint32_t pos_x) const
{
  BitVectorDomainGenerator gens0(s0);
  BitVectorDomainGenerator gens1(s1);
  do
  {
    BitVector s0_val = gens0.has_next() ? gens0.next() : s0.lo();
    BitVectorDomainGenerator gens1(s1);
    BitVector res;
    if (pos_x == 0)
    {
      res = BitVector::bvite(x_val, s0_val, s1_val_cur);
    }
    else if (pos_x == 1)
    {
      res = BitVector::bvite(s0_val, x_val, s1_val_cur);
    }
    else
    {
      res = BitVector::bvite(s0_val, s1_val_cur, x_val);
    }
    if (t.compare(res) == 0) return false;
  } while (gens0.has_next());
  do
  {
    BitVector s1_val = gens1.has_next() ? gens1.next() : s1.lo();
    BitVectorDomainGenerator gens1(s1);
    BitVector res;
    if (pos_x == 0)
    {
      res = BitVector::bvite(x_val, s0_val_cur, s1_val);
    }
    else if (pos_x == 1)
    {
      res = BitVector::bvite(s0_val_cur, x_val, s1_val);
    }
    else
    {
      res = BitVector::bvite(s0_val_cur, s1_val, x_val);
    }
    if (t.compare(res) == 0) return false;
  } while (gens1.has_next());
  return true;
}

bool
TestBvNode::check_sat_ite_cons(const BitVector& x_val,
                               const BitVector& t,
                               uint64_t s0_size,
                               uint64_t s1_size,
                               uint32_t pos_x) const
{
  BitVectorDomainGenerator gens0(s0_size);
  while (gens0.has_next())
  {
    BitVector s0val = gens0.next();
    BitVectorDomainGenerator gens1(s1_size);
    while (gens1.has_next())
    {
      BitVector res;
      if (pos_x == 0)
      {
        res = BitVector::bvite(x_val, s0val, gens1.next());
      }
      else if (pos_x == 1)
      {
        res = BitVector::bvite(s0val, x_val, gens1.next());
      }
      else
      {
        res = BitVector::bvite(s0val, gens1.next(), x_val);
      }
      if (t.compare(res) == 0) return true;
    }
  }
  return false;
}

bool
TestBvNode::check_sat_not(Kind kind,
                          const BitVectorDomain& x,
                          const BitVector& t) const
{
  assert(kind == IS_CONS || kind == IS_ESS || kind == IS_INV);
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res = val.bvnot();
    if (t.compare(res) == 0) return kind == IS_ESS ? false : true;
  } while (gen.has_next());
  return kind == IS_ESS ? true : false;
}

bool
TestBvNode::check_sat_extract(Kind kind,
                              const BitVectorDomain& x,
                              const BitVector& t,
                              uint64_t hi,
                              uint64_t lo) const
{
  assert(kind == IS_CONS || kind == IS_ESS || kind == IS_INV);
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res = val.bvextract(hi, lo);
    if (t.compare(res) == 0) return kind == IS_ESS ? false : true;
  } while (gen.has_next());
  return kind == IS_ESS ? true : false;
}

bool
TestBvNode::check_sat_sext(Kind kind,
                           const BitVectorDomain& x,
                           const BitVector& t,
                           uint64_t n) const
{
  assert(kind == IS_CONS || kind == IS_ESS || kind == IS_INV);
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res = val.bvsext(n);
    if (t.compare(res) == 0) return kind == IS_ESS ? false : true;
  } while (gen.has_next());
  return kind == IS_ESS ? true : false;
}

template <class T>
void
TestBvNode::test_binary(Kind kind,
                        NodeKind op_kind,
                        uint32_t pos_x,
                        TestBvNode::BoundsKind bounds_kind,
                        OptimizationKind opt_kind)
{
  uint64_t bw_x = TEST_BW;
  uint64_t bw_s = TEST_BW;
  uint64_t bw_t = TEST_BW;

  if (op_kind == NodeKind::BV_ULT || op_kind == NodeKind::BV_SLT
      || op_kind == NodeKind::EQ)
  {
    bw_t = 1;
  }
  else if (op_kind == NodeKind::BV_CONCAT)
  {
    bw_s = 2; /* decrease number of tests for concat */
    bw_t = bw_s + bw_x;
  }

  uint64_t nval_x = 1 << bw_x;
  uint64_t nval_s = 1 << bw_s;
  uint64_t nval_t = 1 << bw_t;

  if (kind == IS_ESS)
  {
    std::vector<std::string> svalues;
    if (op_kind == NodeKind::BV_CONCAT)
    {
      gen_xvalues(bw_s, svalues);
    }
    else
    {
      svalues = d_xvalues;
    }

    for (const std::string& s_value : svalues)
    {
      BitVectorDomain s(s_value);
      for (uint64_t i = 0; i < nval_x; i++)
      {
        BitVector x_val = BitVector::from_ui(bw_x, i);
        for (uint64_t j = 0; j < nval_t; j++)
        {
          /* Target value of the operation (op). */
          BitVector t = BitVector::from_ui(bw_t, j);
          /* For this test, we don't care about the current assignment of s,
           * thus we initialize it with a random value that matches constant
           * bits in s. */
          BitVector s_val = s.lo();
          if (!s.is_fixed())
          {
            BitVectorDomainGenerator gen(s, d_rng.get());
            s_val = gen.random();
          }
          /* For this test, the domain of x is irrelevant, hence we
           * initialize it with an unconstrained domain. */
          std::unique_ptr<BitVectorNode> op_x(
              new BitVectorNode(d_rng.get(), x_val, BitVectorDomain(bw_x)));
          std::unique_ptr<BitVectorNode> op_s(
              new BitVectorNode(d_rng.get(), s_val, s));
          /* For this test, we don't care about current assignment and domain of
           * the op, thus we initialize them with 0 and x..x, respectively. */
          T op(d_rng.get(),
               bw_t,
               pos_x == 0 ? op_x.get() : op_s.get(),
               pos_x == 1 ? op_x.get() : op_s.get());
          bool res    = op.is_essential(t, pos_x);
          bool status = check_sat_binary_is_ess(op_kind, x_val, t, s, pos_x);
          if (res != status)
          {
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "t: " << t << std::endl;
            std::cout << "x: " << x_val << std::endl;
            std::cout << "s: " << s << ": " << s_val << std::endl;
          }
          ASSERT_EQ(res, status);
        }
      }
    }
  }
  else
  {
    for (const std::string& x_value : d_xvalues)
    {
      BitVectorDomain x(x_value);
      for (uint64_t i = 0; i < nval_s; i++)
      {
        /* Assignment of the other operand. */
        BitVector s_val = BitVector::from_ui(bw_s, i);
        for (uint64_t j = 0; j < nval_t; j++)
        {
          /* Target value of the operation (op). */
          BitVector t = BitVector::from_ui(bw_t, j);
          /* For this test, we don't care about the current assignment of x,
           * thus we initialize it with a random value that matches constant
           * bits in x. */
          BitVector x_val = x.lo();
          if (!x.is_fixed())
          {
            BitVectorDomainGenerator gen(x, d_rng.get());
            x_val = gen.random();
          }

          bool use_bounds  = bounds_kind != NONE;
          uint32_t n_tests = 0;
          BitVector min, max;
          do
          {
            std::unique_ptr<BitVectorNode> op_x;
            std::unique_ptr<BitVectorNode> child0, child1;
            if (opt_kind == CONCAT)
            {
              uint64_t bw_x0 = d_rng->pick<uint64_t>(1, bw_x - 1);
              uint64_t bw_x1 = bw_x - bw_x0;
              child0.reset(new BitVectorNode(d_rng.get(), bw_x0));
              child1.reset(new BitVectorNode(d_rng.get(), bw_x1));
              op_x.reset(new BitVectorConcat(
                  d_rng.get(), x, child0.get(), child1.get()));
              op_x->set_assignment(x_val);
            }
            else if (opt_kind == SEXT)
            {
              uint64_t n     = d_rng->pick<uint64_t>(0, bw_x - 1);
              uint64_t bw_xx = bw_x - n;
              child0.reset(new BitVectorNode(d_rng.get(), bw_xx));
              op_x.reset(
                  new BitVectorSignExtend(d_rng.get(), x, child0.get(), n));
              op_x->set_assignment(x_val);
            }
            else
            {
              op_x.reset(new BitVectorNode(d_rng.get(), x_val, x));
            }
            /* For this test, we don't care about the domain of s, thus we
             * initialize it with an unconstrained domain. */
            BitVectorDomain s(bw_s);
            std::unique_ptr<BitVectorNode> op_s(
                new BitVectorNode(d_rng.get(), s_val, s));
            /* For this test, we don't care about current assignment and domain
             * of the op, thus we initialize them with 0 and x..x,
             * respectively. */
            std::unique_ptr<BitVectorNode> op;
            if (opt_kind == DEFAULT)
            {
              op.reset(new T(d_rng.get(),
                             bw_t,
                             pos_x == 0 ? op_x.get() : op_s.get(),
                             pos_x == 1 ? op_x.get() : op_s.get()));
            }
            else
            {
              if (op_kind == NodeKind::BV_ULT)
              {
                op.reset(
                    new BitVectorUlt(d_rng.get(),
                                     bw_t,
                                     pos_x == 0 ? op_x.get() : op_s.get(),
                                     pos_x == 1 ? op_x.get() : op_s.get(),
                                     opt_kind == CONCAT || opt_kind == SEXT));
              }
              else
              {
                assert(op_kind == NodeKind::BV_SLT);
                op.reset(
                    new BitVectorSlt(d_rng.get(),
                                     bw_t,
                                     pos_x == 0 ? op_x.get() : op_s.get(),
                                     pos_x == 1 ? op_x.get() : op_s.get(),
                                     opt_kind == CONCAT || opt_kind == SEXT));
              }
            }

            if (bounds_kind != NONE)
            {
              bool is_signed = bounds_kind == SIGNED;
              min            = BitVector(bw_x, *d_rng.get());
              if (is_signed)
              {
                max = BitVector(bw_x,
                                *d_rng.get(),
                                min,
                                is_signed ? BitVector::mk_max_signed(bw_x)
                                          : BitVector::mk_ones(bw_x),
                                is_signed);
              }
              else
              {
                max = BitVector(
                    bw_x, *d_rng.get(), min, BitVector::mk_ones(bw_x), false);
                if (bounds_kind == BOTH)
                {
                  op_x->update_bounds(min, max, false, false, false);
                  is_signed = true;
                  min       = BitVector(bw_x, *d_rng.get());
                  max       = BitVector(bw_x,
                                  *d_rng.get(),
                                  min,
                                  BitVector::mk_max_signed(bw_x),
                                  is_signed);
                }
              }
              op_x->update_bounds(min, max, false, false, is_signed);
            }

            if (kind == IS_CONS || kind == IS_INV)
            {
              bool res    = kind == IS_INV ? op->is_invertible(t, pos_x)
                                           : op->is_consistent(t, pos_x);
              bool status = check_sat_binary(
                  kind, op_kind, op_x.get(), t, s_val, pos_x, opt_kind);
              if (res != status)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "s: " << s_val << std::endl;
                if (opt_kind != DEFAULT && op_x->kind() == NodeKind::BV_SEXT)
                {
                  std::cout
                      << "n: "
                      << static_cast<BitVectorSignExtend*>(op_x.get())->get_n()
                      << std::endl;
                }
                std::cout << "min_u: "
                          << (op_x->min_u() ? op_x->min_u()->str() : "(nil)")
                          << std::endl;
                std::cout << "max_u: "
                          << (op_x->max_u() ? op_x->max_u()->str() : "(nil)")
                          << std::endl;
                std::cout << "min_s: "
                          << (op_x->min_s() ? op_x->min_s()->str() : "(nil)")
                          << std::endl;
                std::cout << "max_s: "
                          << (op_x->max_s() ? op_x->max_s()->str() : "(nil)")
                          << std::endl;
              }
              assert(res == status);
              ASSERT_EQ(res, status);
            }
            else if (kind == INV)
            {
              if (!op->is_invertible(t, pos_x)) continue;
              BitVector inv = op->inverse_value(t, pos_x);
              int32_t cmp =
                  t.compare(eval_op_binary(op_kind, inv, s_val, pos_x));
              if (cmp != 0)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "s: " << s_val << std::endl;
                std::cout << "inverse: " << inv << std::endl;
              }
              ASSERT_EQ(cmp, 0);
              ASSERT_TRUE(op->is_consistent(t, pos_x));
            }
            else
            {
              assert(kind == CONS);
              if (!op->is_consistent(t, pos_x)) continue;
              BitVector cons = op->consistent_value(t, pos_x);
              bool status =
                  check_sat_binary_cons(op_kind, cons, t, s_val.size(), pos_x);
              if (!status)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "consistent: " << cons << std::endl;
              }
              ASSERT_TRUE(status);
            }
          } while (use_bounds && ++n_tests < 10);
        }
      }
    }
  }
}

void
TestBvNode::test_ite(Kind kind, uint32_t pos_x)
{
  uint64_t bw_s0, bw_s1, bw_x, bw_t = TEST_BW;
  uint64_t n_vals, n_vals_s0, n_vals_s1;

  if (pos_x)
  {
    bw_x  = TEST_BW;
    bw_s0 = 1;
    bw_s1 = TEST_BW;
  }
  else
  {
    bw_x  = 1;
    bw_s0 = TEST_BW;
    bw_s1 = TEST_BW;
  }
  n_vals    = 1 << bw_x;
  n_vals_s0 = 1 << bw_s0;
  n_vals_s1 = 1 << bw_s1;

  if (kind == IS_ESS)
  {
    std::vector<std::string> s0_values, s1_values;
    if (pos_x)
    {
      s0_values.push_back("x");
      s0_values.push_back("0");
      s0_values.push_back("1");
    }
    else
    {
      s0_values = d_xvalues;
    }
    s1_values = d_xvalues;

    for (const std::string& s0_value : s0_values)
    {
      BitVectorDomain s0(s0_value);
      for (const std::string& s1_value : s1_values)
      {
        BitVectorDomain s1(s1_value);
        for (uint64_t i = 0; i < n_vals; i++)
        {
          BitVector x_val = BitVector::from_ui(bw_x, i);
          for (uint64_t j = 0; j < n_vals; j++)
          {
            BitVector t = BitVector::from_ui(bw_t, j);
            /* For this test, the domain of x is irrelevant, hence we
             * initialize it with an unconstrained domain. */
            std::unique_ptr<BitVectorNode> op_x(
                new BitVectorNode(d_rng.get(), x_val, BitVectorDomain(bw_x)));
            /* For this test, we don't care about the current assignment of s0
             * and s1, hence we use a random value. */
            BitVector s0_val = s0.lo(), s1_val = s1.lo();
            if (!s0.is_fixed())
            {
              BitVectorDomainGenerator gen(s0, d_rng.get());
              s0_val = gen.random();
            }
            if (!s1.is_fixed())
            {
              BitVectorDomainGenerator gen(s1, d_rng.get());
              s1_val = gen.random();
            }
            std::unique_ptr<BitVectorNode> op_s0(
                new BitVectorNode(d_rng.get(), s0_val, s0));
            std::unique_ptr<BitVectorNode> op_s1(
                new BitVectorNode(d_rng.get(), s1_val, s1));
            /* For this test, we don't care about current assignment and domain
             * of the op, thus we initialize them with 0 and x..x,
             * respectively. */
            BitVectorIte op(d_rng.get(),
                            bw_t,
                            pos_x == 0 ? op_x.get() : op_s0.get(),
                            pos_x == 1
                                ? op_x.get()
                                : (pos_x == 2 ? op_s1.get() : op_s0.get()),
                            pos_x == 2 ? op_x.get() : op_s1.get());
            bool res = op.is_essential(t, pos_x);
            bool status =
                check_sat_ite_is_ess(x_val, t, s0, s0_val, s1, s1_val, pos_x);
            if (res != status)
            {
              std::cout << "pos_x: " << pos_x << std::endl;
              std::cout << "t: " << t << std::endl;
              std::cout << "x: " << x_val << std::endl;
              std::cout << "s0: " << s0 << ": " << s0_val << std::endl;
              std::cout << "s1: " << s1 << ": " << s1_val << std::endl;
            }
            ASSERT_EQ(res, status);
          }
        }
      }
    }
  }
  else
  {
    std::vector<std::string> x_values;
    if (pos_x)
    {
      x_values = d_xvalues;
    }
    else
    {
      x_values.push_back("x");
      x_values.push_back("0");
      x_values.push_back("1");
    }

    for (const std::string& x_value : x_values)
    {
      BitVectorDomain x(x_value);
      for (uint64_t i = 0; i < n_vals_s0; i++)
      {
        BitVector s0_val = BitVector::from_ui(bw_s0, i);
        for (uint64_t j = 0; j < n_vals_s1; j++)
        {
          BitVector s1_val = BitVector::from_ui(bw_s1, j);
          for (uint64_t k = 0; k < n_vals; k++)
          {
            BitVector t = BitVector::from_ui(bw_t, k);

            /* For this test, we don't care about the current assignment of x,
             * thus we initialize it with a random value that matches constant
             * bits in x. */
            BitVector x_val = x.lo();
            if (!x.is_fixed())
            {
              BitVectorDomainGenerator gen(x, d_rng.get());
              x_val = gen.random();
            }
            std::unique_ptr<BitVectorNode> op_x(
                new BitVectorNode(d_rng.get(), x_val, x));
            /* For this test, we don't care about the domains of s0 and s1,
             * hence we initialize them with unconstrained domains. */
            std::unique_ptr<BitVectorNode> op_s0(
                new BitVectorNode(d_rng.get(), s0_val, BitVectorDomain(bw_s0)));
            std::unique_ptr<BitVectorNode> op_s1(
                new BitVectorNode(d_rng.get(), s1_val, BitVectorDomain(bw_s1)));
            /* For this test, we don't care about current assignment and domain
             * of the op, thus we initialize them with 0 and x..x,
             * respectively. */
            BitVectorIte op(d_rng.get(),
                            bw_t,
                            pos_x == 0 ? op_x.get() : op_s0.get(),
                            pos_x == 1
                                ? op_x.get()
                                : (pos_x == 2 ? op_s1.get() : op_s0.get()),
                            pos_x == 2 ? op_x.get() : op_s1.get());

            if (kind == IS_INV || kind == IS_CONS)
            {
              bool res    = kind == IS_INV ? op.is_invertible(t, pos_x)
                                           : op.is_consistent(t, pos_x);
              bool status = check_sat_ite(kind, x, t, s0_val, s1_val, pos_x);
              if (res != status)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "s0: " << s0_val << std::endl;
                std::cout << "s1: " << s1_val << std::endl;
              }
              ASSERT_EQ(res, status);
            }
            else if (kind == INV)
            {
              if (x.is_fixed()) continue;
              if (!op.is_invertible(t, pos_x)) continue;
              BitVector inv = op.inverse_value(t, pos_x);
              int32_t cmp;
              if (pos_x == 0)
              {
                cmp = t.compare(BitVector::bvite(inv, s0_val, s1_val));
              }
              else if (pos_x == 1)
              {
                cmp = t.compare(BitVector::bvite(s0_val, inv, s1_val));
              }
              else
              {
                cmp = t.compare(BitVector::bvite(s0_val, s1_val, inv));
              }
              if (cmp != 0)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "s0: " << s0_val << std::endl;
                std::cout << "s1: " << s1_val << std::endl;
                std::cout << "inverse: " << inv << std::endl;
              }
              ASSERT_EQ(cmp, 0);
              ASSERT_TRUE(op.is_consistent(t, pos_x));
            }
            else
            {
              assert(kind == CONS);
              if (x.is_fixed()) continue;
              if (!op.is_consistent(t, pos_x)) continue;
              BitVector cons = op.consistent_value(t, pos_x);
              bool status    = check_sat_ite_cons(
                  cons, t, s0_val.size(), s1_val.size(), pos_x);
              if (!status)
              {
                std::cout << "pos_x: " << pos_x << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "consistent: " << cons << std::endl;
              }
              ASSERT_TRUE(status);
            }
          }
        }
      }
    }
  }
}

void
TestBvNode::test_not(Kind kind)
{
  for (const std::string& x_value : d_xvalues)
  {
    BitVectorDomain x(x_value);
    uint64_t bw_t = x.size();
    for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
    {
      BitVector t = BitVector::from_ui(bw_t, i);
      /* For this test, we don't care about the current assignment of x,
       * thus we initialize it with a random value that matches constant
       * bits in x. */
      BitVector x_val = x.lo();
      if (!x.is_fixed())
      {
        BitVectorDomainGenerator gen(x, d_rng.get());
        x_val = gen.random();
      }
      std::unique_ptr<BitVectorNode> op_x(
          new BitVectorNode(d_rng.get(), x_val, x));
      /* For this test, we don't care about current assignment and domain
       * of the op, thus we initialize them with 0 and 'x..x',
       * respectively. */
      BitVectorNot op(d_rng.get(), bw_t, op_x.get());

      if (kind == IS_CONS || kind == IS_ESS || kind == IS_INV)
      {
        bool res    = kind == IS_ESS ? op.is_essential(t, 0)
                                     : (kind == IS_INV ? op.is_invertible(t, 0)
                                                       : op.is_consistent(t, 0));
        bool status = check_sat_not(kind, x, t);

        if (res != status)
        {
          std::cout << "t: " << t << std::endl;
          std::cout << "x: " << x_value << ": " << x_val << std::endl;
        }
        ASSERT_EQ(res, status);
      }
      else
      {
        assert(kind == INV || kind == CONS);
        if (x.is_fixed()) continue;
        if (kind == INV && !op.is_invertible(t, 0)) continue;
        if (kind == CONS && !op.is_consistent(t, 0)) continue;

        if (kind == INV)
        {
          BitVector inv = op.inverse_value(t, 0);
          int32_t cmp   = t.compare(inv.bvnot());
          if (cmp != 0)
          {
            std::cout << "t: " << t << std::endl;
            std::cout << "x: " << x_value << ": " << x_val << std::endl;
            std::cout << "inverse: " << inv << std::endl;
          }
          ASSERT_EQ(cmp, 0);
        }
        else
        {
          BitVector cons = op.consistent_value(t, 0);
          int32_t cmp    = t.compare(cons.bvnot());
          if (cmp != 0)
          {
            std::cout << "t: " << t << std::endl;
            std::cout << "x: " << x_value << ": " << x_val << std::endl;
            std::cout << "consistent: " << cons << std::endl;
          }
          ASSERT_EQ(cmp, 0);
        }
        ASSERT_TRUE(op.is_consistent(t, 0));
      }
    }
  }
}

void
TestBvNode::test_extract(Kind kind)
{
  uint64_t bw_x = TEST_BW;

  for (const std::string& x_value : d_xvalues)
  {
    BitVectorDomain x(x_value);
    for (uint64_t lo = 0; lo < bw_x; ++lo)
    {
      for (uint64_t hi = lo; hi < bw_x; ++hi)
      {
        uint64_t bw_t = hi - lo + 1;
        for (uint64_t i = 0, n = 1 << bw_t; i < n; ++i)
        {
          BitVector t = BitVector::from_ui(bw_t, i);
          /* For this test, we don't care about the current assignment of x,
           * thus we initialize it with a random value that matches constant
           * bits in x. */
          BitVector x_val = x.lo();
          if (!x.is_fixed())
          {
            BitVectorDomainGenerator gen(x, d_rng.get());
            x_val = gen.random();
          }
          std::unique_ptr<BitVectorNode> op_x(
              new BitVectorNode(d_rng.get(), x_val, x));
          /* For this test, we don't care about current assignment and domain
           * of the op, thus we initialize them with 0 and 'x..x',
           * respectively. */
          BitVectorExtract op(d_rng.get(), bw_t, op_x.get(), hi, lo, false);

          if (kind == IS_CONS || kind == IS_ESS || kind == IS_INV)
          {
            bool res    = kind == IS_ESS
                              ? op.is_essential(t, 0)
                              : (kind == IS_INV ? op.is_invertible(t, 0)
                                                : op.is_consistent(t, 0));
            bool status = check_sat_extract(kind, x, t, hi, lo);

            if (res != status)
            {
              std::cout << "hi: " << hi << std::endl;
              std::cout << "lo: " << lo << std::endl;
              std::cout << "t: " << t << std::endl;
              std::cout << "x: " << x_value << ": " << x_val << std::endl;
            }
            ASSERT_EQ(res, status);
          }
          else
          {
            assert(kind == INV || kind == CONS);
            if (x.is_fixed()) continue;
            if (kind == INV && !op.is_invertible(t, 0)) continue;
            if (kind == CONS && !op.is_consistent(t, 0)) continue;

            if (kind == INV)
            {
              BitVector inv = op.inverse_value(t, 0);
              int32_t cmp   = t.compare(inv.bvextract(hi, lo));
              if (cmp != 0)
              {
                std::cout << "hi: " << hi << std::endl;
                std::cout << "lo: " << lo << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "inverse: " << inv << std::endl;
              }
              ASSERT_EQ(cmp, 0);
            }
            else
            {
              BitVector cons = op.consistent_value(t, 0);
              int32_t cmp    = t.compare(cons.bvextract(hi, lo));
              if (cmp != 0)
              {
                std::cout << "hi: " << hi << std::endl;
                std::cout << "lo: " << lo << std::endl;
                std::cout << "t: " << t << std::endl;
                std::cout << "x: " << x_value << ": " << x_val << std::endl;
                std::cout << "consistent: " << cons << std::endl;
              }
              ASSERT_EQ(cmp, 0);
            }
            ASSERT_TRUE(op.is_consistent(t, 0));
          }
        }
      }
    }
  }
}

void
TestBvNode::test_sext(Kind kind)
{
  uint64_t bw_x = TEST_BW;

  for (const std::string& x_value : d_xvalues)
  {
    BitVectorDomain x(x_value);
    for (uint64_t n = 1; n <= bw_x; ++n)
    {
      uint64_t bw_t = bw_x + n;
      for (uint64_t i = 0, m = 1 << bw_t; i < m; ++i)
      {
        BitVector t = BitVector::from_ui(bw_t, i);
        /* For this test, we don't care about the current assignment of x,
         * thus we initialize it with a random value that matches constant
         * bits in x. */
        BitVector x_val = x.lo();
        if (!x.is_fixed())
        {
          BitVectorDomainGenerator gen(x, d_rng.get());
          x_val = gen.random();
        }
        std::unique_ptr<BitVectorNode> op_x(
            new BitVectorNode(d_rng.get(), x_val, x));
        /* For this test, we don't care about current assignment and domain
         * of the op, thus we initialize them with 0 and 'x..x',
         * respectively. */
        BitVectorSignExtend op(d_rng.get(), bw_t, op_x.get(), n);

        if (kind == IS_CONS || kind == IS_ESS || kind == IS_INV)
        {
          bool res    = kind == IS_ESS ? op.is_essential(t, 0)
                                       : (kind == IS_INV ? op.is_invertible(t, 0)
                                                         : op.is_consistent(t, 0));
          bool status = check_sat_sext(kind, x, t, n);

          if (res != status)
          {
            std::cout << "n: " << n << std::endl;
            std::cout << "t: " << t << std::endl;
            std::cout << "x: " << x_value << ": " << x_val << std::endl;
          }
          ASSERT_EQ(res, status);
        }
        else
        {
          assert(kind == INV || kind == CONS);
          if (x.is_fixed()) continue;
          if (kind == INV && !op.is_invertible(t, 0)) continue;
          if (kind == CONS && !op.is_consistent(t, 0)) continue;

          if (kind == INV)
          {
            BitVector inv = op.inverse_value(t, 0);
            int32_t cmp   = t.compare(inv.bvsext(n));
            if (cmp != 0)
            {
              std::cout << "n: " << n << std::endl;
              std::cout << "t: " << t << std::endl;
              std::cout << "x: " << x_value << ": " << x_val << std::endl;
              std::cout << "inverse: " << inv << std::endl;
            }
            ASSERT_EQ(cmp, 0);
          }
          else
          {
            BitVector cons = op.consistent_value(t, 0);
            int32_t cmp    = t.compare(cons.bvsext(n));
            if (cmp != 0)
            {
              std::cout << "n: " << n << std::endl;
              std::cout << "t: " << t << std::endl;
              std::cout << "x: " << x_value << ": " << x_val << std::endl;
              std::cout << "consistent: " << cons << std::endl;
            }
            ASSERT_EQ(cmp, 0);
          }
          ASSERT_TRUE(op.is_consistent(t, 0));
        }
      }
    }
  }
}
}  // namespace bzla::ls::test
#endif
