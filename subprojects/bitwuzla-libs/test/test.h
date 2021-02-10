#ifndef BZLALS__TEST__TEST_H
#define BZLALS__TEST__TEST_H

#include <cmath>
#include <string>

#include "bitvector.h"
#include "bitvector_domain.h"
#include "bitvector_op.h"
#include "gmpmpz.h"
#include "gmprandstate.h"
#include "gtest/gtest.h"
#include "rng.h"

namespace bzlals {
namespace test {

/* -------------------------------------------------------------------------- */

class TestCommon : public ::testing::Test
{
 protected:
  enum OpKind
  {
    ADD,
    AND,
    ASHR,
    CONCAT,
    DEC,
    EQ,
    IMPLIES,
    ITE,
    INC,
    MUL,
    NAND,
    NE,
    NEG,
    NOR,
    NOT,
    OR,
    REDAND,
    REDOR,
    SDIV,
    SEXT,
    SGT,
    SGE,
    SHL,
    SHR,
    SLT,
    SLE,
    SREM,
    SUB,
    UDIV,
    UGT,
    UGE,
    ULT,
    ULE,
    UREM,
    XNOR,
    XOR,
    ZEXT,
  };
};

/* -------------------------------------------------------------------------- */

class TestBvDomainCommon : public TestCommon
{
 protected:
  static void gen_all_combinations(size_t size,
                                   const std::vector<char>& bits,
                                   std::vector<std::string>& values);
  static void gen_xvalues(uint32_t bw, std::vector<std::string>& values);
  static void gen_values(uint32_t bw, std::vector<std::string>& values);
};

void
TestBvDomainCommon::gen_all_combinations(size_t size,
                                         const std::vector<char>& bits,
                                         std::vector<std::string>& values)
{
  size_t num_values;
  size_t num_bits = bits.size();
  std::vector<size_t> psizes;

  num_values = pow(num_bits, size);
  for (size_t i = 0; i < size; ++i)
  {
    psizes.push_back(num_values / pow(num_bits, i + 1));
  }

  /* Generate all combinations of 'bits'. */
  for (size_t row = 0; row < num_values; ++row)
  {
    std::string val;
    for (size_t col = 0; col < size; ++col)
    {
      val += bits[(row / psizes[col]) % num_bits];
    }
    values.push_back(val);
  }
}

void
TestBvDomainCommon::gen_xvalues(uint32_t bw, std::vector<std::string>& values)
{
  gen_all_combinations(bw, {'x', '0', '1'}, values);
}

void
TestBvDomainCommon::gen_values(uint32_t bw, std::vector<std::string>& values)
{
  gen_all_combinations(bw, {'0', '1'}, values);
}

/* -------------------------------------------------------------------------- */

class TestBvOp : public TestBvDomainCommon
{
 protected:
  enum Kind
  {
    IS_CONS,
    IS_INV,
  };

  void SetUp() override
  {
    TestBvDomainCommon::SetUp();
    gen_values(TEST_BW, d_values);
    gen_xvalues(TEST_BW, d_xvalues);
    d_rng.reset(new RNG(1234));
  }

  BitVector check_sat_binary_aux(OpKind op_kind,
                                 const BitVector& x,
                                 const BitVector& s,
                                 uint32_t pos_x);
  bool check_sat_binary(Kind kind,
                        OpKind op_kind,
                        const BitVectorDomain& x,
                        const BitVector& t,
                        const BitVector& s,
                        uint32_t pos_x);
  bool check_sat_ite(Kind kind,
                     const BitVectorDomain& x,
                     const BitVector& t,
                     const BitVector& s0,
                     const BitVector& s1,
                     uint32_t pos_x);
  bool check_sat_extract(Kind kind,
                         const BitVectorDomain& x,
                         const BitVector& t,
                         uint32_t hi,
                         uint32_t lo);
  bool check_sat_sext(Kind kind,
                      const BitVectorDomain& x,
                      const BitVector& t,
                      uint32_t n);

  template <class T>
  void test_binary(Kind kind, OpKind op_kind, uint32_t pos_x, bool const_bits);
  void test_ite(Kind kind, uint32_t pos_x, bool const_bits);
  void test_extract(Kind kind, bool const_bits);
  void test_sext(Kind kind, bool const_bits);

  static constexpr uint32_t TEST_BW = 4;
  std::vector<std::string> d_values;
  std::vector<std::string> d_xvalues;
  std::unique_ptr<RNG> d_rng;
};

BitVector
TestBvOp::check_sat_binary_aux(OpKind op_kind,
                               const BitVector& x,
                               const BitVector& s,
                               uint32_t pos_x)
{
  BitVector res;
  switch (op_kind)
  {
    case ADD: res = pos_x ? s.bvadd(x) : x.bvadd(s); break;
    case AND: res = pos_x ? s.bvand(x) : x.bvand(s); break;
    case ASHR: res = pos_x ? s.bvashr(x) : x.bvashr(s); break;
    case CONCAT: res = pos_x ? s.bvconcat(x) : x.bvconcat(s); break;
    case EQ: res = pos_x ? s.bveq(x) : x.bveq(s); break;
    case IMPLIES: res = pos_x ? s.bvimplies(x) : x.bvimplies(s); break;
    case MUL: res = pos_x ? s.bvmul(x) : x.bvmul(s); break;
    case NAND: res = pos_x ? s.bvnand(x) : x.bvnand(s); break;
    case NE: res = pos_x ? s.bvne(x) : x.bvne(s); break;
    case NOR: res = pos_x ? s.bvnor(x) : x.bvnor(s); break;
    case OR: res = pos_x ? s.bvor(x) : x.bvor(s); break;
    case SDIV: res = pos_x ? s.bvsdiv(x) : x.bvsdiv(s); break;
    case SGT: res = pos_x ? s.bvsgt(x) : x.bvsgt(s); break;
    case SGE: res = pos_x ? s.bvsge(x) : x.bvsge(s); break;
    case SHL: res = pos_x ? s.bvshl(x) : x.bvshl(s); break;
    case SHR: res = pos_x ? s.bvshr(x) : x.bvshr(s); break;
    case SLT: res = pos_x ? s.bvslt(x) : x.bvslt(s); break;
    case SLE: res = pos_x ? s.bvsle(x) : x.bvsle(s); break;
    case SREM: res = pos_x ? s.bvsrem(x) : x.bvsrem(s); break;
    case SUB: res = pos_x ? s.bvsub(x) : x.bvsub(s); break;
    case UDIV: res = pos_x ? s.bvudiv(x) : x.bvudiv(s); break;
    case UGT: res = pos_x ? s.bvugt(x) : x.bvugt(s); break;
    case UGE: res = pos_x ? s.bvuge(x) : x.bvuge(s); break;
    case ULT: res = pos_x ? s.bvult(x) : x.bvult(s); break;
    case ULE: res = pos_x ? s.bvule(x) : x.bvule(s); break;
    case UREM: res = pos_x ? s.bvurem(x) : x.bvurem(s); break;
    case XNOR: res = pos_x ? s.bvxnor(x) : x.bvxnor(s); break;
    case XOR: res = pos_x ? s.bvxor(x) : x.bvxor(s); break;
    default: assert(false);
  }
  return res;
}

bool
TestBvOp::check_sat_binary(Kind kind,
                           OpKind op_kind,
                           const BitVectorDomain& x,
                           const BitVector& t,
                           const BitVector& s,
                           uint32_t pos_x)
{
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector res;
    BitVector xval = gen.has_next() ? gen.next() : x.lo();
    if (kind == IS_CONS)
    {
      BitVectorDomainGenerator gens(s.size());
      while (gens.has_next())
      {
        res = check_sat_binary_aux(op_kind, xval, gens.next(), pos_x);
        if (t.compare(res) == 0) return true;
      }
    }
    else
    {
      res = check_sat_binary_aux(op_kind, xval, s, pos_x);
      if (t.compare(res) == 0) return true;
    }
  } while (gen.has_next());
  return false;
}

bool
TestBvOp::check_sat_ite(Kind kind,
                        const BitVectorDomain& x,
                        const BitVector& t,
                        const BitVector& s0,
                        const BitVector& s1,
                        uint32_t pos_x)
{
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res;
    if (pos_x == 0)
    {
      res = BitVector::bvite(val, s0, s1);
    }
    else if (pos_x == 1)
    {
      if (s0.is_false() && s1.compare(t) != 0) return false;
      res = BitVector::bvite(s0, val, s1);
    }
    else
    {
      if (s0.is_true() && s1.compare(t) != 0) return false;
      res = BitVector::bvite(s0, s1, val);
    }
    if (t.compare(res) == 0) return true;
  } while (gen.has_next());
  return false;
}

bool
TestBvOp::check_sat_extract(Kind kind,
                            const BitVectorDomain& x,
                            const BitVector& t,
                            uint32_t hi,
                            uint32_t lo)
{
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res = val.bvextract(hi, lo);
    if (t.compare(res) == 0) return true;
  } while (gen.has_next());
  return false;
}

bool
TestBvOp::check_sat_sext(Kind kind,
                         const BitVectorDomain& x,
                         const BitVector& t,
                         uint32_t n)
{
  BitVectorDomainGenerator gen(x);
  do
  {
    BitVector val = gen.has_next() ? gen.next() : x.lo();
    BitVector res = val.bvsext(n);
    if (t.compare(res) == 0) return true;
  } while (gen.has_next());
  return false;
}

template <class T>
void
TestBvOp::test_binary(Kind kind,
                      OpKind op_kind,
                      uint32_t pos_x,
                      bool const_bits)
{
  std::vector<std::string> x_values;

  uint32_t bw_x = TEST_BW;
  uint32_t bw_s = TEST_BW;
  uint32_t bw_t = TEST_BW;

  if (const_bits)
  {
    x_values = d_xvalues;
  }
  else
  {
    /* x is unconstrained (no const bits) */
    x_values.push_back(std::string(bw_x, 'x'));
  }

  if (op_kind == ULT || op_kind == SLT || op_kind == EQ)
  {
    bw_t = 1;
  }
  else if (op_kind == CONCAT)
  {
    bw_s = 2; /* decrease number of tests for concat */
    bw_t = bw_s + bw_x;
  }

  uint32_t nval_s = 1 << bw_s;
  uint32_t nval_t = 1 << bw_t;
  for (const std::string& x_value : x_values)
  {
    BitVectorDomain x(x_value);
    for (uint32_t i = 0; i < nval_s; i++)
    {
      /* Assignment of the other operand. */
      BitVector s(bw_s, i);
      for (uint32_t j = 0; j < nval_t; j++)
      {
        /* Target value of the operation (op). */
        BitVector t(bw_t, j);
        /* For this test, we don't care about the current assignment of x, thus
         * we initialize it with 0. */
        BitVectorOp* op_x =
            new T(d_rng.get(), BitVector::mk_zero(bw_x), x, nullptr, nullptr);
        /* For this test, we don't care about the domain of s, thus we
         * initialize it with an unconstrained domain. */
        BitVectorOp* op_s =
            new T(d_rng.get(), s, BitVectorDomain(bw_s), nullptr, nullptr);
        /* For this test, we don't care about current assignment and domain of
         * the op, thus we initialize them with 0 and 'x..x', respectively. */
        T op(d_rng.get(),
             bw_t,
             pos_x == 0 ? op_x : op_s,
             pos_x == 1 ? op_x : op_s);

        bool res    = kind == IS_INV ? op.is_invertible(t, pos_x)
                                     : op.is_consistent(t, pos_x);
        bool status = check_sat_binary(kind, op_kind, x, t, s, pos_x);
        if (res != status)
        {
          std::cout << "pos_x: " << pos_x << std::endl;
          std::cout << "t: " << t.to_string() << std::endl;
          std::cout << "x: " << x_value << std::endl;
          std::cout << "s: " << s.to_string() << std::endl;
        }
        ASSERT_EQ(res, status);

        delete op[pos_x];
        delete op[1 - pos_x];
      }
    }
  }
}

void
TestBvOp::test_ite(Kind kind, uint32_t pos_x, bool const_bits)
{
  std::vector<std::string> x_values;
  uint32_t bw_s0, bw_s1, bw = TEST_BW;
  uint32_t n_vals, n_vals_s0, n_vals_s1;
  uint32_t pos_s0 = pos_x == 0 ? 1 : 0;
  uint32_t pos_s1 = pos_x == 2 ? 1 : 2;

  if (pos_x)
  {
    bw_s0 = 1;
    bw_s1 = bw;
    if (const_bits)
    {
      x_values = d_xvalues;
    }
    else
    {
      x_values.push_back(std::string(bw, 'x'));
    }
  }
  else
  {
    bw_s0 = bw;
    bw_s1 = bw;
    if (const_bits)
    {
      x_values.push_back("x");
      x_values.push_back("0");
      x_values.push_back("1");
    }
    else
    {
      x_values.push_back("x");
    }
  }
  n_vals    = 1 << bw;
  n_vals_s0 = 1 << bw_s0;
  n_vals_s1 = 1 << bw_s1;

  for (const std::string& x_value : x_values)
  {
    BitVectorDomain x(x_value);
    for (uint32_t i = 0; i < n_vals_s0; i++)
    {
      BitVector s0(bw_s0, i);
      for (uint32_t j = 0; j < n_vals_s1; j++)
      {
        BitVector s1(bw_s1, j);
        for (uint32_t k = 0; k < n_vals; k++)
        {
          BitVector t(bw, k);

          /* For this test, we don't care about the current assignment of x,
           * thus we initialize it with 0. */
          BitVectorOp* op_x = new BitVectorIte(d_rng.get(),
                                               BitVector::mk_zero(bw),
                                               x,
                                               nullptr,
                                               nullptr,
                                               nullptr);
          /* For this test, we don't care about the domain of 0, thus we
           * initialize it with an unconstrained domain. */
          BitVectorOp* op_s0 = new BitVectorIte(d_rng.get(),
                                                s0,
                                                BitVectorDomain(bw_s0),
                                                nullptr,
                                                nullptr,
                                                nullptr);
          BitVectorOp* op_s1 = new BitVectorIte(d_rng.get(),
                                                s1,
                                                BitVectorDomain(bw_s0),
                                                nullptr,
                                                nullptr,
                                                nullptr);
          /* For this test, we don't care about current assignment and domain of
           * the op, thus we initialize them with 0 and 'x..x', respectively. */
          BitVectorIte op(d_rng.get(),
                          bw,
                          pos_x == 0 ? op_x : op_s0,
                          pos_x == 1 ? op_x : (pos_x == 2 ? op_s1 : op_s0),
                          pos_x == 2 ? op_x : op_s1);

          bool res    = op.is_invertible(t, pos_x);
          bool status = check_sat_ite(kind, x, t, s0, s1, pos_x);
          if (res != status)
          {
            std::cout << "pos_x: " << pos_x << std::endl;
            std::cout << "t: " << t.to_string() << std::endl;
            std::cout << "x: " << x_value << std::endl;
            std::cout << "s0: " << s0.to_string() << std::endl;
            std::cout << "s1: " << s1.to_string() << std::endl;
          }
          ASSERT_EQ(res, status);

          delete op[pos_x];
          delete op[pos_s0];
          delete op[pos_s1];
        }
      }
    }
  }
}

void
TestBvOp::test_extract(Kind kind, bool const_bits)
{
  std::vector<std::string> x_values;
  uint32_t bw_x = TEST_BW;

  if (const_bits)
  {
    x_values = d_values;
  }
  else
  {
    /* x is unconstrained (no const bits) */
    x_values.push_back(std::string(bw_x, 'x'));
  }

  for (const std::string& x_value : x_values)
  {
    BitVectorDomain x(x_value);
    for (uint32_t lo = 0; lo < bw_x; ++lo)
    {
      for (uint32_t hi = lo; hi < bw_x; ++hi)
      {
        uint32_t bw_t = hi - lo + 1;
        for (uint32_t i = 0, n = 1 << bw_t; i < n; ++i)
        {
          BitVector t(bw_t, i);
          /* For this test, we don't care about the current assignment of x,
           * thus we initialize it with 0. */
          BitVectorOp* op_x = new BitVectorExtract(
              d_rng.get(), BitVector::mk_zero(bw_x), x, nullptr, hi, lo);
          /* For this test, we don't care about current assignment and domain
           * of the op, thus we initialize them with 0 and 'x..x',
           * respectively. */
          BitVectorExtract op(d_rng.get(), bw_t, op_x, hi, lo);

          bool res    = op.is_invertible(t, 0);
          bool status = check_sat_extract(kind, x, t, hi, lo);

          if (res != status)
          {
            std::cout << "hi: " << hi << std::endl;
            std::cout << "lo: " << lo << std::endl;
            std::cout << "t: " << t.to_string() << std::endl;
            std::cout << "x: " << x_value << std::endl;
          }
          ASSERT_EQ(res, status);

          delete op_x;
        }
      }
    }
  }
}

void
TestBvOp::test_sext(Kind kind, bool const_bits)
{
  std::vector<std::string> x_values;
  uint32_t bw_x = TEST_BW;

  if (const_bits)
  {
    x_values = d_values;
  }
  else
  {
    /* x is unconstrained (no const bits) */
    x_values.push_back(std::string(bw_x, 'x'));
  }

  for (const std::string& x_value : x_values)
  {
    BitVectorDomain x(x_value);
    for (uint32_t n = 1; n <= bw_x; ++n)
    {
      uint32_t bw_t = bw_x + n;
      for (uint32_t i = 0, m = 1 << bw_t; i < m; ++i)
      {
        BitVector t(bw_t, i);
        /* For this test, we don't care about the current assignment of x,
         * thus we initialize it with 0. */
        BitVectorOp* op_x = new BitVectorSignExtend(
            d_rng.get(), BitVector::mk_zero(bw_x), x, nullptr, n);
        /* For this test, we don't care about current assignment and domain
         * of the op, thus we initialize them with 0 and 'x..x',
         * respectively. */
        BitVectorSignExtend op(d_rng.get(), bw_t, op_x, n);

        bool res    = op.is_invertible(t, 0);
        bool status = check_sat_sext(kind, x, t, n);

        if (res != status)
        {
          std::cout << "n: " << n << std::endl;
          std::cout << "t: " << t.to_string() << std::endl;
          std::cout << "x: " << x_value << std::endl;
        }
        ASSERT_EQ(res, status);

        delete op_x;
      }
    }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace test
}  // namespace bzlals
#endif
