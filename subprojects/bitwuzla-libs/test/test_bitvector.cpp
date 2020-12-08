#include <bitset>
#include <iostream>

#include "bitvector.h"
#include "gmpmpz.h"
#include "gmprandstate.h"
#include "gtest/gtest.h"
#include "rng.h"

namespace bzlals {

class TestBitVector : public ::testing::Test
{
 protected:
  enum Kind
  {
    ADD,
    AND,
    ASHR,
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
  };

  static constexpr uint32_t N_BITVEC_TESTS = 100000;
  void SetUp() override { d_rng.reset(new RNG(1234)); }

  static uint64_t _add(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _and(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ashr(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _dec(uint64_t x, uint32_t size);
  static uint64_t _eq(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _implies(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ite(uint64_t c, uint64_t t, uint64_t e, uint32_t size);
  static uint64_t _inc(uint64_t x, uint32_t size);
  static uint64_t _mul(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _nand(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ne(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _neg(uint64_t x, uint32_t size);
  static uint64_t _nor(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _not(uint64_t x, uint32_t size);
  static uint64_t _or(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _redand(uint64_t x, uint32_t size);
  static uint64_t _redor(uint64_t x, uint32_t size);
  static int64_t _sdiv(int64_t x, int64_t y, uint32_t size);
  static int64_t _sgt(int64_t x, int64_t y, uint32_t size);
  static int64_t _sge(int64_t x, int64_t y, uint32_t size);
  static uint64_t _shl(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _shr(uint64_t x, uint64_t y, uint32_t size);
  static int64_t _slt(int64_t x, int64_t y, uint32_t size);
  static int64_t _sle(int64_t x, int64_t y, uint32_t size);
  static int64_t _srem(int64_t x, int64_t y, uint32_t size);
  static uint64_t _sub(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _udiv(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ugt(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _uge(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ult(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _ule(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _urem(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _xnor(uint64_t x, uint64_t y, uint32_t size);
  static uint64_t _xor(uint64_t x, uint64_t y, uint32_t size);

  BitVector mk_ones(uint32_t size);
  BitVector mk_min_signed(uint32_t size);
  BitVector mk_max_signed(uint32_t size);
  void test_count(uint32_t size, bool leading, bool zeros);
  void test_count_aux(const std::string& val, bool leading, bool zeros);
  void test_unary(Kind kind, uint32_t size);
  void test_binary(Kind kind, uint32_t size);
  void test_concat(uint32_t size);
  std::unique_ptr<RNG> d_rng;
};

uint64_t
TestBitVector::_not(uint64_t x, uint32_t size)
{
  return ~x % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_neg(uint64_t x, uint32_t size)
{
  return -x % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_redand(uint64_t x, uint32_t size)
{
  uint64_t a = UINT64_MAX << size;
  return (x + a) == UINT64_MAX;
}

uint64_t
TestBitVector::_redor(uint64_t x, uint32_t size)
{
  (void) size;
  return x != 0;
}

uint64_t
TestBitVector::_inc(uint64_t x, uint32_t size)
{
  return (x + 1) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_dec(uint64_t x, uint32_t size)
{
  return (x - 1) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_add(uint64_t x, uint64_t y, uint32_t size)
{
  return (x + y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_sub(uint64_t x, uint64_t y, uint32_t size)
{
  return (x - y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_and(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x & y;
}

uint64_t
TestBitVector::_nand(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  uint32_t shift = 64 - size;
  return (((~(x & y)) << shift) >> shift);
}

uint64_t
TestBitVector::_or(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x | y;
}

uint64_t
TestBitVector::_nor(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  uint32_t shift = 64 - size;
  return ((~(x | y)) << shift) >> shift;
}

uint64_t
TestBitVector::_xnor(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  uint32_t shift = 64 - size;
  return ((~(x ^ y)) << shift) >> shift;
}

uint64_t
TestBitVector::_implies(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size == 1);
  (void) size;
  return ((~x | y) << 63) >> 63;
}

uint64_t
TestBitVector::_xor(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x ^ y;
}

uint64_t
TestBitVector::_eq(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x == y;
}

uint64_t
TestBitVector::_ne(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x != y;
}

uint64_t
TestBitVector::_ult(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x < y;
}

uint64_t
TestBitVector::_ule(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x <= y;
}

uint64_t
TestBitVector::_ugt(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x > y;
}

uint64_t
TestBitVector::_uge(uint64_t x, uint64_t y, uint32_t size)
{
  (void) size;
  return x >= y;
}

int64_t
TestBitVector::_slt(int64_t x, int64_t y, uint32_t size)
{
  (void) size;
  return x < y;
}

int64_t
TestBitVector::_sle(int64_t x, int64_t y, uint32_t size)
{
  (void) size;
  return x <= y;
}

int64_t
TestBitVector::_sgt(int64_t x, int64_t y, uint32_t size)
{
  (void) size;
  return x > y;
}

int64_t
TestBitVector::_sge(int64_t x, int64_t y, uint32_t size)
{
  (void) size;
  return x >= y;
}

uint64_t
TestBitVector::_shl(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  if (y >= size) return 0;
  return (x << y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_shr(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  if (y >= size) return 0;
  return (x >> y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_ashr(uint64_t x, uint64_t y, uint32_t size)
{
  assert(size <= 64);
  uint64_t max = pow(2, size);
  if ((x >> (size - 1)) & 1)
  {
    if (y > size) return ~0 % max;
    return ~((~x % max) >> y) % max;
  }
  if (y > size) return 0;
  return (x >> y) % max;
}

uint64_t
TestBitVector::_mul(uint64_t x, uint64_t y, uint32_t size)
{
  return (x * y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_udiv(uint64_t x, uint64_t y, uint32_t size)
{
  if (y == 0) return UINT64_MAX % (uint64_t) pow(2, size);
  return (x / y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_urem(uint64_t x, uint64_t y, uint32_t size)
{
  if (y == 0) return x;
  return (x % y) % (uint64_t) pow(2, size);
}

int64_t
TestBitVector::_sdiv(int64_t x, int64_t y, uint32_t size)
{
  if (y == 0)
  {
    return x < 0 ? 1 : UINT64_MAX % (uint64_t) pow(2, size);
  }
  return (x / y) % (uint64_t) pow(2, size);
}

int64_t
TestBitVector::_srem(int64_t x, int64_t y, uint32_t size)
{
  if (y == 0) return x % (uint64_t) pow(2, size);
  return (x % y) % (uint64_t) pow(2, size);
}

uint64_t
TestBitVector::_ite(uint64_t c, uint64_t t, uint64_t e, uint32_t size)
{
  (void) size;
  return c ? t : e;
}

BitVector
TestBitVector::mk_ones(uint32_t size)
{
  if (size <= 64)
  {
    return BitVector(size, UINT64_MAX);
  }
  BitVector r(64, UINT64_MAX);
  BitVector l(size - 64, UINT64_MAX);
  return l.bvconcat(r);
}

BitVector
TestBitVector::mk_min_signed(uint32_t size)
{
  if (size <= 64)
  {
    return BitVector(size, ((uint64_t) 1) << (size - 1));
  }
  BitVector r(64, 0);
  BitVector l(size - 64, ((uint64_t) 1) << (size - 1 - 64));
  return l.bvconcat(r);
}

BitVector
TestBitVector::mk_max_signed(uint32_t size)
{
  if (size <= 64)
  {
    return BitVector(size, (((uint64_t) 1) << (size - 1)) - 1);
  }
  BitVector r(64, UINT64_MAX);
  BitVector l(size - 64, (((uint64_t) 1) << (size - 1 - 64)) - 1);
  return l.bvconcat(r);
}

void
TestBitVector::test_count_aux(const std::string& val, bool leading, bool zeros)
{
  uint32_t size     = val.size();
  uint32_t expected = 0;
  char c            = zeros ? '0' : '1';
  BitVector bv(size, val);
  if (leading)
  {
    for (expected = 0; expected < size && val[expected] == c; ++expected)
      ;
    if (zeros)
    {
      ASSERT_EQ(bv.count_leading_zeros(), expected);
    }
    else
    {
      ASSERT_EQ(bv.count_leading_ones(), expected);
    }
  }
  else
  {
    for (expected = 0; expected < size && val[size - 1 - expected] == c;
         ++expected)
      ;
    assert(zeros);
    ASSERT_EQ(bv.count_trailing_zeros(), expected);
  }
}

void
TestBitVector::test_count(uint32_t size, bool leading, bool zeros)
{
  if (size == 8)
  {
    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      ss << std::bitset<8>(i).to_string();
      test_count_aux(ss.str(), leading, zeros);
    }
  }
  else
  {
    // concat 8-bit value with 0s to create value for bv
    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << v << std::string(size - 8, '0');
      test_count_aux(ss.str(), leading, zeros);
    }

    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << std::string(size - 8, '0') << v;
      test_count_aux(ss.str(), leading, zeros);
    }

    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << v << std::string(size - 16, '0') << v;
      test_count_aux(ss.str(), leading, zeros);
    }

    // concat 8-bit values with 1s to create value for bv
    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << v << std::string(size - 8, '1');
      test_count_aux(ss.str(), leading, zeros);
    }

    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << std::string(size - 8, '1') << v;
      test_count_aux(ss.str(), leading, zeros);
    }

    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      std::stringstream ss;
      std::string v = std::bitset<8>(i).to_string();
      ss << v << std::string(size - 16, '1') << v;
      test_count_aux(ss.str(), leading, zeros);
    }
  }
}

void
TestBitVector::test_unary(TestBitVector::Kind kind, uint32_t size)
{
  for (uint32_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint64_t ares;
    BitVector res;
    BitVector bv(size, *d_rng);
    uint64_t a = bv.to_uint64();
    switch (kind)
    {
      case DEC:
        res  = bv.bvdec();
        ares = _dec(a, size);
        break;

      case INC:
        res  = bv.bvinc();
        ares = _inc(a, size);
        break;

      case NEG:
        res  = bv.bvneg();
        ares = _neg(a, size);
        break;

      case NOT:
        res  = bv.bvnot();
        ares = _not(a, size);
        break;

      case REDAND:
        res  = bv.bvredand();
        ares = _redand(a, size);
        break;

      case REDOR:
        res  = bv.bvredor();
        ares = _redor(a, size);
        break;

      default: assert(false);
    }
    uint64_t bres = res.to_uint64();
    ASSERT_EQ(ares, bres);
  }
}

void
TestBitVector::test_binary(TestBitVector::Kind kind, uint32_t size)
{
  BitVector zero = BitVector::mk_zero(size);

  for (uint32_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint64_t ares, bres;
    BitVector res;
    BitVector bv1(size, *d_rng);
    BitVector bv2(size, *d_rng);
    uint64_t a1 = bv1.to_uint64();
    uint64_t a2 = bv2.to_uint64();
    /* test for x = 0 explicitly */
    switch (kind)
    {
      case ADD:
        res  = zero.bvadd(bv2);
        ares = _add(0, a2, size);
        break;

      case AND:
        res  = zero.bvand(bv2);
        ares = _and(0, a2, size);
        break;

      case EQ:
        res  = zero.bveq(bv2);
        ares = _eq(0, a2, size);
        break;

      case IMPLIES:
        res  = zero.bvimplies(bv2);
        ares = _implies(0, a2, size);
        break;

      case NAND:
        res  = zero.bvnand(bv2);
        ares = _nand(0, a2, size);
        break;

      case NE:
        res  = zero.bvne(bv2);
        ares = _ne(0, a2, size);
        break;

      case NOR:
        res  = zero.bvnor(bv2);
        ares = _nor(0, a2, size);
        break;

      case OR:
        res  = zero.bvor(bv2);
        ares = _or(0, a2, size);
        break;

      case SUB:
        res  = zero.bvsub(bv2);
        ares = _sub(0, a2, size);
        break;

      case XOR:
        res  = zero.bvxor(bv2);
        ares = _xor(0, a2, size);
        break;

      case XNOR:
        res  = zero.bvxnor(bv2);
        ares = _xnor(0, a2, size);
        break;

      default: assert(false);
    }
    bres = res.to_uint64();
    ASSERT_EQ(ares, bres);
    /* test for y = 0 explicitly */
    switch (kind)
    {
      case ADD:
        res  = bv1.bvadd(zero);
        ares = _add(a1, 0, size);
        break;

      case AND:
        res  = bv1.bvand(zero);
        ares = _and(a1, 0, size);
        break;

      case EQ:
        res  = bv1.bveq(zero);
        ares = _eq(a1, 0, size);
        break;

      case IMPLIES:
        res  = bv1.bvimplies(zero);
        ares = _implies(a1, 0, size);
        break;

      case NAND:
        res  = bv1.bvnand(zero);
        ares = _nand(a1, 0, size);
        break;

      case NE:
        res  = bv1.bvne(zero);
        ares = _ne(a1, 0, size);
        break;

      case NOR:
        res  = bv1.bvnor(zero);
        ares = _nor(a1, 0, size);
        break;

      case OR:
        res  = bv1.bvor(zero);
        ares = _or(a1, 0, size);
        break;

      case SUB:
        res  = bv1.bvsub(zero);
        ares = _sub(a1, 0, size);
        break;

      case XOR:
        res  = bv1.bvxor(zero);
        ares = _xor(a1, 0, size);
        break;

      case XNOR:
        res  = bv1.bvxnor(zero);
        ares = _xnor(a1, 0, size);
        break;

      default: assert(false);
    }
    bres = res.to_uint64();
    ASSERT_EQ(ares, bres);
    /* test x, y random */
    switch (kind)
    {
      case ADD:
        res  = bv1.bvadd(bv2);
        ares = _add(a1, a2, size);
        break;

      case AND:
        res  = bv1.bvand(bv2);
        ares = _and(a1, a2, size);
        break;

      case EQ:
        res  = bv1.bveq(bv2);
        ares = _eq(a1, a2, size);
        break;

      case IMPLIES:
        res  = bv1.bvimplies(bv2);
        ares = _implies(a1, a2, size);
        break;

      case NAND:
        res  = bv1.bvnand(bv2);
        ares = _nand(a1, a2, size);
        break;

      case NE:
        res  = bv1.bvne(bv2);
        ares = _ne(a1, a2, size);
        break;

      case NOR:
        res  = bv1.bvnor(bv2);
        ares = _nor(a1, a2, size);
        break;

      case OR:
        res  = bv1.bvor(bv2);
        ares = _or(a1, a2, size);
        break;

      case SUB:
        res  = bv1.bvsub(bv2);
        ares = _sub(a1, a2, size);
        break;

      case XOR:
        res  = bv1.bvxor(bv2);
        ares = _xor(a1, a2, size);
        break;

      case XNOR:
        res  = bv1.bvxnor(bv2);
        ares = _xnor(a1, a2, size);
        break;

      default: assert(false);
    }
    bres = res.to_uint64();
    ASSERT_EQ(ares, bres);
  }
}

void
TestBitVector::test_concat(uint32_t size)
{
  for (uint32_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint32_t size1 = d_rng->pick<uint32_t>(1, size - 1);
    uint32_t size2 = size - size1;
    BitVector bv1(size1, *d_rng);
    BitVector bv2(size2, *d_rng);
    BitVector res = bv1.bvconcat(bv2);
    ASSERT_EQ(res.get_size(), size1 + size2);
    uint64_t u1   = bv1.to_uint64();
    uint64_t u2   = bv2.to_uint64();
    uint64_t u    = (u1 << size2) | u2;
    uint64_t ures = res.to_uint64();
    ASSERT_EQ(u, ures);
  }
}

TEST_F(TestBitVector, ctor_dtor)
{
  ASSERT_NO_FATAL_FAILURE(BitVector(1));
  ASSERT_NO_FATAL_FAILURE(BitVector(10));
  ASSERT_NO_FATAL_FAILURE(BitVector(6, "101010"));
  ASSERT_NO_FATAL_FAILURE(BitVector(8, "101010"));
  ASSERT_NO_FATAL_FAILURE(BitVector(16, 1234));
  ASSERT_NO_FATAL_FAILURE(BitVector(16, 123412341234));
  ASSERT_DEATH(BitVector(0), "> 0");
  ASSERT_DEATH(BitVector(2, "101010"), "<= size");
  ASSERT_DEATH(BitVector(6, "123412"), "is_bin_str");
  ASSERT_DEATH(BitVector(0, 1234), "> 0");
}

TEST_F(TestBitVector, ctor_rand)
{
  for (uint32_t size = 1; size <= 64; ++size)
  {
    BitVector bv1(size, *d_rng);
    BitVector bv2(size, *d_rng);
    BitVector bv3(size, *d_rng);
    assert(bv1.compare(bv2) || bv1.compare(bv3) || bv2.compare(bv3));
  }
}

TEST_F(TestBitVector, to_string)
{
  ASSERT_EQ(BitVector(1).to_string(), "0");
  ASSERT_EQ(BitVector(10).to_string(), "0000000000");
  ASSERT_EQ(BitVector(6, "101010").to_string(), "101010");
  ASSERT_EQ(BitVector(8, "101010").to_string(), "00101010");
  ASSERT_EQ(BitVector(16, 1234).to_string(), "0000010011010010");
  ASSERT_EQ(BitVector(16, 123412341234).to_string(), "1110000111110010");
  ASSERT_EQ(BitVector(16, UINT64_MAX).to_string(), "1111111111111111");
}

TEST_F(TestBitVector, to_uint64)
{
  for (uint64_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint64_t x = (d_rng->pick<uint64_t>() << 32) | d_rng->pick<uint64_t>();
    BitVector bv(64, x);
    uint64_t y = bv.to_uint64();
    ASSERT_EQ(x, y);
  }
  ASSERT_NO_FATAL_FAILURE(BitVector(28).to_uint64());
  ASSERT_DEATH(BitVector(128).to_uint64(), "");
}

TEST_F(TestBitVector, compare)
{
  for (uint32_t i = 0; i < 15; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i);
    ASSERT_EQ(bv1.compare(bv2), 0);
  }

  for (uint32_t i = 0; i < 15 - 1; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i + 1);
    ASSERT_LT(bv1.compare(bv2), 0);
    ASSERT_GT(bv2.compare(bv1), 0);
  }

  for (uint32_t i = 0, j = 0; i < 15; ++i)
  {
    uint32_t k = rand() % 16;
    do
    {
      j = rand() % 16;
    } while (j == k);

    BitVector bv1(4, j);
    BitVector bv2(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.compare(bv2), 0);
      ASSERT_LT(bv2.compare(bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.compare(bv2), 0);
      ASSERT_GT(bv2.compare(bv1), 0);
    }
  }
  ASSERT_DEATH(BitVector(1).compare(BitVector(2)), "");
}

TEST_F(TestBitVector, signed_compare)
{
  for (int32_t i = -8; i < 7; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i);
    ASSERT_EQ(bv1.signed_compare(bv2), 0);
  }

  for (int32_t i = -8; i < 7 - 1; i++)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i + 1);
    ASSERT_LT(bv1.signed_compare(bv2), 0);
    ASSERT_GT(bv2.signed_compare(bv1), 0);
  }

  for (int32_t i = 0, j = 0; i < 15; i++)
  {
    /* j <= 0, k <= 0 */
    int32_t k = rand() % 9;
    do
    {
      j = rand() % 9;
    } while (j == k);
    j = -j;
    k = -k;
    BitVector bv1(4, j);
    BitVector bv2(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.signed_compare(bv2), 0);
      ASSERT_LT(bv2.signed_compare(bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.signed_compare(bv2), 0);
      ASSERT_GT(bv2.signed_compare(bv1), 0);
    }

    {
      /* j <= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 9;
      } while (j == k);
      j = -j;
      BitVector bv1(4, j);
      BitVector bv2(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }

    {
      /* j >= 0, k <= 0 */
      k = rand() % 9;
      do
      {
        j = rand() % 8;
      } while (j == k);
      k = -k;
      BitVector bv1(4, j);
      BitVector bv2(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }

    {
      /* j >= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 8;
      } while (j == k);
      BitVector bv1(4, -j);
      BitVector bv2(4, -k);
      if (-j > -k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (-j < -k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }
  }
  ASSERT_DEATH(BitVector(1).signed_compare(BitVector(2)), "");
}

TEST_F(TestBitVector, set_get_flip_bit)
{
  for (uint32_t i = 1; i < 32; ++i)
  {
    BitVector bv(i, *d_rng);
    uint32_t n  = d_rng->pick<uint32_t>(0, i - 1);
    uint32_t v  = bv.get_bit(n);
    uint32_t vv = d_rng->flip_coin() ? 1 : 0;
    bv.set_bit(n, vv);
    ASSERT_EQ(bv.get_bit(n), vv);
    ASSERT_TRUE(v == vv || bv.get_bit(n) == (((~v) << 31) >> 31));
    bv.flip_bit(n);
    ASSERT_EQ(bv.get_bit(n), (((~vv) << 31) >> 31));
  }
}

TEST_F(TestBitVector, is_zero)
{
  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 0);
    }
    else
    {
      BitVector r(64, 0);
      BitVector l(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_TRUE(bv1.is_zero());
    ASSERT_TRUE(bv2.is_zero());
    ASSERT_TRUE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 1);
    }
    else
    {
      BitVector r(i - 64, 1);
      BitVector l(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    BitVector bv1 = BitVector::mk_min_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_min_signed(i);
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    BitVector bv1 = BitVector::mk_max_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_max_signed(i);
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }
}

TEST_F(TestBitVector, is_one)
{
  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 0);
    }
    else
    {
      BitVector r(64, 0);
      BitVector l(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_one());
    ASSERT_FALSE(bv2.is_one());
    ASSERT_FALSE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 1);
    }
    else
    {
      BitVector r(i - 64, 1);
      BitVector l(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_TRUE(bv1.is_one());
    ASSERT_TRUE(bv2.is_one());
    ASSERT_TRUE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_FALSE(bv1.is_one());
    ASSERT_FALSE(bv2.is_one());
    ASSERT_FALSE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    BitVector bv1 = BitVector::mk_min_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_min_signed(i);
    ASSERT_FALSE(bv1.is_one());
    ASSERT_FALSE(bv2.is_one());
    ASSERT_FALSE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 3; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    BitVector bv1 = BitVector::mk_max_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_max_signed(i);
    ASSERT_FALSE(bv1.is_one());
    ASSERT_FALSE(bv2.is_one());
    ASSERT_FALSE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }
}

TEST_F(TestBitVector, is_ones)
{
  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 0);
    }
    else
    {
      BitVector r(64, 0);
      BitVector l(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 1);
    }
    else
    {
      BitVector r(i - 64, 1);
      BitVector l(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_TRUE(bv1.is_ones());
    ASSERT_TRUE(bv2.is_ones());
    ASSERT_TRUE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    BitVector bv1 = BitVector::mk_min_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_min_signed(i);
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    BitVector bv1 = BitVector::mk_max_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_max_signed(i);
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }
}

TEST_F(TestBitVector, is_max_signed)
{
  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 0);
    }
    else
    {
      BitVector r(64, 0);
      BitVector l(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 3; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 1);
    }
    else
    {
      BitVector r(i - 64, 1);
      BitVector l(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    BitVector bv1 = BitVector::mk_min_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_min_signed(i);
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    BitVector bv1 = BitVector::mk_max_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_max_signed(i);
    ASSERT_TRUE(bv1.is_max_signed());
    ASSERT_TRUE(bv2.is_max_signed());
    ASSERT_TRUE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }
}

TEST_F(TestBitVector, is_min_signed)
{
  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 0);
    }
    else
    {
      BitVector r(64, 0);
      BitVector l(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector(i, 1);
    }
    else
    {
      BitVector r(i - 64, 1);
      BitVector l(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    BitVector bv1 = BitVector::mk_min_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_min_signed(i);
    ASSERT_TRUE(bv1.is_min_signed());
    ASSERT_TRUE(bv2.is_min_signed());
    ASSERT_TRUE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    BitVector bv1 = BitVector::mk_max_signed(i);
    BitVector bv2(i, ss.str());
    BitVector bv3 = mk_max_signed(i);
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }
}

TEST_F(TestBitVector, count_trailing_zeros)
{
  test_count(8, false, true);
  test_count(64, false, true);
  test_count(76, false, true);
  test_count(128, false, true);
  test_count(176, false, true);
}

TEST_F(TestBitVector, count_leading_zeros)
{
  test_count(8, true, true);
  test_count(64, true, true);
  test_count(76, true, true);
  test_count(128, true, true);
  test_count(176, true, true);
}

TEST_F(TestBitVector, count_leading_ones)
{
  test_count(8, true, false);
  test_count(64, true, false);
  test_count(76, true, false);
  test_count(128, true, false);
  test_count(176, true, false);
}

TEST_F(TestBitVector, dec)
{
  test_unary(DEC, 1);
  test_unary(DEC, 7);
  test_unary(DEC, 31);
  test_unary(DEC, 33);
}

TEST_F(TestBitVector, inc)
{
  test_unary(INC, 1);
  test_unary(INC, 7);
  test_unary(INC, 31);
  test_unary(INC, 33);
}

TEST_F(TestBitVector, neg)
{
  test_unary(NEG, 1);
  test_unary(NEG, 7);
  test_unary(NEG, 31);
  test_unary(NEG, 33);
}

TEST_F(TestBitVector, not )
{
  test_unary(NOT, 1);
  test_unary(NOT, 7);
  test_unary(NOT, 31);
  test_unary(NOT, 33);
}

TEST_F(TestBitVector, redand)
{
  test_unary(REDAND, 1);
  test_unary(REDAND, 7);
  test_unary(REDAND, 31);
  test_unary(REDAND, 33);
}

TEST_F(TestBitVector, redor)
{
  test_unary(REDOR, 1);
  test_unary(REDOR, 7);
  test_unary(REDOR, 31);
  test_unary(REDOR, 33);
}

TEST_F(TestBitVector, add)
{
  test_binary(ADD, 1);
  test_binary(ADD, 7);
  test_binary(ADD, 31);
  test_binary(ADD, 33);
}

TEST_F(TestBitVector, and)
{
  test_binary(AND, 1);
  test_binary(AND, 7);
  test_binary(AND, 31);
  test_binary(AND, 33);
}

TEST_F(TestBitVector, concat)
{
  test_concat(2);
  test_concat(7);
  test_concat(31);
  test_concat(33);
  test_concat(64);
}

TEST_F(TestBitVector, eq)
{
  test_binary(EQ, 1);
  test_binary(EQ, 7);
  test_binary(EQ, 31);
  test_binary(EQ, 33);
}

TEST_F(TestBitVector, implies) { test_binary(IMPLIES, 1); }

TEST_F(TestBitVector, nand)
{
  test_binary(NAND, 1);
  test_binary(NAND, 7);
  test_binary(NAND, 31);
  test_binary(NAND, 33);
}

TEST_F(TestBitVector, ne)
{
  test_binary(NE, 1);
  test_binary(NE, 7);
  test_binary(NE, 31);
  test_binary(NE, 33);
}

TEST_F(TestBitVector, or)
{
  test_binary(OR, 1);
  test_binary(OR, 7);
  test_binary(OR, 31);
  test_binary(OR, 33);
}

TEST_F(TestBitVector, nor)
{
  test_binary(NOR, 1);
  test_binary(NOR, 7);
  test_binary(NOR, 31);
  test_binary(NOR, 33);
}

TEST_F(TestBitVector, sub)
{
  test_binary(SUB, 1);
  test_binary(SUB, 7);
  test_binary(SUB, 31);
  test_binary(SUB, 33);
}

TEST_F(TestBitVector, xor)
{
  test_binary(XOR, 1);
  test_binary(XOR, 7);
  test_binary(XOR, 31);
  test_binary(XOR, 33);
}

TEST_F(TestBitVector, xnor)
{
  test_binary(XNOR, 1);
  test_binary(XNOR, 7);
  test_binary(XNOR, 31);
  test_binary(XNOR, 33);
}

TEST_F(TestBitVector, is_true)
{
  BitVector bv1 = BitVector::mk_true();
  ASSERT_TRUE(bv1.is_true());
  for (int32_t i = 1; i < 32; ++i)
  {
    BitVector bv2 = BitVector::mk_one(i);
    BitVector bv3(i, d_rng->pick<uint32_t>(1, (1 << i) - 1));
    if (i > 1)
    {
      ASSERT_FALSE(bv2.is_true());
      ASSERT_FALSE(bv3.is_true());
    }
    else
    {
      ASSERT_TRUE(bv3.is_true());
      ASSERT_TRUE(bv3.is_true());
    }
  }
}

TEST_F(TestBitVector, is_false)
{
  BitVector bv1 = BitVector::mk_false();
  ASSERT_TRUE(bv1.is_false());
  for (int32_t i = 1; i < 32; ++i)
  {
    BitVector bv2 = BitVector::mk_zero(i);
    BitVector bv3(i, d_rng->pick<uint32_t>(1, (1 << i) - 1));
    if (i > 1)
    {
      ASSERT_FALSE(bv2.is_false());
      ASSERT_FALSE(bv3.is_false());
    }
    else
    {
      ASSERT_TRUE(bv2.is_false());
      ASSERT_FALSE(bv3.is_false());
    }
  }
}

}  // namespace bzlals
