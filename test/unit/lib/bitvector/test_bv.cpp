/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitset>
#include <cmath>
#include <cstdint>

#include "bv/bitvector.h"
#include "test_lib.h"
#include "util/integer.h"

#ifndef int128_t
using int128_t = __int128_t;
#endif

namespace bzla::test {

/* -------------------------------------------------------------------------- */

class TestBitVector : public TestCommon
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
    NEGO,
    NOR,
    NOT,
    OR,
    ROL,
    ROLI,
    ROR,
    RORI,
    REDAND,
    REDOR,
    REDXOR,
    REPEAT,
    SADDO,
    SDIV,
    SDIVO,
    SEXT,
    SGT,
    SGE,
    SHL,
    SHR,
    SLT,
    SLE,
    SMOD,
    SMULO,
    SREM,
    SSUBO,
    SUB,
    UADDO,
    UDIV,
    UGT,
    UGE,
    ULT,
    ULE,
    UMULO,
    UREM,
    USUBO,
    XNOR,
    XOR,
    ZEXT,
  };

  enum BvFunKind
  {
    /** Not in-place, this is not passed as argument. */
    DEFAULT,
    /** In-place, this is not passed as argument. */
    INPLACE,
    /**
     * In-place, version that uses this as first argument.
     * For additional arguments, test with non-this and this arguments.
     */
    INPLACE_THIS,
    /**
     * In-place, version that does not use this as first argument.
     * Test with all non-this and all this arguments.
     */
    INPLACE_THIS_ALL,
  };

  static constexpr uint32_t N_TESTS = 1000;
  void SetUp() override { d_rng.reset(new RNG(1234)); }

  static uint64_t _add(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _and(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ashr(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _dec(uint64_t x, uint64_t size);
  static uint64_t _eq(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _implies(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ite(uint64_t c, uint64_t t, uint64_t e, uint64_t size);
  static uint64_t _inc(uint64_t x, uint64_t size);
  static uint64_t _mul(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _nand(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ne(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _neg(uint64_t x, uint64_t size);
  static uint64_t _nego(uint64_t x, uint64_t size);
  static uint64_t _nor(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _not(uint64_t x, uint64_t size);
  static uint64_t _or(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _redand(uint64_t x, uint64_t size);
  static uint64_t _redor(uint64_t x, uint64_t size);
  static uint64_t _redxor(uint64_t x, uint64_t size);
  static uint64_t _saddo(int64_t x, int64_t y, uint64_t size);
  static uint64_t _ssubo(int64_t x, int64_t y, uint64_t size);
  static uint64_t _smulo(int64_t x, int64_t y, uint64_t size);
  static uint64_t _sdivo(int64_t x, int64_t y, uint64_t size);
  static int64_t _sdiv(int64_t x, int64_t y, uint64_t size);
  static int64_t _sgt(int64_t x, int64_t y, uint64_t size);
  static int64_t _sge(int64_t x, int64_t y, uint64_t size);
  static uint64_t _shl(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _shr(uint64_t x, uint64_t y, uint64_t size);
  static int64_t _slt(int64_t x, int64_t y, uint64_t size);
  static int64_t _sle(int64_t x, int64_t y, uint64_t size);
  static int64_t _srem(int64_t x, int64_t y, uint64_t size);
  static int64_t _smod(int64_t x, int64_t y, uint64_t size);
  static uint64_t _sub(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _uaddo(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _umulo(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _usubo(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _udiv(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ugt(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _uge(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ult(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _ule(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _urem(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _xnor(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t _xor(uint64_t x, uint64_t y, uint64_t size);
  static uint64_t normalize_uint64(uint64_t size, uint64_t value);
  static int64_t normalize_int64(uint64_t size, int64_t value);

  BitVector mk_ones(uint64_t size);
  BitVector mk_min_signed(uint64_t size);
  BitVector mk_max_signed(uint64_t size);

  std::string to_bin_string(uint64_t size, uint64_t val);

  void test_ctor_random_bit_range(uint64_t size);
  void test_count(uint64_t size, bool leading, bool zeros);
  void test_count_aux(const std::string& val, bool leading, bool zeros);
  void test_unary_aux(BvFunKind fun_kind,
                      Kind kind,
                      const BitVector& bv);
  void test_unary(BvFunKind fun_kind, Kind kind);
  void test_binary_aux(BvFunKind fun_kind,
                       Kind kind,
                       const BitVector& bv0,
                       const BitVector& bv1);
  void test_binary(BvFunKind fun_kind, Kind kind);
  void test_binary_signed_aux(BvFunKind fun_kind,
                              Kind kind,
                              const BitVector& bv0,
                              const BitVector& bv1);
  void test_binary_signed(BvFunKind fun_kind, Kind kind);
  void test_concat_aux(BvFunKind fun_kind,
                       const BitVector& bv0,
                       const BitVector& bv1);
  void test_concat(BvFunKind fun_kind);
  void test_extend_aux(BvFunKind fun_kind,
                       Kind kind,
                       const BitVector& bv,
                       uint64_t n);
  void test_extend(BvFunKind fun_kind, Kind kind);
  void test_repeat_aux(BvFunKind fun_kind, const BitVector& bv, uint64_t n);
  void test_repeat(BvFunKind fun_kind);
  void test_extract_aux(BvFunKind fun_kind, const BitVector& bv);
  void test_extract(BvFunKind fun_kind);
  void test_is_neg_overflow_aux(uint64_t size,
                                const std::string& s1,
                                bool expected);
  void test_is_neg_overflow(uint64_t size);
  void test_is_uadd_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_uadd_overflow(uint64_t size);
  void test_is_sadd_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_sadd_overflow(uint64_t size);
  void test_is_ssub_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_ssub_overflow(uint64_t size);
  void test_is_usub_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_usub_overflow(uint64_t size);
  void test_is_umul_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_umul_overflow(uint64_t size);
  void test_is_smul_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_smul_overflow(uint64_t size);
  void test_is_sdiv_overflow_aux(uint64_t size,
                                 const std::string& s1,
                                 const std::string& s2,
                                 bool expected);
  void test_is_sdiv_overflow(uint64_t size);
  void test_ite_aux(BvFunKind fun_kind,
                    const BitVector& bv0,
                    const BitVector& b1,
                    const BitVector& bv2);
  void test_ite(BvFunKind fun_kind);
  void test_modinv_aux(BvFunKind fun_kind, const BitVector& bv);
  void test_modinv(BvFunKind fun_kind);
  void test_shift_aux(BvFunKind fun_kind,
                      Kind kind,
                      const std::string& to_shift,
                      const std::string& shift,
                      const std::string& expected,
                      bool shift_by_int);
  void test_shift(BvFunKind fun_kind, Kind kind, bool shift_by_int);
  void test_rotate_aux(BvFunKind fun_kind,
                       Kind kind,
                       const BitVector& bv,
                       uint64_t n);
  void test_rotate_aux(BvFunKind fun_kind,
                       Kind kind,
                       const BitVector& bv,
                       const BitVector& n);
  void test_rotate(BvFunKind fun_kind, Kind kind);
  void test_udivurem(uint64_t size);
  std::unique_ptr<RNG> d_rng;
};

uint64_t
TestBitVector::normalize_uint64(uint64_t size, uint64_t value)
{
  return size > 63 ? value
                   : (value % (uint64_t) pow(2, static_cast<double>(size)));
}

int64_t
TestBitVector::normalize_int64(uint64_t size, int64_t value)
{
  return size > 63 ? value
                   : (value % (int64_t) pow(2, static_cast<double>(size)));
}

uint64_t
TestBitVector::_not(uint64_t x, uint64_t size)
{
  return normalize_uint64(size, ~x);
}

uint64_t
TestBitVector::_neg(uint64_t x, uint64_t size)
{
  return normalize_uint64(size, -x);
}

uint64_t
TestBitVector::_nego(uint64_t x, uint64_t size)
{
  /* we only test values representable in 64 bits */
  if (size >= 64)
  {
    size = 63;
  }
  return normalize_uint64(size, static_cast<uint64_t>(1) << (size - 1)) == x;
}

uint64_t
TestBitVector::_redand(uint64_t x, uint64_t size)
{
  uint64_t a = UINT64_MAX;
  /* we only test values representable in 64 bits */
  if (size < 64)
  {
    a = a << size;
  }
  return (x + a) == UINT64_MAX;
}

uint64_t
TestBitVector::_redor(uint64_t x, uint64_t size)
{
  (void) size;
  return x != 0;
}

uint64_t
TestBitVector::_redxor(uint64_t x, uint64_t size)
{
  (void) size;
  uint64_t res = 0;
  for (uint64_t i = 0; i < size && i < 64; ++i)
  {
    uint64_t shift = 64 - 1 - i;
    res            = res ^ ((x << shift) >> (shift + i));
  }
  assert(res == 0 || res == 1);
  return res;
}

uint64_t
TestBitVector::_inc(uint64_t x, uint64_t size)
{
  return normalize_uint64(size, x + 1);
}

uint64_t
TestBitVector::_dec(uint64_t x, uint64_t size)
{
  return normalize_uint64(size, x - 1);
}

uint64_t
TestBitVector::_add(uint64_t x, uint64_t y, uint64_t size)
{
  return normalize_uint64(size, x + y);
}

uint64_t
TestBitVector::_uaddo(uint64_t x, uint64_t y, uint64_t size)
{
  return (size == 64 && (x + y < x || x + y < y))
         || (size < 64 && x + y > normalize_uint64(size, ~0));
}

uint64_t
TestBitVector::_saddo(int64_t x, int64_t y, uint64_t size)
{
  if (size < 64)
  {
    return x + y < -std::pow(2, size - 1)
           || x + y > static_cast<int64_t>(normalize_uint64(size - 1, ~0));
  }
  return y != 0 && x != 0 && (x + y) - y != x;
}

uint64_t
TestBitVector::_usubo(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x < y;
}

uint64_t
TestBitVector::_ssubo(int64_t x, int64_t y, uint64_t size)
{
  if (size < 64)
  {
    return x - y < -std::pow(2, size - 1)
           || x - y > static_cast<int64_t>(normalize_uint64(size - 1, ~0));
  }
  return y != 0 && x != 0 && (x - y) + y != x;
}

uint64_t
TestBitVector::_umulo(uint64_t x, uint64_t y, uint64_t size)
{
  if (size == 64)
  {
    return y != 0 && x != 0 && x * y / y != x;
  }
  return (size > 32 && x != 0 && y != 0 && (x * y < x || x * y < y))
         || (size <= 32 && x * y > normalize_uint64(size, ~0));
}

__attribute__((no_sanitize("signed-integer-overflow"))) uint64_t
TestBitVector::_smulo(int64_t x, int64_t y, uint64_t size)
{
  if (size == 1)
  {
    return x == -1 && y == -1;
  }
  if (size < 64)
  {
    int128_t _x  = x;
    int128_t _y  = y;
    int128_t mul = _x * _y;
    return mul < static_cast<int128_t>(-std::pow(2, size - 1))
           || mul > static_cast<int64_t>(
                  normalize_uint64(size - 1, ~((uint64_t) 0)));
  }
  return y != 0 && x != 0 && x * y / y != x;
}

uint64_t
TestBitVector::_sdivo(int64_t x, int64_t y, uint64_t size)
{
  return x == -std::pow(2, size - 1) && y == -1;
}

uint64_t
TestBitVector::_sub(uint64_t x, uint64_t y, uint64_t size)
{
  return normalize_uint64(size, x - y);
}

uint64_t
TestBitVector::_and(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x & y;
}

uint64_t
TestBitVector::_nand(uint64_t x, uint64_t y, uint64_t size)
{
  uint64_t res = ~(x & y);
  if (size < 64)
  {
    uint64_t shift = 64 - size;
    res            = ((res << shift) >> shift);
  }
  return res;
}

uint64_t
TestBitVector::_or(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x | y;
}

uint64_t
TestBitVector::_nor(uint64_t x, uint64_t y, uint64_t size)
{
  uint64_t res = ~(x | y);
  if (size < 64)
  {
    uint64_t shift = 64 - size;
    res            = (res << shift) >> shift;
  }
  return res;
}

uint64_t
TestBitVector::_xnor(uint64_t x, uint64_t y, uint64_t size)
{
  uint64_t res = ~(x ^ y);
  if (size < 64)
  {
    uint64_t shift = 64 - size;
    res            = (res << shift) >> shift;
  }
  return res;
}

uint64_t
TestBitVector::_implies(uint64_t x, uint64_t y, uint64_t size)
{
  assert(size == 1);
  (void) size;
  return ((~x | y) << 63) >> 63;
}

uint64_t
TestBitVector::_xor(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x ^ y;
}

uint64_t
TestBitVector::_eq(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x == y;
}

uint64_t
TestBitVector::_ne(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x != y;
}

uint64_t
TestBitVector::_ult(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x < y;
}

uint64_t
TestBitVector::_ule(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x <= y;
}

uint64_t
TestBitVector::_ugt(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x > y;
}

uint64_t
TestBitVector::_uge(uint64_t x, uint64_t y, uint64_t size)
{
  (void) size;
  return x >= y;
}

int64_t
TestBitVector::_slt(int64_t x, int64_t y, uint64_t size)
{
  (void) size;
  return x < y;
}

int64_t
TestBitVector::_sle(int64_t x, int64_t y, uint64_t size)
{
  (void) size;
  return x <= y;
}

int64_t
TestBitVector::_sgt(int64_t x, int64_t y, uint64_t size)
{
  (void) size;
  return x > y;
}

int64_t
TestBitVector::_sge(int64_t x, int64_t y, uint64_t size)
{
  (void) size;
  return x >= y;
}

uint64_t
TestBitVector::_shl(uint64_t x, uint64_t y, uint64_t size)
{
  if (y >= size) return 0;
  return normalize_uint64(size, x << y);
}

uint64_t
TestBitVector::_shr(uint64_t x, uint64_t y, uint64_t size)
{
  if (y >= size) return 0;
  return normalize_uint64(size, x >> y);
}

uint64_t
TestBitVector::_ashr(uint64_t x, uint64_t y, uint64_t size)
{
  size = size > 64 ? 64 : size;
  if ((x >> (size - 1)) & 1)
  {
    if (y > size) return normalize_uint64(size, ~0ull);
    return normalize_uint64(size, ~(normalize_uint64(size, ~x) >> y));
  }
  if (y > size) return 0;
  return normalize_uint64(size, x >> y);
}

uint64_t
TestBitVector::_mul(uint64_t x, uint64_t y, uint64_t size)
{
  return normalize_uint64(size, x * y);
}

uint64_t
TestBitVector::_udiv(uint64_t x, uint64_t y, uint64_t size)
{
  if (y == 0) return normalize_uint64(size, UINT64_MAX);
  return normalize_uint64(size, x / y);
}

uint64_t
TestBitVector::_urem(uint64_t x, uint64_t y, uint64_t size)
{
  if (y == 0) return x;
  return normalize_uint64(size, x % y);
}

int64_t
TestBitVector::_sdiv(int64_t x, int64_t y, uint64_t size)
{
  if (y == 0)
  {
    return x < 0 ? 1 : static_cast<int64_t>(normalize_uint64(size, UINT64_MAX));
  }
  return normalize_int64(size, x / y);
}

int64_t
TestBitVector::_srem(int64_t x, int64_t y, uint64_t size)
{
  if (y == 0) return normalize_int64(size, x);
  return normalize_int64(size, x % y);
}

int64_t
TestBitVector::_smod(int64_t x, int64_t y, uint64_t size)
{
  if (y == 0) return normalize_int64(size, x);
  int64_t urem = normalize_int64(size, (x < 0 ? -x : x) % (y < 0 ? -y : y));
  if (urem == 0 || (x > 0 && y > 0))
  {
    return urem;
  }
  if (x < 0 && y > 0)
  {
    return normalize_int64(size, -urem + y);
  }
  if (x > 0 && y < 0)
  {
    return normalize_int64(size, urem + y);
  }
  return normalize_int64(size, -urem);
}

uint64_t
TestBitVector::_ite(uint64_t c, uint64_t t, uint64_t e, uint64_t size)
{
  (void) size;
  return c ? t : e;
}

BitVector
TestBitVector::mk_ones(uint64_t size)
{
  if (size <= 64)
  {
    return BitVector(size, std::string(size, '1'), 2);
  }
  BitVector r = BitVector::from_ui(64, UINT64_MAX);
  BitVector l(size - 64, std::string(size - 64, '1'), 2);
  return l.bvconcat(r);
}

BitVector
TestBitVector::mk_min_signed(uint64_t size)
{
  if (size <= 64)
  {
    return BitVector::from_ui(size, ((uint64_t) 1) << (size - 1));
  }
  BitVector r = BitVector::from_ui(64, 0);
  BitVector l =
      BitVector::from_ui(size - 64, ((uint64_t) 1) << (size - 1 - 64));
  return l.bvconcat(r);
}

BitVector
TestBitVector::mk_max_signed(uint64_t size)
{
  if (size <= 64)
  {
    return BitVector::from_ui(size, (((uint64_t) 1) << (size - 1)) - 1);
  }
  BitVector r = BitVector::from_ui(64, UINT64_MAX);
  BitVector l =
      BitVector::from_ui(size - 64, (((uint64_t) 1) << (size - 1 - 64)) - 1);
  return l.bvconcat(r);
}

std::string
TestBitVector::to_bin_string(uint64_t size, uint64_t val)
{
  switch (size)
  {
    case 1: return std::bitset<1>(val).to_string();
    case 2: return std::bitset<2>(val).to_string();
    case 3: return std::bitset<3>(val).to_string();
    case 8: return std::bitset<8>(val).to_string();
    case 64: return std::bitset<64>(val).to_string();
    case 65: return std::bitset<65>(val).to_string();
    case 128: return std::bitset<128>(val).to_string();

    default: assert(false);
  }
  return std::string();
}

void
TestBitVector::test_ctor_random_bit_range(uint64_t size)
{
  for (uint32_t i = 0; i < N_TESTS; ++i)
  {
    uint64_t up, lo;
    lo = d_rng->pick<uint64_t>(0, size - 1);
    up = lo == size - 1 ? size - 1 : d_rng->pick<uint64_t>(lo + 1, size - 1);
    BitVector bv1(size, *d_rng, up, lo);
    BitVector bv2(size, *d_rng, up, lo);
    BitVector bv3(size, *d_rng, up, lo);
    for (uint64_t j = lo; j <= up; ++j)
    {
      if (bv1.bit(j) != bv2.bit(j) || bv1.bit(j) != bv3.bit(j)
          || bv2.bit(j) != bv3.bit(j))
      {
        break;
      }
    }
    for (uint64_t j = 0; j < lo; ++j)
    {
      ASSERT_EQ(bv1.bit(j), 0);
      ASSERT_EQ(bv2.bit(j), 0);
      ASSERT_EQ(bv3.bit(j), 0);
    }
    for (uint64_t j = up + 1; j < size; j++)
    {
      ASSERT_EQ(bv1.bit(j), 0);
      ASSERT_EQ(bv2.bit(j), 0);
      ASSERT_EQ(bv3.bit(j), 0);
    }
  }
}

void
TestBitVector::test_count_aux(const std::string& val, bool leading, bool zeros)
{
  uint64_t size     = val.size();
  uint64_t expected = 0;
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
TestBitVector::test_count(uint64_t size, bool leading, bool zeros)
{
  if (size == 8)
  {
    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      test_count_aux(to_bin_string(8, i), leading, zeros);
    }
  }
  else
  {
    for (uint64_t i = 0; i < (1u << 8); ++i)
    {
      // concat 8-bit value with 0s to create value for bv
      test_count_aux(
          to_bin_string(8, i) + std::string(size - 8, '0'), leading, zeros);
      test_count_aux(
          std::string(size - 8, '0') + to_bin_string(8, i), leading, zeros);
      test_count_aux(
          to_bin_string(8, i) + std::string(size - 16, '0'), leading, zeros);
      // concat 8-bit values with 1s to create value for bv
      test_count_aux(
          to_bin_string(8, i) + std::string(size - 8, '1'), leading, zeros);
      test_count_aux(
          std::string(size - 8, '1') + to_bin_string(8, i), leading, zeros);
      test_count_aux(
          to_bin_string(8, i) + std::string(size - 16, '1'), leading, zeros);
    }
  }
}

void
TestBitVector::test_extend_aux(BvFunKind fun_kind,
                               Kind kind,
                               const BitVector& bv,
                               uint64_t n)
{
  uint64_t size = bv.size();
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind == DEFAULT || fun_kind == INPLACE)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }
  char c = 0;

  for (auto& res : reses)
  {
    switch (kind)
    {
      case ZEXT:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvzext(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvzext(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvzext(res, n);
        }
        else
        {
          res = bv.bvzext(n);
        }
        c = '0';
        break;
      case SEXT:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvsext(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvsext(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvsext(res, n);
        }
        else
        {
          res = bv.bvsext(n);
        }
        c = bv.msb() ? '1' : '0';
        break;

      default: assert(false);
    }
    ASSERT_EQ(size + n, res.size());
    std::string res_str = res.str();
    std::string bv_str  = bv.str();
    uint64_t len        = size - n;
    ASSERT_EQ(bv_str.compare(0, len, res_str, n, len), 0);
    ASSERT_EQ(std::string(n, c).compare(0, n, res_str, 0, n), 0);
  }
}

void
TestBitVector::test_extend(BvFunKind fun_kind, Kind kind)
{
  /* test all values for bit-widths 2 - 8 */
  for (uint64_t size = 2; size <= 8; ++size)
  {
    uint64_t n = d_rng->pick<uint64_t>(0, size - 1);
    uint64_t s = size - n;
    for (uint64_t i = 0, m = 1 << s; i < m; ++i)
    {
      test_extend_aux(fun_kind, kind, BitVector::from_ui(s, i), n);
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      uint64_t n = d_rng->pick<uint64_t>(0, size - 1);
      if (size > 64)
      {
        test_extend_aux(fun_kind, kind, BitVector(size - n, *d_rng, 63, 0), n);
      }
      else
      {
        test_extend_aux(fun_kind, kind, BitVector(size - n, *d_rng), n);
      }
    }
  }
}

void
TestBitVector::test_repeat_aux(BvFunKind fun_kind,
                               const BitVector& bv,
                               uint64_t n)
{
  uint64_t size = bv.size();
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind == DEFAULT || fun_kind == INPLACE)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }

  for (auto& res : reses)
  {
    if (fun_kind == INPLACE)
    {
      (void) res.ibvrepeat(bv, n);
    }
    else if (fun_kind == INPLACE_THIS)
    {
      (void) res.ibvrepeat(n);
    }
    else if (fun_kind == INPLACE_THIS_ALL)
    {
      // test with *this as argument
      (void) res.ibvrepeat(res, n);
    }
    else
    {
      res = bv.bvrepeat(n);
    }
    ASSERT_EQ(size * n, res.size());
    std::string res_str = res.str();
    std::stringstream exp_str;
    for (uint64_t i = 0; i < n; ++i)
    {
      exp_str << bv.str();
    }
    ASSERT_EQ(res_str, exp_str.str());
  }
}

void
TestBitVector::test_repeat(BvFunKind fun_kind)
{
  /* test all values for bit-widths 2 - 8 */
  for (uint64_t size = 2; size <= 8; ++size)
  {
    uint64_t n = d_rng->pick<uint64_t>(1, size - 1);
    uint64_t s = size - n;
    for (uint64_t i = 0, m = 1 << s; i < m; ++i)
    {
      test_repeat_aux(fun_kind, BitVector::from_ui(s, i), n);
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      uint64_t n = d_rng->pick<uint64_t>(1, size - 1);
      if (size > 64)
      {
        test_repeat_aux(fun_kind, BitVector(size - n, *d_rng, 63, 0), n);
      }
      else
      {
        test_repeat_aux(fun_kind, BitVector(size - n, *d_rng), n);
      }
    }
  }
}

void
TestBitVector::test_is_neg_overflow_aux(uint64_t size,
                                        const std::string& s1,
                                        bool expected)
{
  BitVector bv1(size, s1, 2);
  ASSERT_EQ(bv1.is_neg_overflow(), expected);
}

void
TestBitVector::test_is_neg_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_neg_overflow_aux(size, "0", false);
      test_is_neg_overflow_aux(size, "1", true);
      break;
    case 7:
      test_is_neg_overflow_aux(size, "0100000", false);
      test_is_neg_overflow_aux(size, "1000000", true);
      break;
    case 31:
      test_is_neg_overflow_aux(size, "1000000000000000000000000001111", false);
      test_is_neg_overflow_aux(size, "1000000000000000000000000000000", true);
      break;
    case 64:
      test_is_neg_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111",
          false);
      test_is_neg_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000",
          false);
      break;
    case 65:
      test_is_neg_overflow_aux(
          size,
          "100000000111111111111111111111111111111111111111111111111111110",
          false);
      test_is_neg_overflow_aux(
          size,
          "100000000000000000000000000000000000000000000000000000000000000",
          false);
      break;
    case 127:
      test_is_neg_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          false);
      test_is_neg_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000000",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_uadd_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 10);
  BitVector bv2(size, s2, 10);
  ASSERT_EQ(bv1.is_uadd_overflow(bv2), expected);
}

void
TestBitVector::test_is_uadd_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_uadd_overflow_aux(size, "0", "0", false);
      test_is_uadd_overflow_aux(size, "0", "1", false);
      test_is_uadd_overflow_aux(size, "1", "0", false);
      test_is_uadd_overflow_aux(size, "1", "1", true);
      break;
    case 7:
      test_is_uadd_overflow_aux(size, "3", "6", false);
      test_is_uadd_overflow_aux(size, "126", "2", true);
      break;
    case 31:
      test_is_uadd_overflow_aux(size, "15", "78", false);
      test_is_uadd_overflow_aux(size, "2147483647", "2147483647", true);
      break;
    case 64:
      test_is_uadd_overflow_aux(size, "18446744073709551614", "1", false);
      test_is_uadd_overflow_aux(size, "18446744073709551614", "2", true);
      break;
    case 65:
      test_is_uadd_overflow_aux(size, "36893488147419103230", "1", false);
      test_is_uadd_overflow_aux(size, "36893488147419103230", "2", true);
      break;
    case 127:
      test_is_uadd_overflow_aux(
          size, "170141183460469231731687303715884105726", "1", false);
      test_is_uadd_overflow_aux(
          size, "170141183460469231731687303715884105726", "2", true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_sadd_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 2);
  BitVector bv2(size, s2, 2);
  ASSERT_EQ(bv1.is_sadd_overflow(bv2), expected);
}

void
TestBitVector::test_is_sadd_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_sadd_overflow_aux(size, "0", "0", false);
      test_is_sadd_overflow_aux(size, "0", "1", false);
      test_is_sadd_overflow_aux(size, "1", "1", true);
      break;
    case 7:
      test_is_sadd_overflow_aux(size, "0000011", "0000110", false);
      test_is_sadd_overflow_aux(size, "1111110", "1010101", false);
      test_is_sadd_overflow_aux(size, "1111110", "1000001", true);
      break;
    case 31:
      test_is_sadd_overflow_aux(size,
                                "0000000000000000000000000001111",
                                "0000000000000000000000001001110",
                                false);
      test_is_sadd_overflow_aux(size,
                                "0111111111111111111111111111111",
                                "0000000000000000000000001001110",
                                true);
      test_is_sadd_overflow_aux(size,
                                "1100000000000000000000000000000",
                                "1000000000000000000000000000001",
                                true);
      break;
    case 64:
      test_is_sadd_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_sadd_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000100",
          true);
      test_is_sadd_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111110",
          "1000000000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    case 65:
      test_is_sadd_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_sadd_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111010",
          "00000000000000000000000000000000000000000000000000000000100000001",
          true);
      test_is_sadd_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000000",
          "10000000000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    case 127:
      test_is_sadd_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_sadd_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "00000000000000000000000100000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      test_is_sadd_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_sadd_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000000",
          "10000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_usub_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 2);
  BitVector bv2(size, s2, 2);
  ASSERT_EQ(bv1.is_usub_overflow(bv2), expected);
}

void
TestBitVector::test_is_usub_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_usub_overflow_aux(size, "0", "0", false);
      test_is_usub_overflow_aux(size, "0", "1", true);
      test_is_usub_overflow_aux(size, "1", "1", false);
      break;
    case 7:
      test_is_usub_overflow_aux(size, "0000011", "0000110", true);
      test_is_usub_overflow_aux(size, "1111110", "1010101", false);
      test_is_usub_overflow_aux(size, "1111110", "0111111", false);
      break;
    case 31:
      test_is_usub_overflow_aux(size,
                                "0000000000000000000000000001111",
                                "0000000000000000000000001001110",
                                true);
      test_is_usub_overflow_aux(size,
                                "1111111111111111111111111111111",
                                "0000000000000000000000001001110",
                                false);
      test_is_usub_overflow_aux(size,
                                "1100000000000000000000000000000",
                                "1000000000000000000000000000001",
                                false);
      test_is_usub_overflow_aux(size,
                                "0111111111111111111111111111111",
                                "1000000000000000000000001001110",
                                true);
      test_is_usub_overflow_aux(size,
                                "1100000000000000000000000000000",
                                "0100000000000000000000000000001",
                                false);
      break;
    case 64:
      test_is_usub_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_usub_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000100",
          false);
      test_is_usub_overflow_aux(
          size,
          "1011111111111111111111111111111111111111111111111111111111111110",
          "0110000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_usub_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111110",
          "1010000000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    case 65:
      test_is_usub_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_usub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111010",
          "11100000000000000000000000000000000000000000000000000000100000001",
          true);
      test_is_usub_overflow_aux(
          size,
          "10100010000100000100001000000000000000000000000000000000000000000",
          "01111111111111111111111111111111111111100000000000000000000000001",
          false);
      break;
    case 127:
      test_is_usub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_usub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "10000000000000000000000100000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      test_is_usub_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_usub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111100000"
          "00000000000000000000000000000000000000000000000000000000000",
          "10000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_ssub_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 2);
  BitVector bv2(size, s2, 2);
  ASSERT_EQ(bv1.is_ssub_overflow(bv2), expected);
}

void
TestBitVector::test_is_ssub_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_ssub_overflow_aux(size, "0", "0", false);
      test_is_ssub_overflow_aux(size, "0", "1", true);
      test_is_ssub_overflow_aux(size, "1", "1", false);
      break;
    case 7:
      test_is_ssub_overflow_aux(size, "0000011", "0000110", false);
      test_is_ssub_overflow_aux(size, "1111110", "1010101", false);
      test_is_ssub_overflow_aux(size, "1111110", "0111111", true);
      break;
    case 31:
      test_is_ssub_overflow_aux(size,
                                "0000000000000000000000000001111",
                                "0000000000000000000000001001110",
                                false);
      test_is_ssub_overflow_aux(size,
                                "1111111111111111111111111111111",
                                "0000000000000000000000001001110",
                                false);
      test_is_ssub_overflow_aux(size,
                                "1100000000000000000000000000000",
                                "1000000000000000000000000000001",
                                false);
      test_is_ssub_overflow_aux(size,
                                "0111111111111111111111111111111",
                                "1000000000000000000000001001110",
                                true);
      test_is_ssub_overflow_aux(size,
                                "1100000000000000000000000000000",
                                "0100000000000000000000000000001",
                                true);
      break;
    case 64:
      test_is_ssub_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_ssub_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111110",
          "0000000000000000000000000000000000000000000000000000000000000100",
          false);
      test_is_ssub_overflow_aux(
          size,
          "1011111111111111111111111111111111111111111111111111111111111110",
          "0110000000000000000000000000000000000000000000000000000000000001",
          true);
      test_is_ssub_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111110",
          "1010000000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    case 65:
      test_is_ssub_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_ssub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111010",
          "11100000000000000000000000000000000000000000000000000000100000001",
          true);
      test_is_ssub_overflow_aux(
          size,
          "10100010000100000100001000000000000000000000000000000000000000000",
          "01111111111111111111111111111111111111100000000000000000000000001",
          true);
      break;
    case 127:
      test_is_ssub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_ssub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111001",
          "10000000000000000000000100000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      test_is_ssub_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111110",
          "00000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          false);
      test_is_ssub_overflow_aux(
          size,
          "01111111111111111111111111111111111111111111111111111111111111100000"
          "00000000000000000000000000000000000000000000000000000000000",
          "10000000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000001",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_umul_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 10);
  BitVector bv2(size, s2, 10);
  ASSERT_EQ(bv1.is_umul_overflow(bv2), expected);
}

void
TestBitVector::test_is_umul_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_umul_overflow_aux(size, "0", "0", false);
      test_is_umul_overflow_aux(size, "0", "1", false);
      test_is_umul_overflow_aux(size, "1", "1", false);
      break;
    case 7:
      test_is_umul_overflow_aux(size, "3", "6", false);
      test_is_umul_overflow_aux(size, "124", "2", true);
      break;
    case 31:
      test_is_umul_overflow_aux(size, "15", "78", false);
      test_is_umul_overflow_aux(size, "1073742058", "2", true);
      break;
    case 64:
      test_is_umul_overflow_aux(size, "9223372036854775805", "2", false);
      test_is_umul_overflow_aux(size, "18446744073709551615", "2", true);
      break;
    case 65:
      test_is_umul_overflow_aux(size, "18446744073709551615", "2", false);
      test_is_umul_overflow_aux(size, "36893488147419103231", "2", true);
      break;
    case 127:
      test_is_umul_overflow_aux(
          size, "85070591730234615865843651857942052863", "2", false);
      test_is_umul_overflow_aux(
          size, "170141183460469231731687303715884105727", "2", true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_smul_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 2);
  BitVector bv2(size, s2, 2);
  ASSERT_EQ(bv1.is_smul_overflow(bv2), expected);
}

void
TestBitVector::test_is_smul_overflow(uint64_t size)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(size).is_smul_overflow(BitVector(size + 1, *d_rng)),
      "d_size == bv.d_size");
  switch (size)
  {
    case 1:
      test_is_smul_overflow_aux(size, "0", "0", false);
      test_is_smul_overflow_aux(size, "0", "1", false);
      test_is_smul_overflow_aux(size, "1", "0", false);
      test_is_smul_overflow_aux(size, "1", "1", true);
      break;
    case 7:
      test_is_smul_overflow_aux(size, "0000011", "0000110", false);
      test_is_smul_overflow_aux(size, "0111111", "0000110", true);
      test_is_smul_overflow_aux(size, "1111111", "0000110", false);
      test_is_smul_overflow_aux(size, "1000000", "0000110", true);
      test_is_smul_overflow_aux(size, "0111100", "1010110", true);
      test_is_smul_overflow_aux(size, "1000000", "1000110", true);
      break;
    case 31:
      test_is_smul_overflow_aux(size,
                                "0000000000000000000000000001111",
                                "0000000000000000000000001001110",
                                false);
      test_is_smul_overflow_aux(size,
                                "1000000000000000000000011101010",
                                "0000000000000000000000000000010",
                                true);
      test_is_smul_overflow_aux(size,
                                "1000000000000000000000011101010",
                                "0111111111111111111111110000010",
                                true);
      test_is_smul_overflow_aux(size,
                                "1000000000000000000000000001010",
                                "1111111111111111111111111111110",
                                true);
      test_is_smul_overflow_aux(size,
                                "1111111111111111111111111101010",
                                "1111111111111111111111111111110",
                                false);
      test_is_smul_overflow_aux(size,
                                "1000000000000000000000011101010",
                                "1000000000000000000000000000010",
                                true);
      break;
    case 64:
      test_is_smul_overflow_aux(
          size,
          "0000000000000000000000000000000000000000000111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_smul_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          true);
      test_is_smul_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_smul_overflow_aux(
          size,
          "1000000000000000000000000000000000000000000000000000000000001101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          true);
      break;
    case 65:
      test_is_smul_overflow_aux(
          size,
          "00000000000000000000000000000000000000000000111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000011",
          false);
      test_is_smul_overflow_aux(
          size,
          "00111111111111111111111111111111111111111111111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000110",
          true);
      test_is_smul_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000011",
          false);
      test_is_smul_overflow_aux(
          size,
          "11000000000000000000000000000000000000000000000000000000000001101",
          "00000000000000000000000000000100000000000000000000000000000000010",
          true);
      break;
    case 127:
      test_is_smul_overflow_aux(
          size,
          "00000000000000000000000000000000000000000000000000000000000000000"
          "11000000000000000000000000000000000000000000000000000000000001",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000100000000000000000000000000000010",
          false);
      test_is_smul_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_smul_overflow_aux(
          size,
          "11000000000000000000000000000000000000000000000000000000000001101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000100000000000000000000000000000010",
          true);
      test_is_smul_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "11111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111111010",
          false);
      test_is_smul_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000001"
          "11000000000000000000000000000000000000000000000000000000001101",
          "11111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111100000000000000011111010",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_is_sdiv_overflow_aux(uint64_t size,
                                         const std::string& s1,
                                         const std::string& s2,
                                         bool expected)
{
  BitVector bv1(size, s1, 2);
  BitVector bv2(size, s2, 2);
  ASSERT_EQ(bv1.is_sdiv_overflow(bv2), expected);
}

void
TestBitVector::test_is_sdiv_overflow(uint64_t size)
{
  switch (size)
  {
    case 1:
      test_is_sdiv_overflow_aux(size, "0", "0", false);
      test_is_sdiv_overflow_aux(size, "0", "1", false);
      test_is_sdiv_overflow_aux(size, "1", "0", false);
      test_is_sdiv_overflow_aux(size, "1", "1", true);
      break;
    case 7:
      test_is_sdiv_overflow_aux(size, "0000011", "0000110", false);
      test_is_sdiv_overflow_aux(size, "0111111", "0000110", false);
      test_is_sdiv_overflow_aux(size, "1111111", "0000110", false);
      test_is_sdiv_overflow_aux(size, "1000000", "0000110", false);
      test_is_sdiv_overflow_aux(size, "0111100", "1010110", false);
      test_is_sdiv_overflow_aux(size, "1000000", "1111111", true);
      break;
    case 31:
      test_is_sdiv_overflow_aux(size,
                                "0000000000000000000000000001111",
                                "0000000000000000000000001001110",
                                false);
      test_is_sdiv_overflow_aux(size,
                                "1000000000000000000000011101010",
                                "0000000000000000000000000000010",
                                false);
      test_is_sdiv_overflow_aux(size,
                                "1000000000000000000000011101010",
                                "0111111111111111111111110000010",
                                false);
      test_is_sdiv_overflow_aux(size,
                                "1000000000000000000000000001010",
                                "1111111111111111111111111111110",
                                false);
      test_is_sdiv_overflow_aux(size,
                                "1111111111111111111111111101010",
                                "1111111111111111111111111111110",
                                false);
      test_is_sdiv_overflow_aux(size,
                                "1000000000000000000000000000000",
                                "1111111111111111111111111111111",
                                true);
      break;
    case 64:
      test_is_sdiv_overflow_aux(
          size,
          "0000000000000000000000000000000000000000000111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "0111111111111111111111111111111111111111111111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "1111111111111111111111111111111111111111111111111111111111111101",
          "0000000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "1000000000000000000000000000000000000000000000000000000000000000",
          "1111111111111111111111111111111111111111111111111111111111111111",
          true);
      break;
    case 65:
      test_is_sdiv_overflow_aux(
          size,
          "00000000000000000000000000000000000000000000111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000011",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "00111111111111111111111111111111111111111111111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000110",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101",
          "00000000000000000000000000000000000000000000000000000000000000011",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000000",
          "11111111111111111111111111111111111111111111111111111111111111111",
          true);
      break;
    case 127:
      test_is_sdiv_overflow_aux(
          size,
          "00000000000000000000000000000000000000000000000000000000000000000"
          "11000000000000000000000000000000000000000000000000000000000001",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000100000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "11000000000000000000000000000000000000000000000000000000000001101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "00000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000100000000000000000000000000000010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "11111111111111111111111111111111111111111111111111111111111111101"
          "11000000000000000000000000000000000000000000000000000000001101",
          "11111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111111010",
          false);
      test_is_sdiv_overflow_aux(
          size,
          "10000000000000000000000000000000000000000000000000000000000000000"
          "00000000000000000000000000000000000000000000000000000000000000",
          "11111111111111111111111111111111111111111111111111111111111111111"
          "11111111111111111111111111111111111111111111111111111111111111",
          true);
      break;
    default: assert(false);
  }
}

void
TestBitVector::test_ite_aux(BvFunKind fun_kind,
                            const BitVector& bv0,
                            const BitVector& bv1,
                            const BitVector& bv2)
{
  assert(bv0.size() == 1);
  assert(bv1.size() == bv2.size());
  uint64_t size = bv1.size();
  BitVector b0(bv0);
  BitVector b1(bv1);
  BitVector b2(bv2);
  std::vector<BitVector> reses{BitVector(size)};
  if (fun_kind != INPLACE_THIS)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }

  uint64_t a0 = b0.to_uint64();
  /* we only test values representable in 64 bits */
  uint64_t a1    = size > 64 ? b1.bvextract(63, 0).to_uint64() : b1.to_uint64();
  uint64_t a2    = size > 64 ? b2.bvextract(63, 0).to_uint64() : b2.to_uint64();
  uint64_t ares  = _ite(a0, a1, a2, size);
  uint64_t atres = _ite(a0, a1, a1, size);

  for (auto& res : reses)
  {
    if (fun_kind == INPLACE_THIS_ALL)
    {
      (void) res.ibvite(b0, b1, b2);
      // test with *this as arguments
      BitVector tres0(b0);
      BitVector tres1(b1);
      (void) tres0.ibvite(tres0, b1, b2);
      (void) tres1.ibvite(b0, tres1, tres1);
      ASSERT_TRUE(BitVector::from_ui(tres0.size(), ares).compare(tres0) == 0);
      ASSERT_TRUE(BitVector::from_ui(tres0.size(), atres).compare(tres1) == 0);
    }
    else
    {
      assert(fun_kind == DEFAULT);
      res = BitVector::bvite(b0, b1, b2);
    }

    ASSERT_EQ(BitVector::from_ui(res.size(), ares).compare(res), 0);
  }
}

void
TestBitVector::test_ite(BvFunKind fun_kind)
{
  /* test all values for bit-widths 1 - 4 */
  for (uint64_t k = 0; k < 2; ++k)
  {
    for (uint64_t size = 1; size <= 4; ++size)
    {
      for (uint64_t i = 0, n = 1 << size; i < n; ++i)
      {
        for (uint64_t j = 0, m = 1 << size; j < m; ++j)
        {
          test_ite_aux(fun_kind,
                       BitVector::from_ui(1, k),
                       BitVector::from_ui(size, i),
                       BitVector::from_ui(size, j));
        }
      }
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 31, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      if (size > 64)
      {
        test_ite_aux(fun_kind,
                     BitVector(1, *d_rng),
                     BitVector(size, *d_rng, 63, 0),
                     BitVector(size, *d_rng, 63, 0));
      }
      else
      {
        test_ite_aux(fun_kind,
                     BitVector(1, *d_rng),
                     BitVector(size, *d_rng),
                     BitVector(size, *d_rng));
      }
    }
  }
  /* death tests */
  BitVector b1(1, *d_rng);
  BitVector b8(8, *d_rng);
  BitVector b16(16, *d_rng);
  if (fun_kind == INPLACE_THIS_ALL)
  {
    ASSERT_DEATH_DEBUG(b8.ibvite(b8, b8, b8), "c.d_size == 1");
    ASSERT_DEATH_DEBUG(b8.ibvite(b1, b8, b16), "e.d_size == t.d_size");
    ASSERT_DEATH_DEBUG(b8.ibvite(b1, b16, b8), "e.d_size == t.d_size");
  }
  else
  {
    assert(fun_kind == DEFAULT);
    ASSERT_DEATH_DEBUG(BitVector::bvite(b8, b8, b8), "c.d_size == 1");
    ASSERT_DEATH_DEBUG(BitVector::bvite(b1, b8, b16), "t.d_size == e.d_size");
    ASSERT_DEATH_DEBUG(BitVector::bvite(b1, b16, b8), "t.d_size == e.d_size");
  }
}

void
TestBitVector::test_modinv_aux(BvFunKind fun_kind, const BitVector& bv)
{
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind != INPLACE_THIS)
  {
    reses.push_back(BitVector());
    reses.emplace_back(bv.size() + 1);
  }

  for (auto& res : reses)
  {
    if (fun_kind == INPLACE_THIS)
    {
      (void) res.ibvmodinv();
    }
    else if (fun_kind == INPLACE_THIS_ALL)
    {
      (void) res.ibvmodinv(bv);
      // test with *this as argument
      BitVector tres(bv);
      (void) tres.ibvmodinv(tres);
      ASSERT_TRUE(bv.bvmul(tres).is_one());
    }
    else
    {
      res = bv.bvmodinv();
    }

    ASSERT_TRUE(bv.bvmul(res).is_one());
  }
}

void
TestBitVector::test_modinv(BvFunKind fun_kind)
{
  /* test all values for bit-widths 1 - 4 */
  for (uint64_t size = 1; size <= 4; ++size)
  {
    for (uint64_t i = 0, n = 1 << size; i < n; ++i)
    {
      if ((i & 1) == 0) continue;
      test_modinv_aux(fun_kind, BitVector::from_ui(size, i));
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 31, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      if (size > 64)
      {
        BitVector bv = BitVector(size, *d_rng, 63, 0);
        bv.set_bit(0, 1);  // must be odd
        test_modinv_aux(fun_kind, bv);
      }
      else
      {
        BitVector bv = BitVector(size, *d_rng);
        bv.set_bit(0, 1);  // must be odd
        test_modinv_aux(fun_kind, bv);
      }
    }
  }
}

void
TestBitVector::test_unary_aux(BvFunKind fun_kind,
                              Kind kind,
                              const BitVector& bv)
{
  uint64_t ares = 0;
  uint64_t size = bv.size();
  BitVector b(bv);
  BitVector tres;
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind != INPLACE_THIS)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }
  /* we only test values representable in 64 bits */
  uint64_t a = size > 64 ? bv.bvextract(63, 0).to_uint64() : bv.to_uint64();

  for (auto& res : reses)
  {
    switch (kind)
    {
      case DEC:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvdec();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvdec(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvdec(tres);
        }
        else
        {
          res = b.bvdec();
        }
        ares = _dec(a, size);
        break;

      case INC:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvinc();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvinc(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvinc(tres);
        }
        else
        {
          res = b.bvinc();
        }
        ares = _inc(a, size);
        break;

      case NEG:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvneg();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvneg(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvneg(tres);
        }
        else
        {
          res = b.bvneg();
        }
        ares = _neg(a, size);
        break;

      case NEGO:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvnego();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvnego(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvnego(tres);
        }
        else
        {
          res = b.bvnego();
        }
        ares = _nego(a, size);
        break;

      case NOT:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvnot();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvnot(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvnot(tres);
        }
        else
        {
          res = b.bvnot();
        }
        ares = _not(a, size);
        break;

      case REDAND:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvredand();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvredand(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvredand(tres);
        }
        else
        {
          res = b.bvredand();
        }
        ares = _redand(a, size);
        break;

      case REDOR:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvredor();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvredor(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvredor(tres);
        }
        else
        {
          res = b.bvredor();
        }
        ares = _redor(a, size);
        break;

      case REDXOR:
        if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvredxor();
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          (void) res.ibvredxor(b);
          // test with *this as argument
          tres = bv;
          (void) tres.ibvredxor(tres);
        }
        else
        {
          res = b.bvredxor();
        }
        ares = _redxor(a, size);
        break;

      default: assert(false);
    }
    if (res.size() > 64)
    {
      ASSERT_EQ(BitVector::from_ui(64, ares).compare(res.ibvextract(63, 0)), 0);
      ASSERT_TRUE(
          tres.is_null()
          || BitVector::from_ui(64, ares).compare(tres.ibvextract(63, 0)) == 0);
    }
    else
    {
      ASSERT_EQ(BitVector::from_ui(res.size(), ares).compare(res), 0);
      ASSERT_TRUE(tres.is_null()
                  || BitVector::from_ui(tres.size(), ares).compare(tres) == 0);
    }
  }
}

void
TestBitVector::test_unary(BvFunKind fun_kind, Kind kind)
{
  /* test all values for bit-widths 1 - 4 */
  for (uint64_t size = 1; size <= 4; ++size)
  {
    for (uint64_t i = 0, n = 1 << size; i < n; ++i)
    {
      test_unary_aux(fun_kind, kind, BitVector::from_ui(size, i));
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 31, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      if (size > 64)
      {
        test_unary_aux(fun_kind, kind, BitVector(size, *d_rng, 63, 0));
      }
      else
      {
        test_unary_aux(fun_kind, kind, BitVector(size, *d_rng));
      }
    }
  }
}

void
TestBitVector::test_binary_aux(BvFunKind fun_kind,
                               TestBitVector::Kind kind,
                               const BitVector& bv0,
                               const BitVector& bv1)
{
  assert(bv0.size() == bv1.size());

  uint64_t size  = bv0.size();
  BitVector zero = BitVector::mk_zero(size);
  uint64_t a0 = size >= 64 ? bv0.bvextract(63, 0).to_uint64() : bv0.to_uint64();
  uint64_t a1 = size >= 64 ? bv1.bvextract(63, 0).to_uint64() : bv1.to_uint64();

  std::vector<std::pair<BitVector, BitVector>> bv_args = {
      std::make_pair(zero, bv1),
      std::make_pair(bv0, zero),
      std::make_pair(bv0, bv1)};
  std::vector<std::pair<uint64_t, uint64_t>> int_args = {
      std::make_pair(0, a1), std::make_pair(a0, 0), std::make_pair(a0, a1)};

  for (size_t i = 0; i < 3; ++i)
  {
    const BitVector& b1 = bv_args[i].first;
    const BitVector& b2 = bv_args[i].second;
    uint64_t i1         = int_args[i].first;
    uint64_t i2         = int_args[i].second;
    std::vector<BitVector> reses{BitVector(b1)};
    if (fun_kind == DEFAULT || fun_kind == INPLACE)
    {
      reses.push_back(BitVector());
      reses.emplace_back(64);
      reses.emplace_back(65);
    }
    BitVector tres;
    uint64_t ares = 0, atres = 0;

    for (auto& res : reses)
    {
      switch (kind)
      {
        case ADD:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvadd(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvadd(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvadd(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvadd(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvadd(tres, tres);
          }
          else
          {
            res = b1.bvadd(b2);
          }
          ares  = _add(i1, i2, size);
          atres = _add(i1, i1, size);
          break;

        case AND:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvand(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvand(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvand(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvand(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvand(tres, tres);
          }
          else
          {
            res = b1.bvand(b2);
          }
          ares  = _and(i1, i2, size);
          atres = _and(i1, i1, size);
          break;

        case ASHR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvashr(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvashr(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvashr(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvashr(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvashr(tres, tres);
          }
          else
          {
            res = b1.bvashr(b2);
          }
          ares  = _ashr(i1, i2, size);
          atres = _ashr(i1, i1, size);
          break;

        case EQ:
          if (fun_kind == INPLACE)
          {
            (void) res.ibveq(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibveq(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibveq(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibveq(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibveq(tres, tres);
          }
          else
          {
            res = b1.bveq(b2);
          }
          ares  = _eq(i1, i2, size);
          atres = _eq(i1, i1, size);
          break;

        case IMPLIES:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvimplies(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvimplies(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvimplies(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvimplies(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvimplies(tres, tres);
          }
          else
          {
            res = b1.bvimplies(b2);
          }
          ares  = _implies(i1, i2, size);
          atres = _implies(i1, i1, size);
          break;

        case MUL:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvmul(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvmul(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvmul(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvmul(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvmul(tres, tres);
          }
          else
          {
            res = b1.bvmul(b2);
          }
          ares  = _mul(i1, i2, size);
          atres = _mul(i1, i1, size);
          break;

        case NAND:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvnand(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvnand(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvnand(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvnand(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvnand(tres, tres);
          }
          else
          {
            res = b1.bvnand(b2);
          }
          ares  = _nand(i1, i2, size);
          atres = _nand(i1, i1, size);
          break;

        case NE:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvne(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvne(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvne(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvne(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvne(tres, tres);
          }
          else
          {
            res = b1.bvne(b2);
          }
          ares  = _ne(i1, i2, size);
          atres = _ne(i1, i1, size);
          break;

        case NOR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvnor(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvnor(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvnor(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvnor(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvnor(tres, tres);
          }
          else
          {
            res = b1.bvnor(b2);
          }
          ares  = _nor(i1, i2, size);
          atres = _nor(i1, i1, size);
          break;

        case OR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvor(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvor(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvor(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvor(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvor(tres, tres);
          }
          else
          {
            res = b1.bvor(b2);
          }
          ares  = _or(i1, i2, size);
          atres = _or(i1, i1, size);
          break;

        case SHL:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvshl(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvshl(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvshl(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvshl(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvshl(tres, tres);
          }
          else
          {
            res = b1.bvshl(b2);
          }
          ares  = _shl(i1, i2, size);
          atres = _shl(i1, i1, size);
          break;

        case SHR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvshr(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvshr(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvshr(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvshr(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvshr(tres, tres);
          }
          else
          {
            res = b1.bvshr(b2);
          }
          ares  = _shr(i1, i2, size);
          atres = _shr(i1, i1, size);
          break;

        case SUB:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvsub(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvsub(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsub(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvsub(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsub(tres, tres);
          }
          else
          {
            res = b1.bvsub(b2);
          }
          ares  = _sub(i1, i2, size);
          atres = _sub(i1, i1, size);
          break;

        case UADDO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvuaddo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvuaddo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvuaddo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvuaddo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvuaddo(tres, tres);
          }
          else
          {
            res = b1.bvuaddo(b2);
          }
          ares  = _uaddo(i1, i2, size);
          atres = _uaddo(i1, i1, size);
          break;

        case UMULO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvumulo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvumulo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvumulo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvumulo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvumulo(tres, tres);
          }
          else
          {
            res = b1.bvumulo(b2);
          }
          ares  = _umulo(i1, i2, size);
          atres = _umulo(i1, i1, size);
          break;

        case USUBO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvusubo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvusubo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvusubo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvusubo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvusubo(tres, tres);
          }
          else
          {
            res = b1.bvusubo(b2);
          }
          ares  = _usubo(i1, i2, size);
          atres = _usubo(i1, i1, size);
          break;

        case UDIV:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvudiv(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvudiv(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvudiv(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvudiv(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvudiv(tres, tres);
          }
          else
          {
            res = b1.bvudiv(b2);
          }
          ares  = _udiv(i1, i2, size);
          atres = _udiv(i1, i1, size);
          break;

        case ULT:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvult(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvult(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvult(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvult(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvult(tres, tres);
          }
          else
          {
            res = b1.bvult(b2);
          }
          ares  = _ult(i1, i2, size);
          atres = _ult(i1, i1, size);
          break;

        case ULE:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvule(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvule(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvule(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvule(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvule(tres, tres);
          }
          else
          {
            res = b1.bvule(b2);
          }
          ares  = _ule(i1, i2, size);
          atres = _ule(i1, i1, size);
          break;

        case UGT:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvugt(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvugt(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvugt(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvugt(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvugt(tres, tres);
          }
          else
          {
            res = b1.bvugt(b2);
          }
          ares  = _ugt(i1, i2, size);
          atres = _ugt(i1, i1, size);
          break;

        case UGE:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvuge(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvuge(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvuge(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvuge(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvuge(tres, tres);
          }
          else
          {
            res = b1.bvuge(b2);
          }
          ares  = _uge(i1, i2, size);
          atres = _uge(i1, i1, size);
          break;

        case UREM:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvurem(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvurem(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvurem(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvurem(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvurem(tres, tres);
          }
          else
          {
            res = b1.bvurem(b2);
          }
          ares  = _urem(i1, i2, size);
          atres = _urem(i1, i1, size);
          break;

        case XOR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvxor(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvxor(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvxor(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvxor(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvxor(tres, tres);
          }
          else
          {
            res = b1.bvxor(b2);
          }
          ares  = _xor(i1, i2, size);
          atres = _xor(i1, i1, size);
          break;

        case XNOR:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvxnor(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvxnor(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvxnor(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvxnor(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvxnor(tres, tres);
          }
          else
          {
            res = b1.bvxnor(b2);
          }
          ares  = _xnor(i1, i2, size);
          atres = _xnor(i1, i1, size);
          break;

        default: assert(false);
      }
      if (res.size() > 64)
      {
        ASSERT_EQ(BitVector::from_ui(64, ares).compare(res.ibvextract(63, 0)),
                  0);
        ASSERT_TRUE(
            tres.is_null()
            || BitVector::from_ui(64, atres).compare(tres.ibvextract(63, 0))
                   == 0);
      }
      else if (b1.size() <= 64)
      {
        ASSERT_EQ(BitVector::from_ui(res.size(), ares).compare(res), 0);
        ASSERT_TRUE(tres.is_null()
                    || BitVector::from_ui(tres.size(), atres).compare(tres)
                           == 0);
      }
      if (kind == Kind::UADDO)
      {
        BitVector b1ext = b1.bvzext(1);
        BitVector b2ext = b2.bvzext(1);
        ASSERT_EQ(b1ext.ibvadd(b2ext).ibvextract(size, size).is_zero(),
                  res.is_zero());
      }
      if (kind == Kind::USUBO)
      {
        BitVector b1ext = b1.bvzext(1);
        BitVector b2ext = b2.bvzext(1);
        ASSERT_EQ(b1ext.ibvsub(b2ext).ibvextract(size, size).is_zero(),
                  res.is_zero());
      }
      else if (kind == Kind::UMULO)
      {
        BitVector b1ext = b1.bvzext(size);
        BitVector b2ext = b2.bvzext(size);
        ASSERT_EQ(b1ext.ibvmul(b2ext).ibvextract(2 * size - 1, size).is_zero(),
                  res.is_zero());
      }
    }
  }
}

void
TestBitVector::test_binary(BvFunKind fun_kind, TestBitVector::Kind kind)
{
  /* test all values for bit-widths 1 - 4 */
  for (uint64_t size = 1; size <= 4; ++size)
  {
    for (uint64_t i = 0, n = 1 << size; i < n; ++i)
    {
      for (uint64_t j = 0, m = 1 << size; j < m; ++j)
      {
        test_binary_aux(fun_kind,
                        kind,
                        BitVector::from_ui(size, i),
                        BitVector::from_ui(size, j));
      }
    }
    if (kind == IMPLIES) return;
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 31, 64, 65, 127})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      if (size > 64)
      {
        /* We only randomize bits 63 to 0 in order to be able to compare against
         * the corresponding implementation with uint64. */
        test_binary_aux(fun_kind,
                        kind,
                        BitVector(size, *d_rng, 63, 0),
                        BitVector(size, *d_rng, 63, 0));
      }
      else
      {
        test_binary_aux(
            fun_kind, kind, BitVector(size, *d_rng), BitVector(size, *d_rng));
      }
    }
  }
  /* death tests */
  BitVector b1(33, *d_rng);
  BitVector b2(34, *d_rng);
  switch (kind)
  {
    case ADD:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvadd(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvadd(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvadd(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvadd(b2), "d_size == .*d_size");
      }
      break;

    case AND:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvand(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvand(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvand(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvand(b2), "d_size == .*d_size");
      }
      break;

    case ASHR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvashr(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvashr(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvashr(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvashr(b2), "d_size == .*d_size");
      }
      break;

    case EQ:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibveq(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibveq(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibveq(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bveq(b2), "d_size == .*d_size");
      }
      break;

    case IMPLIES:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(BitVector(1).ibvimplies(b2), "b1.d_size == 1");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvimplies(b1, b2), "b1.d_size == 1");
        ASSERT_DEATH_DEBUG(b1.ibvimplies(b2, b1), "bv0.d_size == 1");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvimplies(b2), "d_size == .*d_size");
      }
      break;

    case MUL:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvmul(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvmul(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvmul(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvmul(b2), "d_size == .*d_size");
      }
      break;

    case NAND:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvnand(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvnand(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvnand(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvnand(b2), "d_size == .*d_size");
      }
      break;

    case NE:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvne(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvne(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvne(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvne(b2), "d_size == .*d_size");
      }
      break;

    case NOR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvnor(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvnor(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvnor(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvnor(b2), "d_size == .*d_size");
      }
      break;

    case OR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvor(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvor(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvor(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvor(b2), "d_size == .*d_size");
      }
      break;

    case SHL:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvshl(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvshl(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvshl(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvshl(b2), "d_size == .*d_size");
      }
      break;

    case SHR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvshr(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvshr(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvshr(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvshr(b2), "d_size == .*d_size");
      }
      break;

    case SUB:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsub(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsub(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsub(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsub(b2), "d_size == .*d_size");
      }
      break;

    case UADDO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvuaddo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvuaddo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvuaddo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvuaddo(b2), "d_size == .*d_size");
      }
      break;

    case UMULO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvumulo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvumulo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvumulo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvumulo(b2), "d_size == .*d_size");
      }
      break;

    case USUBO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvusubo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvusubo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvusubo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvusubo(b2), "d_size == .*d_size");
      }
      break;

    case UDIV:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvudiv(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvudiv(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvudiv(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvudiv(b2), "d_size == .*d_size");
      }
      break;

    case ULT:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvult(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvult(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvult(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvult(b2), "d_size == .*d_size");
      }
      break;

    case ULE:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvule(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvule(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvule(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvule(b2), "d_size == .*d_size");
      }
      break;

    case UGT:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvugt(b1, b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvugt(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvugt(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvugt(b2), "d_size == .*d_size");
      }
      break;

    case UGE:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvuge(b1, b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvuge(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvuge(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvuge(b2), "d_size == .*d_size");
      }
      break;

    case UREM:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvurem(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvurem(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvurem(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvurem(b2), "d_size == .*d_size");
      }
      break;

    case XOR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvxor(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvxor(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvxor(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvxor(b2), "d_size == .*d_size");
      }
      break;

    case XNOR:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvxnor(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvxnor(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvxnor(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvxnor(b2), "d_size == .*d_size");
      }
      break;

    default: assert(false);
  }
}

void
TestBitVector::test_binary_signed_aux(BvFunKind fun_kind,
                                      Kind kind,
                                      const BitVector& bv0,
                                      const BitVector& bv1)
{
  assert(bv0.size() == bv1.size());

  uint64_t size  = bv0.size();
  BitVector zero = BitVector::mk_zero(size);
  BitVector b1(bv0);
  BitVector b2(bv1);
  /* we only test values representable in 64 bits */
  int64_t a1 = static_cast<int64_t>(size > 64 ? b1.bvextract(63, 0).to_uint64()
                                              : b1.to_uint64());
  int64_t a2 = static_cast<int64_t>(size > 64 ? b2.bvextract(63, 0).to_uint64()
                                              : b2.to_uint64());
  if (b1.bit(size - 1))
  {
    a1 = static_cast<int64_t>((UINT64_MAX << size) | static_cast<uint64_t>(a1));
  }
  if (b2.bit(size - 1))
  {
    a2 = static_cast<int64_t>((UINT64_MAX << size) | static_cast<uint64_t>(a2));
  }
  std::vector<std::pair<BitVector, BitVector>> bv_args = {
      std::make_pair(zero, b2),
      std::make_pair(b1, zero),
      std::make_pair(b1, b2)};
  std::vector<std::pair<int64_t, int64_t>> int_args = {
      std::make_pair(0, a2), std::make_pair(a1, 0), std::make_pair(a1, a2)};

  for (size_t i = 0; i < 3; ++i)
  {
    const BitVector& b1 = bv_args[i].first;
    const BitVector& b2 = bv_args[i].second;
    int64_t i1          = int_args[i].first;
    int64_t i2          = int_args[i].second;
    std::vector<BitVector> reses{BitVector(b1)};
    if (fun_kind != INPLACE_THIS)
    {
      reses.push_back(BitVector());
      reses.emplace_back(64);
      reses.emplace_back(65);
    }
    BitVector tres;
    int64_t ares = 0, atres = 0;

    for (auto& res : reses)
    {
      switch (kind)
      {
        case SADDO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvsaddo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvsaddo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsaddo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvsaddo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsaddo(tres, tres);
          }
          else
          {
            res = b1.bvsaddo(b2);
          }
          ares  = _saddo(i1, i2, size);
          atres = _saddo(i1, i1, size);
          break;

        case SSUBO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvssubo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvssubo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvssubo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvssubo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvssubo(tres, tres);
          }
          else
          {
            res = b1.bvssubo(b2);
          }
          ares  = _ssubo(i1, i2, size);
          atres = _ssubo(i1, i1, size);
          break;

        case SMULO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvsmulo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvsmulo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsmulo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvsmulo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsmulo(tres, tres);
          }
          else
          {
            res = b1.bvsmulo(b2);
          }
          ares  = _smulo(i1, i2, size);
          atres = _smulo(i1, i1, size);
          break;

        case SDIVO:
          if (fun_kind == INPLACE)
          {
            (void) res.ibvsdivo(b1, b2);
          }
          else if (fun_kind == INPLACE_THIS)
          {
            // test with *this as first argument
            (void) res.ibvsdivo(b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsdivo(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            // test with *this as first argument
            (void) res.ibvsdivo(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsdivo(tres, tres);
          }
          else
          {
            res = b1.bvsdivo(b2);
          }
          ares  = _sdivo(i1, i2, size);
          atres = _sdivo(i1, i1, size);
          break;

        case SDIV:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsdiv(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsdiv(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsdiv(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsdiv(tres, tres);
          }
          else
          {
            res = b1.bvsdiv(b2);
          }
          ares  = _sdiv(i1, i2, size);
          atres = _sdiv(i1, i1, size);
          break;

        case SLT:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvslt(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvslt(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvslt(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvslt(tres, tres);
          }
          else
          {
            res = b1.bvslt(b2);
          }
          ares  = _slt(i1, i2, size);
          atres = _slt(i1, i1, size);
          break;

        case SLE:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsle(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsle(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsle(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsle(tres, tres);
          }
          else
          {
            res = b1.bvsle(b2);
          }
          ares  = _sle(i1, i2, size);
          atres = _sle(i1, i1, size);
          break;

        case SGT:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsgt(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsgt(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsgt(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsgt(tres, tres);
          }
          else
          {
            res = b1.bvsgt(b2);
          }
          ares  = _sgt(i1, i2, size);
          atres = _sgt(i1, i1, size);
          break;

        case SGE:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsge(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsge(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsge(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsge(tres, tres);
          }
          else
          {
            res = b1.bvsge(b2);
          }
          ares  = _sge(i1, i2, size);
          atres = _sge(i1, i1, size);
          break;

        case SREM:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsrem(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsrem(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsrem(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsrem(tres, tres);
          }
          else
          {
            res = b1.bvsrem(b2);
          }
          ares  = _srem(i1, i2, size);
          atres = _srem(i1, i1, size);
          break;

        case SMOD:
          if (fun_kind == INPLACE_THIS)
          {
            (void) res.ibvsmod(b2);
            // test with *this as argument
            tres = b1;
            (void) tres.ibvsmod(tres);
          }
          else if (fun_kind == INPLACE_THIS_ALL)
          {
            (void) res.ibvsmod(b1, b2);
            // test with *this as arguments
            tres = b1;
            (void) tres.ibvsmod(tres, tres);
          }
          else
          {
            res = b1.bvsmod(b2);
          }
          ares  = _smod(i1, i2, size);
          atres = _smod(i1, i1, size);
          break;

        default: assert(false);
      }
      ASSERT_EQ(BitVector::from_si(res.size(), ares).compare(res), 0);
      ASSERT_TRUE(tres.is_null()
                  || BitVector::from_si(tres.size(), atres).compare(tres) == 0);
    }
  }
}

void
TestBitVector::test_binary_signed(BvFunKind fun_kind, Kind kind)
{
  /* test all values for bit-widths 1 - 4 */
  for (uint64_t size = 1; size <= 4; ++size)
  {
    for (uint64_t i = 0, n = 1 << size; i < n; ++i)
    {
      for (uint64_t j = 0, m = 1 << size; j < m; ++j)
      {
        test_binary_signed_aux(fun_kind,
                               kind,
                               BitVector::from_ui(size, i),
                               BitVector::from_ui(size, j));
      }
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 32, 35})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      test_binary_signed_aux(
          fun_kind, kind, BitVector(size, *d_rng), BitVector(size, *d_rng));
    }
  }
  /* death tests */
  BitVector b1(33, *d_rng);
  BitVector b2(34, *d_rng);
  switch (kind)
  {
    case SADDO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsaddo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsaddo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsaddo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsaddo(b2), "d_size == .*d_size");
      }
      break;

    case SSUBO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvssubo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvssubo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvssubo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvssubo(b2), "d_size == .*d_size");
      }
      break;

    case SMULO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsmulo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsmulo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsmulo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsmulo(b2), "d_size == .*d_size");
      }
      break;

    case SDIVO:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsdivo(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsdivo(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsdivo(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsdivo(b2), "d_size == .*d_size");
      }
      break;

    case SDIV:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsdiv(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsdiv(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsdiv(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsdiv(b2), "d_size == .*d_size");
      }
      break;

    case SLT:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvslt(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvslt(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvslt(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvslt(b2), "d_size == .*d_size");
      }
      break;

    case SLE:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsle(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsle(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsle(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsle(b2), "d_size == .*d_size");
      }
      break;

    case SGT:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsgt(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsgt(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsgt(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsgt(b2), "d_size == .*d_size");
      }
      break;

    case SGE:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsge(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsge(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsge(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsge(b2), "d_size == .*d_size");
      }
      break;

    case SREM:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsrem(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsrem(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsrem(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsrem(b2), "d_size == .*d_size");
      }
      break;

    case SMOD:
      if (fun_kind == INPLACE_THIS)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsmod(b2), "d_size == .*d_size");
      }
      else if (fun_kind == INPLACE_THIS_ALL)
      {
        ASSERT_DEATH_DEBUG(b1.ibvsmod(b1, b2), "d_size == .*d_size");
        ASSERT_DEATH_DEBUG(b1.ibvsmod(b2, b1), "d_size == .*d_size");
      }
      else
      {
        ASSERT_DEATH_DEBUG(b1.bvsmod(b2), "d_size == .*d_size");
      }
      break;

    default: assert(false);
  }
}

void
TestBitVector::test_concat_aux(BvFunKind fun_kind,
                               const BitVector& bv0,
                               const BitVector& bv1)
{
  uint64_t size0 = bv0.size();
  uint64_t size1 = bv1.size();
  uint64_t size  = size0 + size1;
  BitVector bv(size / 2, *d_rng), cbv0(bv0), cbv1(bv1);
  std::vector<BitVector> reses{BitVector(bv0)};
  if (fun_kind != INPLACE_THIS)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }
  BitVector tres, tbv0(bv), tbv1(bv);

  for (auto& res : reses)
  {
    if (fun_kind == INPLACE_THIS)
    {
      (void) res.ibvconcat(bv1);
      // test with *this as argument
      tres = bv;
      (void) tres.ibvconcat(tres);
    }
    else if (fun_kind == INPLACE_THIS_ALL)
    {
      (void) res.ibvconcat(bv0, bv1);
      // test with *this as arguments
      tres = bv;
      (void) tres.ibvconcat(tres, tres);
    }
    else
    {
      res = bv0.bvconcat(bv1);
    }
    ASSERT_EQ(res.size(), size0 + size1);
    /* we only test values representable in 64 bits */
    ASSERT_EQ(res.bvextract(res.size() - 1, cbv1.size()).compare(bv0), 0);
    ASSERT_EQ(res.bvextract(cbv1.size() - 1, 0).compare(cbv1), 0);
    ASSERT_TRUE(tres.is_null()
                || tres.bvextract(tres.size() - 1, tbv1.size()).compare(tbv0)
                       == 0);
    ASSERT_TRUE(tres.is_null()
                || tres.bvextract(tbv1.size() - 1, 0).compare(tbv1) == 0);
  }
}

void
TestBitVector::test_concat(BvFunKind fun_kind)
{
  /* test all values for bit-widths 2 - 8 */
  for (uint64_t size = 2; size <= 8; ++size)
  {
    uint64_t size0 = d_rng->pick<uint64_t>(1, size - 1);
    uint64_t size1 = size - size0;
    for (uint64_t i = 0, n = 1 << size0; i < n; ++i)
    {
      for (uint64_t j = 0, m = 1 << size1; j < m; ++j)
      {
        test_concat_aux(
            fun_kind, BitVector::from_ui(size, i), BitVector::from_ui(size, j));
      }
    }
  }
  // test random values for various bit-widths
  std::vector<std::pair<uint64_t, uint64_t>> sizes = {
      {7, 16}, {17, 32}, {33, 64}, {33, 127}};
  for (const auto& [min, max] : sizes)
  {
    uint64_t ntests = std::min(1u << max, N_TESTS);
    uint64_t size0  = d_rng->pick<uint64_t>(min, max - 1);
    uint64_t size1  = max - size0;
    for (uint32_t i = 0; i < ntests; ++i)
    {
      if (size1 > 64)
      {
        test_concat_aux(fun_kind,
                        size0 > 64 ? BitVector(size0, *d_rng, 63, 0)
                                   : BitVector(size0, *d_rng),
                        size1 > 64 ? BitVector(size1, *d_rng, 63, 0)
                                   : BitVector(size1, *d_rng));
      }
      else
      {
        test_concat_aux(
            fun_kind, BitVector(size0, *d_rng), BitVector(size1, *d_rng));
      }
    }
  }
}

void
TestBitVector::test_extract_aux(BvFunKind fun_kind, const BitVector& bv)
{
  uint64_t size = bv.size();

  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind == DEFAULT || fun_kind == INPLACE)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }
  uint64_t lo = d_rng->pick<uint64_t>(0, size - 1);
  uint64_t hi = d_rng->pick<uint64_t>(lo, size - 1);
  ASSERT_GE(hi, lo);
  ASSERT_LT(hi, size);
  ASSERT_LT(lo, size);

  for (auto& res : reses)
  {
    if (fun_kind == INPLACE)
    {
      (void) res.ibvextract(bv, hi, lo);
    }
    else if (fun_kind == INPLACE_THIS)
    {
      (void) res.ibvextract(hi, lo);
    }
    else if (fun_kind == INPLACE_THIS_ALL)
    {
      // test with *this as argument
      (void) res.ibvextract(res, hi, lo);
    }
    else
    {
      res = bv.bvextract(hi, lo);
    }
    ASSERT_EQ(res.size(), hi - lo + 1);
    std::string res_str = res.str();
    std::string bv_str  = bv.str();
    uint64_t len        = hi - lo + 1;
    ASSERT_EQ(bv_str.compare(size - hi - 1, len, res_str, 0, len), 0);
  }
}

void
TestBitVector::test_extract(BvFunKind fun_kind)
{
  /* test all values for bit-widths 1 - 8 */
  for (uint64_t size = 1; size <= 8; ++size)
  {
    for (uint64_t i = 0, n = 1 << size; i < n; ++i)
    {
      test_extract_aux(fun_kind, BitVector::from_ui(size, i));
    }
  }
  // test random values for various bit-widths
  for (uint64_t size : {16, 32, 35})
  {
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      test_extract_aux(fun_kind, BitVector::from_ui(size, i));
    }
  }
  ASSERT_DEATH_DEBUG(BitVector(33, *d_rng).bvextract(31, 32),
                     "idx_hi >= idx_lo");
}

void
TestBitVector::test_shift_aux(BvFunKind fun_kind,
                              Kind kind,
                              const std::string& to_shift,
                              const std::string& shift,
                              const std::string& expected,
                              bool shift_by_int)
{
  uint64_t size = to_shift.size();
  assert(size == shift.size());
  assert(size == expected.size());
  (void) size;

  BitVector bv(to_shift.size(), to_shift);
  BitVector bv_shift(shift.size(), shift);
  BitVector bv_expected(expected.size(), expected);
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind != INPLACE_THIS)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }
  uint64_t int_shift = strtoul(shift.c_str(), nullptr, 2);

  for (auto& res : reses)
  {
    switch (kind)
    {
      case ASHR:
        if (fun_kind == INPLACE_THIS)
        {
          if (shift_by_int)
          {
            (void) res.ibvashr(int_shift);
          }
          else
          {
            (void) res.ibvashr(bv_shift);
          }
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          if (shift_by_int)
          {
            (void) res.ibvashr(bv, int_shift);
          }
          else
          {
            (void) res.ibvashr(bv, bv_shift);
          }
        }
        else
        {
          if (shift_by_int)
          {
            res = bv.bvashr(int_shift);
          }
          else
          {
            res = bv.bvashr(bv_shift);
          }
        }
        break;
      case SHL:
        if (fun_kind == INPLACE_THIS)
        {
          if (shift_by_int)
          {
            (void) res.ibvshl(int_shift);
          }
          else
          {
            (void) res.ibvshl(bv_shift);
          }
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          if (shift_by_int)
          {
            (void) res.ibvshl(bv, int_shift);
          }
          else
          {
            (void) res.ibvshl(bv, bv_shift);
          }
        }
        else
        {
          if (shift_by_int)
          {
            res = bv.bvshl(int_shift);
          }
          else
          {
            res = bv.bvshl(bv_shift);
          }
        }
        break;
      case SHR:
        if (fun_kind == INPLACE_THIS)
        {
          if (shift_by_int)
          {
            (void) res.ibvshr(int_shift);
          }
          else
          {
            (void) res.ibvshr(bv_shift);
          }
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          if (shift_by_int)
          {
            (void) res.ibvshr(bv, int_shift);
          }
          else
          {
            (void) res.ibvshr(bv, bv_shift);
          }
        }
        else
        {
          if (shift_by_int)
          {
            res = bv.bvshr(int_shift);
          }
          else
          {
            res = bv.bvshr(bv_shift);
          }
        }
        break;
      default: assert(false);
    }

    ASSERT_EQ(res.compare(bv_expected), 0);
  }
}

void
TestBitVector::test_shift(BvFunKind fun_kind, Kind kind, bool shift_by_int)
{
  for (uint64_t size : {2, 3, 8})
  {
    for (uint64_t i = 0; i < (1u << size); ++i)
    {
      for (uint64_t j = 0; j < (1u << size); ++j)
      {
        std::string expected;
        if (kind == SHL)
        {
          expected = to_bin_string(size, i) + std::string(j, '0');
        }
        else if (kind == SHR)
        {
          expected = std::string(j, '0') + to_bin_string(size, i);
        }
        else
        {
          assert(kind == ASHR);
          std::string bits_i = to_bin_string(size, i);
          expected = std::string(j, bits_i[0] == '1' ? '1' : '0') + bits_i;
        }
        if (kind == SHL)
        {
          expected = expected.substr(expected.size() - size, size);
        }
        else
        {
          expected = expected.substr(0, size);
        }
        test_shift_aux(fun_kind,
                       kind,
                       to_bin_string(size, i),
                       to_bin_string(size, j),
                       expected,
                       shift_by_int);
      }
    }
  }
  for (uint64_t size : {65, 128})
  {
    for (uint64_t i = 0; i < N_TESTS; ++i)
    {
      uint64_t n           = d_rng->pick<uint64_t>();
      uint64_t m           = d_rng->pick<uint64_t>();
      std::string to_shift = to_bin_string(size - 64, m) + to_bin_string(64, n);
      uint64_t s           = d_rng->pick<uint64_t>(0, size + 2);
      std::string shift    = to_bin_string(size, s);
      std::string expected;
      if (kind == SHL)
      {
        expected = to_shift + std::string(s, '0');
      }
      else if (kind == SHR)
      {
        expected = std::string(s, '0') + to_shift;
      }
      else
      {
        assert(kind == ASHR);
        expected = std::string(s, to_shift[0] == '1' ? '1' : '0') + to_shift;
      }
      if (kind == SHL)
      {
        expected = expected.substr(expected.size() - size, size);
      }
      else
      {
        expected = expected.substr(0, size);
      }
      test_shift_aux(fun_kind, kind, to_shift, shift, expected, shift_by_int);

      /* shift value doesn't fit into uint64_t */
      if (size > 64)
      {
        std::string shift = to_bin_string(size, d_rng->pick<uint64_t>());
        shift[0]          = '1';
        test_shift_aux(fun_kind,
                       kind,
                       to_bin_string(size, n),
                       shift,
                       std::string(size, '0'),
                       shift_by_int);
      }
    }
  }
}

void
TestBitVector::test_rotate_aux(BvFunKind fun_kind,
                               Kind kind,
                               const BitVector& bv,
                               uint64_t n)
{
  uint64_t size = bv.size();
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind == DEFAULT || fun_kind == INPLACE)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }

  for (auto& res : reses)
  {
    switch (kind)
    {
      case ROLI:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvroli(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvroli(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvroli(res, n);
        }
        else
        {
          res = bv.bvroli(n);
        }
        break;
      case ROL:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvrol(bv, BitVector::from_ui(size, n));
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvrol(BitVector::from_ui(size, n));
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvrol(res, BitVector::from_ui(size, n));
        }
        else
        {
          res = bv.bvrol(BitVector::from_ui(size, n));
        }
        break;
      case RORI:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvrori(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvrori(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvrori(res, n);
        }
        else
        {
          res = bv.bvrori(n);
        }
        break;
      case ROR:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvror(bv, BitVector::from_ui(size, n));
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvror(BitVector::from_ui(size, n));
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvror(res, BitVector::from_ui(size, n));
        }
        else
        {
          res = bv.bvror(BitVector::from_ui(size, n));
        }
        break;

      default: assert(false);
    }
    ASSERT_EQ(size, res.size());
    std::string res_str = res.str();
    uint64_t rot        = n % size;
    std::stringstream exp_str;
    if (rot)
    {
      if (kind == ROLI || kind == ROL)
      {
        exp_str << bv.bvextract(size - 1 - rot, 0)
                << bv.bvextract(size - 1, size - rot);
      }
      else if (kind == RORI || kind == ROR)
      {
        exp_str << bv.bvextract(rot - 1, 0) << bv.bvextract(size - 1, rot);
      }
    }
    else
    {
      exp_str << bv;
    }
    ASSERT_EQ(res_str, exp_str.str());
  }
}

void
TestBitVector::test_rotate_aux(BvFunKind fun_kind,
                               Kind kind,
                               const BitVector& bv,
                               const BitVector& n)
{
  uint64_t size = bv.size();
  std::vector<BitVector> reses{BitVector(bv)};
  if (fun_kind == DEFAULT || fun_kind == INPLACE)
  {
    reses.push_back(BitVector());
    reses.emplace_back(64);
    reses.emplace_back(65);
  }

  for (auto& res : reses)
  {
    switch (kind)
    {
      case ROL:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvrol(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvrol(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvrol(res, n);
        }
        else
        {
          res = bv.bvrol(n);
        }
        break;
      case ROR:
        if (fun_kind == INPLACE)
        {
          (void) res.ibvror(bv, n);
        }
        else if (fun_kind == INPLACE_THIS)
        {
          (void) res.ibvror(n);
        }
        else if (fun_kind == INPLACE_THIS_ALL)
        {
          // test with *this as argument
          (void) res.ibvror(res, n);
        }
        else
        {
          res = bv.bvror(n);
        }
        break;

      default: assert(false);
    }
    ASSERT_EQ(size, res.size());
    std::string res_str = res.str();
    std::string str     = n.bvurem(BitVector::from_ui(size, size)).str();
    str.erase(0, str.find_first_not_of('0'));
    uint64_t rot = str.empty() ? 0 : std::stoul(str, nullptr, 2);
    std::stringstream exp_str;
    if (rot)
    {
      if (kind == ROLI || kind == ROL)
      {
        exp_str << bv.bvextract(size - 1 - rot, 0)
                << bv.bvextract(size - 1, size - rot);
      }
      else if (kind == RORI || kind == ROR)
      {
        exp_str << bv.bvextract(rot - 1, 0) << bv.bvextract(size - 1, rot);
      }
    }
    else
    {
      exp_str << bv;
    }
    ASSERT_EQ(res_str, exp_str.str());
  }
}

void
TestBitVector::test_rotate(BvFunKind fun_kind, Kind kind)
{
  for (uint64_t size : {2, 3, 8})
  {
    for (uint64_t i = 0; i < (1u << size); ++i)
    {
      uint64_t n = kind == ROLI || kind == RORI
                       ? d_rng->pick<uint64_t>(0, (1u << size) + size + 1)
                       : d_rng->pick<uint64_t>(0, (1u << size) - 1);
      test_rotate_aux(fun_kind, kind, BitVector::from_ui(size, i), n);
    }
  }
  if (kind == ROL || kind == ROR)
  {
    for (uint64_t size : {65, 128})
    {
      // 'n' does not fit into uint64_t
      for (uint32_t i = 0; i < N_TESTS; ++i)
      {
        BitVector n(size,
                    *d_rng,
                    BitVector::from_ui(size, UINT64_MAX),
                    BitVector::mk_ones(size));
        test_rotate_aux(fun_kind, kind, BitVector::from_ui(size, i), n);
      }
    }
  }
}

void
TestBitVector::test_udivurem(uint64_t size)
{
  BitVector zero = BitVector::mk_zero(size);
  for (uint32_t i = 0; i < N_TESTS; ++i)
  {
    BitVector q, r, tq, tr;
    BitVector bv1(size, *d_rng, 63, 0);
    BitVector bv2(size, *d_rng, 63, 0);
    /* we only test values representable in 64 bits */
    uint64_t a1 =
        size > 64 ? bv1.bvextract(63, 0).to_uint64() : bv1.to_uint64();
    uint64_t a2 =
        size > 64 ? bv2.bvextract(63, 0).to_uint64() : bv2.to_uint64();
    uint64_t ares_div, ares_rem, bres_div, bres_rem;

    /* test for x = 0 explicitly */
    ares_div = _udiv(0, a2, size);
    ares_rem = _urem(0, a2, size);
    // no *this arguments
    zero.bvudivurem(bv2, &q, &r);
    bres_div = size > 64 ? q.bvextract(63, 0).to_uint64() : q.to_uint64();
    bres_rem = size > 64 ? r.bvextract(63, 0).to_uint64() : r.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test with *this as argument
    tq = zero;
    tr = BitVector();
    tq.bvudivurem(bv2, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    tq = BitVector();
    tr = zero;
    tr.bvudivurem(bv2, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test second argument == remainder argument
    tq = BitVector();
    tr = bv2;
    zero.bvudivurem(tr, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);

    /* test for y = 0 explicitly */
    ares_div = _udiv(a1, 0, size);
    ares_rem = _urem(a1, 0, size);
    // no *this arguments
    bv1.bvudivurem(zero, &q, &r);
    bres_div = size > 64 ? q.bvextract(63, 0).to_uint64() : q.to_uint64();
    bres_rem = size > 64 ? r.bvextract(63, 0).to_uint64() : r.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test with *this as argument
    tq = bv1;
    tr = BitVector();
    tq.bvudivurem(zero, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    tq = BitVector();
    tr = bv1;
    tr.bvudivurem(zero, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test second argument == remainder argument
    tq = BitVector();
    tr = zero;
    bv1.bvudivurem(tr, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);

    /* test x, y random */
    ares_div = _udiv(a1, a2, size);
    ares_rem = _urem(a1, a2, size);
    // no *this arguments
    bv1.bvudivurem(bv2, &q, &r);
    bres_div = size >= 64 ? q.bvextract(63, 0).to_uint64() : q.to_uint64();
    bres_rem = size >= 64 ? r.bvextract(63, 0).to_uint64() : r.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test with *this as argument
    tq = bv1;
    tr = BitVector();
    tq.bvudivurem(bv2, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    tq = BitVector();
    tr = bv1;
    tr.bvudivurem(bv2, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
    // test second argument == remainder argument
    tq = BitVector();
    tr = bv2;
    bv1.bvudivurem(tr, &tq, &tr);
    bres_div = size > 64 ? tq.bvextract(63, 0).to_uint64() : tq.to_uint64();
    bres_rem = size > 64 ? tr.bvextract(63, 0).to_uint64() : tr.to_uint64();
    ASSERT_EQ(ares_div, bres_div);
    ASSERT_EQ(ares_rem, bres_rem);
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVector, ctor_dtor)
{
  ASSERT_EQ(BitVector(1).str(), "0");
  ASSERT_EQ(BitVector(10).str(), "0000000000");

  ASSERT_EQ(BitVector(6, "101010").str(), "101010");
  ASSERT_EQ(BitVector(6, "000101010").str(), "101010");
  ASSERT_EQ(BitVector(8, "101010").str(), "00101010");
  ASSERT_EQ(BitVector(8, "128", 10).str(), "10000000");

  ASSERT_EQ(BitVector(8, "-3", 10).str(), "11111101");
  ASSERT_EQ(BitVector(8, "-127", 10).str(), "10000001");
  ASSERT_EQ(BitVector(8, "-128", 10).str(), "10000000");

  ASSERT_EQ(BitVector(8, "a1", 16).str(), "10100001");
  ASSERT_EQ(BitVector(8, "F1", 16).str(), "11110001");

  ASSERT_EQ(BitVector::from_si(8, -3).str(), "11111101");
  ASSERT_EQ(BitVector::from_si(8, -127).str(), "10000001");
  ASSERT_EQ(BitVector::from_si(8, -128).str(), "10000000");

  ASSERT_EQ(
      BitVector::from_si(68, -3).str(),
      "11111111111111111111111111111111111111111111111111111111111111111101");
  ASSERT_EQ(
      BitVector::from_ui(68, static_cast<uint64_t>(-3)).str(),
      "00001111111111111111111111111111111111111111111111111111111111111101");
  ASSERT_EQ(
      BitVector::from_ui(68, 3).str(),
      "00000000000000000000000000000000000000000000000000000000000000000011");

  ASSERT_EQ(BitVector::from_ui(11, 1234).str(), "10011010010");
  ASSERT_EQ(BitVector::from_ui(16, 1234).str(), "0000010011010010");
  ASSERT_EQ(BitVector::from_ui(16, 65535).str(), "1111111111111111");

  ASSERT_EQ(BitVector::from_ui(6, 141, true).str(), "001101");
  ASSERT_EQ(BitVector::from_si(6, -129, true).str(), "111111");

  ASSERT_EQ(BitVector(11, util::Integer(1234).gmp_value()).str(),
            "10011010010");
  ASSERT_EQ(BitVector(16, util::Integer(1234).gmp_value()).str(),
            "0000010011010010");
  ASSERT_EQ(BitVector(16, util::Integer(-1).gmp_value()).str(),
            "1111111111111111");
  ASSERT_EQ(BitVector(8, util::Integer(-3).gmp_value()).str(), "11111101");
  ASSERT_EQ(BitVector(8, util::Integer(-127).gmp_value()).str(), "10000001");
  ASSERT_EQ(BitVector(8, util::Integer(-128).gmp_value()).str(), "10000000");
  ASSERT_EQ(
      BitVector(68, util::Integer(-3).gmp_value()).str(),
      "11111111111111111111111111111111111111111111111111111111111111111101");
  ASSERT_EQ(
      BitVector(68, util::Integer(static_cast<uint64_t>(-3)).gmp_value()).str(),
      "00001111111111111111111111111111111111111111111111111111111111111101");

  ASSERT_DEATH_DEBUG(BitVector(0), "> 0");
  ASSERT_DEATH_DEBUG(BitVector(2, "101010"), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector(6, "a01010"), "is_valid_bin_str");
  ASSERT_DEATH_DEBUG(BitVector(6, "123412"), "is_valid_bin_str");
  ASSERT_DEATH_DEBUG(BitVector(6, "1234", 10), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector(6, "1f", 10), "is_valid_dec_str");
  ASSERT_DEATH_DEBUG(BitVector(8, "-129", 10), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector(6, "1234", 16), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector(6, "1z", 16), "is_valid_hex_str");
  ASSERT_DEATH_DEBUG(BitVector(8, "-12", 16), "is_valid_hex_str");
  ASSERT_DEATH_DEBUG(BitVector(2, ""), "empty");
  ASSERT_DEATH_DEBUG(BitVector::from_ui(0, 1234), "> 0");
  ASSERT_DEATH_DEBUG(BitVector::from_si(8, -129), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector::from_ui(10, 1234), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector::from_ui(16, 123412341234), "fits_in_size");
  ASSERT_DEATH_DEBUG(BitVector::from_ui(16, 65536), "fits_in_size");
}

TEST_F(TestBitVector, ctor_rand)
{
  for (uint64_t size = 1; size <= 127; ++size)
  {
    BitVector bv1, bv2, bv3;
    uint32_t i = 0;
    do
    {
      bv1 = BitVector(size, *d_rng);
      bv2 = BitVector(size, *d_rng);
      bv3 = BitVector(size, *d_rng);
      i += 1;
    } while (i <= 2 && bv1.compare(bv2) == 0 && bv1.compare(bv3) == 0
             && bv2.compare(bv3) == 0);
    ASSERT_TRUE(bv1.compare(bv2) || bv1.compare(bv3) || bv2.compare(bv3));
  }
}

TEST_F(TestBitVector, ctor_random_range)
{
  for (uint64_t size = 1; size <= 65; ++size)
  {
    BitVector from(size, *d_rng);
    // from == to
    BitVector bv1(size, *d_rng, from, from);
    ASSERT_EQ(bv1.compare(from), 0);
    // from < to
    BitVector to(size, *d_rng);
    while (from.compare(to) == 0)
    {
      to = BitVector(size, *d_rng);
    }
    if (to.compare(from) < 0)
    {
      BitVector tmp = to;
      to            = from;
      from          = tmp;
    }

    BitVector bv2(size, *d_rng, from, to);
    ASSERT_GE(bv2.compare(from), 0);
    ASSERT_LE(bv2.compare(to), 0);
  }
}

TEST_F(TestBitVector, ctor_random_signed_range)
{
  for (uint64_t size = 1; size <= 65; size++)
  {
    BitVector from(size, *d_rng);
    // from == to
    BitVector bv1(size, *d_rng, from, from, true);
    ASSERT_EQ(bv1.compare(from), 0);
    // from < to
    BitVector to(size, *d_rng);
    while (from.signed_compare(to) == 0)
    {
      to = BitVector(size, *d_rng);
    }
    if (from.signed_compare(to) >= 0)
    {
      BitVector tmp = to;
      to            = from;
      from          = tmp;
    }
    BitVector bv2(size, *d_rng, from, to, true);
    ASSERT_LE(from.signed_compare(bv2), 0);
    ASSERT_LE(bv2.signed_compare(to), 0);
  }
}

TEST_F(TestBitVector, ctor_random_bit_range)
{
  test_ctor_random_bit_range(1);
  test_ctor_random_bit_range(7);
  test_ctor_random_bit_range(31);
  test_ctor_random_bit_range(33);
}

TEST_F(TestBitVector, str)
{
  ASSERT_EQ(BitVector(1).str(), "0");
  ASSERT_EQ(BitVector(10).str(), "0000000000");
  ASSERT_EQ(BitVector(6, "101010").str(), "101010");
  ASSERT_EQ(BitVector(8, "101010").str(), "00101010");
  ASSERT_EQ(BitVector::from_ui(16, 1234).str(), "0000010011010010");
  ASSERT_EQ(BitVector::from_ui(16, 65530).str(), "1111111111111010");
  ASSERT_EQ(BitVector::from_ui(16, 65535).str(), "1111111111111111");
  ASSERT_EQ(BitVector::from_ui(32, 4294967295).str(),
            "11111111111111111111111111111111");
  ASSERT_EQ(BitVector::from_ui(64, UINT64_MAX).str(),
            "1111111111111111111111111111111111111111111111111111111111111111");
  ASSERT_EQ(
      BitVector::from_ui(65, UINT64_MAX).str(),
      "01111111111111111111111111111111111111111111111111111111111111111");
  ASSERT_EQ(
      BitVector::from_si(68, -3).str(),
      "11111111111111111111111111111111111111111111111111111111111111111101");
  ASSERT_EQ(
      BitVector::from_ui(68, static_cast<uint64_t>(-3)).str(),
      "00001111111111111111111111111111111111111111111111111111111111111101");
  ASSERT_EQ(
      BitVector::from_ui(68, 3).str(),
      "00000000000000000000000000000000000000000000000000000000000000000011");

  ASSERT_EQ(BitVector(10).str(10), "0");
  ASSERT_EQ(BitVector(6, "101010").str(10), "42");
  ASSERT_EQ(BitVector(8, "101010").str(10), "42");
  ASSERT_EQ(BitVector::from_ui(16, 1234).str(10), "1234");
  ASSERT_EQ(BitVector::from_ui(16, 65530).str(10), "65530");
  ASSERT_EQ(BitVector::from_ui(16, 65535).str(10), "65535");
  ASSERT_EQ(BitVector::from_ui(32, 4294967295).str(10), "4294967295");
  ASSERT_EQ(BitVector::from_ui(64, UINT64_MAX).str(10), "18446744073709551615");
  ASSERT_EQ(BitVector::from_ui(65, UINT64_MAX).str(10), "18446744073709551615");
  ASSERT_EQ(BitVector::from_si(68, -3).str(10), "295147905179352825853");
  ASSERT_EQ(BitVector::from_ui(68, static_cast<uint64_t>(-3)).str(10),
            "18446744073709551613");
  ASSERT_EQ(BitVector::from_ui(68, 3).str(10), "3");

  ASSERT_EQ(BitVector(10).str(16), "0");
  ASSERT_EQ(BitVector(6, "101010").str(16), "2a");
  ASSERT_EQ(BitVector(8, "101010").str(16), "2a");
  ASSERT_EQ(BitVector::from_ui(16, 1234).str(16), "4d2");
  ASSERT_EQ(BitVector::from_ui(16, 65530).str(16), "fffa");
  ASSERT_EQ(BitVector::from_ui(16, 65535).str(16), "ffff");
  ASSERT_EQ(BitVector::from_ui(32, 4294967295).str(16), "ffffffff");
  ASSERT_EQ(BitVector::from_ui(64, UINT64_MAX).str(16), "ffffffffffffffff");
  ASSERT_EQ(BitVector::from_ui(65, UINT64_MAX).str(16), "ffffffffffffffff");
  ASSERT_EQ(BitVector::from_si(68, -3).str(16), "ffffffffffffffffd");
  ASSERT_EQ(BitVector::from_ui(68, static_cast<uint64_t>(-3)).str(16),
            "fffffffffffffffd");
  ASSERT_EQ(BitVector::from_ui(68, 3).str(16), "3");
}

TEST_F(TestBitVector, to_uint64)
{
  for (uint64_t i = 0; i < N_TESTS; ++i)
  {
    uint64_t x = (d_rng->pick<uint64_t>() << 32) | d_rng->pick<uint64_t>();
    BitVector bv = BitVector::from_ui(64, x);
    uint64_t y = bv.to_uint64();
    ASSERT_EQ(x, y);
  }
  ASSERT_NO_FATAL_FAILURE(BitVector(28).to_uint64());
  ASSERT_EQ(BitVector(128, std::string(65, '1')).to_uint64(true), UINT64_MAX);
  ASSERT_DEATH_DEBUG(BitVector(128).ibvnot().to_uint64(), "fits_in_size");
}

TEST_F(TestBitVector, compare)
{
  for (uint64_t i = 0; i < 15; ++i)
  {
    BitVector bv1 = BitVector::from_ui(4, i);
    BitVector bv2 = BitVector::from_ui(4, i);
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_TRUE(bv1 == bv2);
  }

  for (uint64_t i = 0; i < 15 - 1; ++i)
  {
    BitVector bv1 = BitVector::from_ui(4, i);
    BitVector bv2 = BitVector::from_ui(4, i + 1);
    ASSERT_LT(bv1.compare(bv2), 0);
    ASSERT_GT(bv2.compare(bv1), 0);
    ASSERT_FALSE(bv1 == bv2);
    ASSERT_TRUE(bv1 != bv2);
  }

  for (uint64_t i = 0, j = 0; i < 15; ++i)
  {
    uint64_t k = static_cast<uint64_t>(rand()) % 16;
    do
    {
      j = static_cast<uint64_t>(rand()) % 16;
    } while (j == k);

    BitVector bv1 = BitVector::from_ui(4, j);
    BitVector bv2 = BitVector::from_ui(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.compare(bv2), 0);
      ASSERT_LT(bv2.compare(bv1), 0);
      ASSERT_FALSE(bv1 == bv2);
      ASSERT_TRUE(bv1 != bv2);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.compare(bv2), 0);
      ASSERT_GT(bv2.compare(bv1), 0);
      ASSERT_FALSE(bv1 == bv2);
      ASSERT_TRUE(bv1 != bv2);
    }
  }
  ASSERT_EQ(BitVector(1).compare(BitVector(2)), -1);
}

TEST_F(TestBitVector, signed_compare)
{
  for (int64_t i = -8; i < 7; ++i)
  {
    BitVector bv1 = BitVector::from_si(4, i);
    BitVector bv2 = BitVector::from_si(4, i);
    ASSERT_EQ(bv1.signed_compare(bv2), 0);
    ASSERT_TRUE(bv1 == bv2);
  }

  for (int64_t i = -8; i < 7 - 1; i++)
  {
    BitVector bv1 = BitVector::from_si(4, i);
    BitVector bv2 = BitVector::from_si(4, i + 1);
    ASSERT_LT(bv1.signed_compare(bv2), 0);
    ASSERT_GT(bv2.signed_compare(bv1), 0);
    ASSERT_FALSE(bv1 == bv2);
    ASSERT_TRUE(bv1 != bv2);
  }

  for (int64_t i = 0, j = 0; i < 15; i++)
  {
    /* j <= 0, k <= 0 */
    int64_t k = rand() % 9;
    do
    {
      j = rand() % 9;
    } while (j == k);
    j = -j;
    k = -k;
    BitVector bv1 = BitVector::from_si(4, j);
    BitVector bv2 = BitVector::from_si(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.signed_compare(bv2), 0);
      ASSERT_LT(bv2.signed_compare(bv1), 0);
      ASSERT_FALSE(bv1 == bv2);
      ASSERT_TRUE(bv1 != bv2);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.signed_compare(bv2), 0);
      ASSERT_GT(bv2.signed_compare(bv1), 0);
      ASSERT_FALSE(bv1 == bv2);
      ASSERT_TRUE(bv1 != bv2);
    }

    {
      /* j <= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 9;
      } while (j == k);
      j = -j;
      BitVector bv1 = BitVector::from_si(4, j);
      BitVector bv2 = BitVector::from_si(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
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
      BitVector bv1 = BitVector::from_si(4, j);
      BitVector bv2 = BitVector::from_si(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
      }
    }

    {
      /* j >= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 8;
      } while (j == k);
      BitVector bv1 = BitVector::from_si(4, -j);
      BitVector bv2 = BitVector::from_si(4, -k);
      if (-j > -k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
      }
      if (-j < -k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
        ASSERT_FALSE(bv1 == bv2);
        ASSERT_TRUE(bv1 != bv2);
      }
    }
  }
  ASSERT_EQ(BitVector(1).signed_compare(BitVector(2)), -1);
}

TEST_F(TestBitVector, is_true)
{
  BitVector bv1 = BitVector::mk_true();
  ASSERT_TRUE(bv1.is_true());
  for (uint64_t i = 1; i < 32; ++i)
  {
    BitVector bv2 = BitVector::mk_one(i);
    BitVector bv3 =
        BitVector::from_ui(i, d_rng->pick<uint64_t>(1, (1u << i) - 1));
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
  for (uint64_t i = 1; i < 32; ++i)
  {
    BitVector bv2 = BitVector::mk_zero(i);
    BitVector bv3 =
        BitVector::from_ui(i, d_rng->pick<uint64_t>(1, (1u << i) - 1));
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

TEST_F(TestBitVector, set_get_flip_bit)
{
  for (uint64_t i = 1; i < 32; ++i)
  {
    BitVector bv(i, *d_rng);
    uint64_t n  = d_rng->pick<uint64_t>(0, i - 1);
    uint32_t v  = bv.bit(n);
    uint32_t vv = d_rng->flip_coin() ? 1 : 0;
    bv.set_bit(n, vv);
    ASSERT_EQ(bv.bit(n), vv);
    ASSERT_TRUE(v == vv || bv.bit(n) == (((~v) << 31) >> 31));
    bv.flip_bit(n);
    ASSERT_EQ(bv.bit(n), (((~vv) << 31) >> 31));
  }
  ASSERT_DEATH_DEBUG(BitVector(5).bit(5), "< size");
}

TEST_F(TestBitVector, is_zero)
{
  for (uint64_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 0);
    }
    else
    {
      BitVector r = BitVector::from_ui(64, 0);
      BitVector l = BitVector::from_ui(i - 64, 0);
      bv3 = l.bvconcat(r);
      assert(bv3.size() == i);
    }
    ASSERT_TRUE(bv1.is_zero());
    ASSERT_TRUE(bv2.is_zero());
    ASSERT_TRUE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 1);
    }
    else
    {
      BitVector r = BitVector::from_ui(i - 64, 1);
      BitVector l = BitVector::from_ui(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv3.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    BitVector bv1 = BitVector::mk_ones(i);
    BitVector bv2(i, s);
    BitVector bv3 = mk_ones(i);
    ASSERT_FALSE(bv1.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_FALSE(bv2.is_zero());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
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

  for (uint64_t i = 2; i <= 128; i++)
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
  for (uint64_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 0);
    }
    else
    {
      BitVector r = BitVector::from_ui(64, 0);
      BitVector l = BitVector::from_ui(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_one());
    ASSERT_FALSE(bv2.is_one());
    ASSERT_FALSE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 1);
    }
    else
    {
      BitVector r = BitVector::from_ui(i - 64, 1);
      BitVector l = BitVector::from_ui(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_TRUE(bv1.is_one());
    ASSERT_TRUE(bv2.is_one());
    ASSERT_TRUE(bv3.is_one());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 2; i <= 128; i++)
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

  for (uint64_t i = 2; i <= 128; i++)
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

  for (uint64_t i = 3; i <= 128; i++)
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
  for (uint64_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 0);
    }
    else
    {
      BitVector r = BitVector::from_ui(64, 0);
      BitVector l = BitVector::from_ui(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 1);
    }
    else
    {
      BitVector r = BitVector::from_ui(i - 64, 1);
      BitVector l = BitVector::from_ui(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_ones());
    ASSERT_FALSE(bv2.is_ones());
    ASSERT_FALSE(bv3.is_ones());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
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

  for (uint64_t i = 2; i <= 128; i++)
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

  for (uint64_t i = 2; i <= 128; i++)
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
  for (uint64_t i = 2; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 0);
    }
    else
    {
      BitVector r = BitVector::from_ui(64, 0);
      BitVector l = BitVector::from_ui(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 3; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 1);
    }
    else
    {
      BitVector r = BitVector::from_ui(i - 64, 1);
      BitVector l = BitVector::from_ui(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_max_signed());
    ASSERT_FALSE(bv2.is_max_signed());
    ASSERT_FALSE(bv3.is_max_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 1; i <= 128; i++)
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

  for (uint64_t i = 1; i <= 128; i++)
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

  for (uint64_t i = 1; i <= 128; i++)
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
  for (uint64_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    BitVector bv1 = BitVector::mk_zero(i);
    BitVector bv2(i, s);
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 0);
    }
    else
    {
      BitVector r = BitVector::from_ui(64, 0);
      BitVector l = BitVector::from_ui(i - 64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    BitVector bv1 = BitVector::mk_one(i);
    BitVector bv2(i, ss.str());
    BitVector bv3;
    if (i <= 64)
    {
      bv3 = BitVector::from_ui(i, 1);
    }
    else
    {
      BitVector r = BitVector::from_ui(i - 64, 1);
      BitVector l = BitVector::from_ui(64, 0);
      bv3 = l.bvconcat(r);
    }
    ASSERT_FALSE(bv1.is_min_signed());
    ASSERT_FALSE(bv2.is_min_signed());
    ASSERT_FALSE(bv3.is_min_signed());
    ASSERT_EQ(bv1.compare(bv2), 0);
    ASSERT_EQ(bv1.compare(bv3), 0);
  }

  for (uint64_t i = 2; i <= 128; i++)
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

  for (uint64_t i = 1; i <= 128; i++)
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

  for (uint64_t i = 1; i <= 128; i++)
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

TEST_F(TestBitVector, is_power_of_two)
{
  for (uint64_t size : {1, 2, 3, 8})
  {
    for (uint64_t i = 0; i < (1u << size); ++i)
    {
      std::string v = to_bin_string(size, i);
      size_t first  = v.find_first_of('1');
      size_t last   = v.find_last_of('1');
      if (first != std::string::npos && first == last)
      {
        ASSERT_TRUE(BitVector(size, v).is_power_of_two());
      }
      else
      {
        ASSERT_FALSE(BitVector(size, v).is_power_of_two());
      }
    }
  }
  for (uint64_t i = 0; i < N_TESTS; ++i)
  {
    uint64_t l = d_rng->pick<uint64_t>();
    for (uint64_t r = 0; r < 2; ++r)
    {
      std::string v = to_bin_string(64, l) + std::to_string(r);
      size_t first  = v.find_first_of('1');
      size_t last   = v.find_last_of('1');
      if (first != std::string::npos && first == last)
      {
        ASSERT_TRUE(BitVector(65, v).is_power_of_two());
      }
      else
      {
        ASSERT_FALSE(BitVector(65, v).is_power_of_two());
      }
    }
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

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVector, dec) { test_unary(DEFAULT, DEC); }

TEST_F(TestBitVector, inc) { test_unary(DEFAULT, INC); }

TEST_F(TestBitVector, neg) { test_unary(DEFAULT, NEG); }

TEST_F(TestBitVector, nego) { test_unary(DEFAULT, NEGO); }

TEST_F(TestBitVector, not ) { test_unary(DEFAULT, NOT); }

TEST_F(TestBitVector, redand) { test_unary(DEFAULT, REDAND); }

TEST_F(TestBitVector, redor) { test_unary(DEFAULT, REDOR); }

TEST_F(TestBitVector, redxor) { test_unary(DEFAULT, REDXOR); }

TEST_F(TestBitVector, add) { test_binary(DEFAULT, ADD); }

TEST_F(TestBitVector, uaddo) { test_binary(DEFAULT, UADDO); }

TEST_F(TestBitVector, usubo) { test_binary(DEFAULT, USUBO); }

TEST_F(TestBitVector, saddo) { test_binary_signed(DEFAULT, SADDO); }

TEST_F(TestBitVector, ssubo) { test_binary_signed(DEFAULT, SSUBO); }

TEST_F(TestBitVector, umulo) { test_binary(DEFAULT, UMULO); }

TEST_F(TestBitVector, smulo) { test_binary_signed(DEFAULT, SMULO); }

TEST_F(TestBitVector, sdivo) { test_binary_signed(DEFAULT, SDIVO); }

TEST_F(TestBitVector, and) { test_binary(DEFAULT, AND); }

TEST_F(TestBitVector, concat) { test_concat(DEFAULT); }

TEST_F(TestBitVector, eq) { test_binary(DEFAULT, EQ); }

TEST_F(TestBitVector, extract) { test_extract(DEFAULT); }

TEST_F(TestBitVector, implies) { test_binary(DEFAULT, IMPLIES); }

TEST_F(TestBitVector, is_neg_overflow)
{
  test_is_neg_overflow(1);
  test_is_neg_overflow(7);
  test_is_neg_overflow(31);
  test_is_neg_overflow(64);
  test_is_neg_overflow(65);
  test_is_neg_overflow(127);
}

TEST_F(TestBitVector, is_uadd_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_uadd_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_uadd_overflow(1);
  test_is_uadd_overflow(7);
  test_is_uadd_overflow(31);
  test_is_uadd_overflow(64);
  test_is_uadd_overflow(65);
  test_is_uadd_overflow(127);
}

TEST_F(TestBitVector, is_sadd_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_sadd_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_sadd_overflow(1);
  test_is_sadd_overflow(7);
  test_is_sadd_overflow(31);
  test_is_sadd_overflow(64);
  test_is_sadd_overflow(65);
  test_is_sadd_overflow(127);
}

TEST_F(TestBitVector, is_usub_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_usub_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_usub_overflow(1);
  test_is_usub_overflow(7);
  test_is_usub_overflow(31);
  test_is_usub_overflow(64);
  test_is_usub_overflow(65);
  test_is_usub_overflow(127);
}

TEST_F(TestBitVector, is_ssub_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_ssub_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_ssub_overflow(1);
  test_is_ssub_overflow(7);
  test_is_ssub_overflow(31);
  test_is_ssub_overflow(64);
  test_is_ssub_overflow(65);
  test_is_ssub_overflow(127);
}

TEST_F(TestBitVector, is_umul_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_umul_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_umul_overflow(1);
  test_is_umul_overflow(7);
  test_is_umul_overflow(31);
  test_is_umul_overflow(64);
  test_is_umul_overflow(65);
  test_is_umul_overflow(127);
}

TEST_F(TestBitVector, is_smul_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_smul_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_smul_overflow(1);
  test_is_smul_overflow(7);
  test_is_smul_overflow(31);
  test_is_smul_overflow(64);
  test_is_smul_overflow(65);
  test_is_smul_overflow(127);
}

TEST_F(TestBitVector, is_sdiv_overflow)
{
  ASSERT_DEATH_DEBUG(
      BitVector::mk_zero(32).is_sdiv_overflow(BitVector(33, *d_rng)),
      "d_size == bv.d_size");

  test_is_sdiv_overflow(1);
  test_is_sdiv_overflow(7);
  test_is_sdiv_overflow(31);
  test_is_sdiv_overflow(64);
  test_is_sdiv_overflow(65);
  test_is_sdiv_overflow(127);
}

TEST_F(TestBitVector, ite) { test_ite(DEFAULT); }

TEST_F(TestBitVector, modinv) { test_modinv(DEFAULT); }

TEST_F(TestBitVector, mul) { test_binary(DEFAULT, MUL); }

TEST_F(TestBitVector, nand) { test_binary(DEFAULT, NAND); }

TEST_F(TestBitVector, ne) { test_binary(DEFAULT, NE); }

TEST_F(TestBitVector, or) { test_binary(DEFAULT, OR); }

TEST_F(TestBitVector, nor) { test_binary(DEFAULT, NOR); }

TEST_F(TestBitVector, sdiv) { test_binary_signed(DEFAULT, SDIV); }

TEST_F(TestBitVector, sext) { test_extend(DEFAULT, SEXT); }

TEST_F(TestBitVector, repeat) { test_repeat(DEFAULT); }

TEST_F(TestBitVector, roli) { test_rotate(DEFAULT, ROLI); }

TEST_F(TestBitVector, rol) { test_rotate(DEFAULT, ROL); }

TEST_F(TestBitVector, rori) { test_rotate(DEFAULT, RORI); }

TEST_F(TestBitVector, ror) { test_rotate(DEFAULT, ROR); }

TEST_F(TestBitVector, shl)
{
  test_binary(DEFAULT, SHL);
  test_shift(DEFAULT, SHL, true);
  test_shift(DEFAULT, SHL, false);
}

TEST_F(TestBitVector, shr)
{
  test_binary(DEFAULT, SHR);
  test_shift(DEFAULT, SHR, true);
  test_shift(DEFAULT, SHR, false);
}

TEST_F(TestBitVector, ashr)
{
  test_binary(DEFAULT, ASHR);
  test_shift(DEFAULT, ASHR, true);
  test_shift(DEFAULT, ASHR, false);
}

TEST_F(TestBitVector, slt) { test_binary_signed(DEFAULT, SLT); }

TEST_F(TestBitVector, sle) { test_binary_signed(DEFAULT, SLE); }

TEST_F(TestBitVector, sgt) { test_binary_signed(DEFAULT, SGT); }

TEST_F(TestBitVector, sge) { test_binary_signed(DEFAULT, SGE); }

TEST_F(TestBitVector, sub) { test_binary(DEFAULT, SUB); }

TEST_F(TestBitVector, srem) { test_binary_signed(DEFAULT, SREM); }

TEST_F(TestBitVector, smod) { test_binary_signed(DEFAULT, SMOD); }

TEST_F(TestBitVector, udiv) { test_binary(DEFAULT, UDIV); }

TEST_F(TestBitVector, ult) { test_binary(DEFAULT, ULT); }

TEST_F(TestBitVector, ule) { test_binary(DEFAULT, ULE); }

TEST_F(TestBitVector, ugt) { test_binary(DEFAULT, UGT); }

TEST_F(TestBitVector, uge) { test_binary(DEFAULT, UGE); }

TEST_F(TestBitVector, urem) { test_binary(DEFAULT, UREM); }

TEST_F(TestBitVector, xor) { test_binary(DEFAULT, XOR); }

TEST_F(TestBitVector, xnor) { test_binary(DEFAULT, XNOR); }

TEST_F(TestBitVector, zext) { test_extend(DEFAULT, ZEXT); }

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVector, idec)
{
  test_unary(INPLACE_THIS_ALL, DEC);
  test_unary(INPLACE_THIS, DEC);
}

TEST_F(TestBitVector, iinc)
{
  test_unary(INPLACE_THIS_ALL, INC);
  test_unary(INPLACE_THIS, INC);
}

TEST_F(TestBitVector, ineg)
{
  test_unary(INPLACE_THIS_ALL, NEG);
  test_unary(INPLACE_THIS, NEG);
}

TEST_F(TestBitVector, inego)
{
  test_unary(INPLACE_THIS_ALL, NEGO);
  test_unary(INPLACE_THIS, NEGO);
}

TEST_F(TestBitVector, inot)
{
  test_unary(INPLACE_THIS_ALL, NOT);
  test_unary(INPLACE_THIS, NOT);
}

TEST_F(TestBitVector, iredand)
{
  test_unary(INPLACE_THIS_ALL, REDAND);
  test_unary(INPLACE_THIS, REDAND);
}

TEST_F(TestBitVector, iredor)
{
  test_unary(INPLACE_THIS_ALL, REDOR);
  test_unary(INPLACE_THIS, REDOR);
}

TEST_F(TestBitVector, iredxor)
{
  test_unary(INPLACE_THIS_ALL, REDXOR);
  test_unary(INPLACE_THIS, REDXOR);
}

TEST_F(TestBitVector, iadd)
{
  test_binary(INPLACE, ADD);
  test_binary(INPLACE_THIS_ALL, ADD);
  test_binary(INPLACE_THIS, ADD);
}

TEST_F(TestBitVector, iuaddo)
{
  test_binary(INPLACE, UADDO);
  test_binary(INPLACE_THIS_ALL, UADDO);
  test_binary(INPLACE_THIS, UADDO);
}

TEST_F(TestBitVector, isaddo)
{
  test_binary_signed(INPLACE, SADDO);
  test_binary_signed(INPLACE_THIS_ALL, SADDO);
  test_binary_signed(INPLACE_THIS, SADDO);
}

TEST_F(TestBitVector, iusubo)
{
  test_binary(INPLACE, USUBO);
  test_binary(INPLACE_THIS_ALL, USUBO);
  test_binary(INPLACE_THIS, USUBO);
}

TEST_F(TestBitVector, issubo)
{
  test_binary_signed(INPLACE, SSUBO);
  test_binary_signed(INPLACE_THIS_ALL, SSUBO);
  test_binary_signed(INPLACE_THIS, SSUBO);
}

TEST_F(TestBitVector, iumulo)
{
  test_binary(INPLACE, UMULO);
  test_binary(INPLACE_THIS_ALL, UMULO);
  test_binary(INPLACE_THIS, UMULO);
}

TEST_F(TestBitVector, ismulo)
{
  test_binary_signed(INPLACE, SMULO);
  test_binary_signed(INPLACE_THIS_ALL, SMULO);
  test_binary_signed(INPLACE_THIS, SMULO);
}

TEST_F(TestBitVector, isdivo)
{
  test_binary_signed(INPLACE, SDIVO);
  test_binary_signed(INPLACE_THIS_ALL, SDIVO);
  test_binary_signed(INPLACE_THIS, SDIVO);
}

TEST_F(TestBitVector, iand)
{
  test_binary(INPLACE, AND);
  test_binary(INPLACE_THIS_ALL, AND);
  test_binary(INPLACE_THIS, AND);
}

TEST_F(TestBitVector, iconcat)
{
  test_concat(INPLACE);
  test_concat(INPLACE_THIS_ALL);
  test_concat(INPLACE_THIS);
}

TEST_F(TestBitVector, ieq)
{
  test_binary(INPLACE, EQ);
  test_binary(INPLACE_THIS_ALL, EQ);
  test_binary(INPLACE_THIS, EQ);
}

TEST_F(TestBitVector, iextract)
{
  test_extract(INPLACE);
  test_extract(INPLACE_THIS_ALL);
  test_extract(INPLACE_THIS);
}

TEST_F(TestBitVector, iimplies)
{
  test_binary(INPLACE, IMPLIES);
  test_binary(INPLACE_THIS_ALL, IMPLIES);
  test_binary(INPLACE_THIS, IMPLIES);
}

TEST_F(TestBitVector, iite) { test_ite(INPLACE_THIS_ALL); }

TEST_F(TestBitVector, imodinv)
{
  test_modinv(INPLACE_THIS_ALL);
  test_modinv(INPLACE_THIS);
}

TEST_F(TestBitVector, imul)
{
  test_binary(INPLACE, MUL);
  test_binary(INPLACE_THIS_ALL, MUL);
  test_binary(INPLACE_THIS, MUL);
}

TEST_F(TestBitVector, inand)
{
  test_binary(INPLACE, NAND);
  test_binary(INPLACE_THIS_ALL, NAND);
  test_binary(INPLACE_THIS, NAND);
}

TEST_F(TestBitVector, ine)
{
  test_binary(INPLACE, NE);
  test_binary(INPLACE_THIS_ALL, NE);
  test_binary(INPLACE_THIS, NE);
}

TEST_F(TestBitVector, ior)
{
  test_binary(INPLACE, OR);
  test_binary(INPLACE_THIS_ALL, OR);
  test_binary(INPLACE_THIS, OR);
}

TEST_F(TestBitVector, inor)
{
  test_binary(INPLACE, NOR);
  test_binary(INPLACE_THIS_ALL, NOR);
  test_binary(INPLACE_THIS, NOR);
}

TEST_F(TestBitVector, isdiv)
{
  test_binary_signed(INPLACE, SDIV);
  test_binary_signed(INPLACE_THIS_ALL, SDIV);
  test_binary_signed(INPLACE_THIS, SDIV);
}

TEST_F(TestBitVector, isext)
{
  test_extend(INPLACE, SEXT);
  test_extend(INPLACE_THIS, SEXT);
  test_extend(INPLACE_THIS_ALL, SEXT);
}

TEST_F(TestBitVector, irepeat)
{
  test_repeat(INPLACE);
  test_repeat(INPLACE_THIS);
  test_repeat(INPLACE_THIS_ALL);
}

TEST_F(TestBitVector, ishl)
{
  test_binary(INPLACE, SHL);
  test_binary(INPLACE_THIS_ALL, SHL);
  test_binary(INPLACE_THIS, SHL);
  test_shift(INPLACE_THIS_ALL, SHL, true);
  test_shift(INPLACE_THIS_ALL, SHL, false);
  test_shift(INPLACE_THIS, SHL, true);
  test_shift(INPLACE_THIS, SHL, false);
}

TEST_F(TestBitVector, ishr)
{
  test_binary(INPLACE, SHR);
  test_binary(INPLACE_THIS_ALL, SHR);
  test_binary(INPLACE_THIS, SHR);
  test_shift(INPLACE_THIS_ALL, SHR, true);
  test_shift(INPLACE_THIS_ALL, SHR, false);
  test_shift(INPLACE_THIS, SHR, true);
  test_shift(INPLACE_THIS, SHR, false);
}

TEST_F(TestBitVector, iashr)
{
  test_binary(INPLACE, ASHR);
  test_binary(INPLACE_THIS_ALL, ASHR);
  test_binary(INPLACE_THIS, ASHR);
  test_shift(INPLACE_THIS_ALL, ASHR, false);
  test_shift(INPLACE_THIS, ASHR, false);
}

TEST_F(TestBitVector, iroli)
{
  test_rotate(INPLACE, ROLI);
  test_rotate(INPLACE_THIS, ROLI);
  test_rotate(INPLACE_THIS_ALL, ROLI);
}

TEST_F(TestBitVector, irol)
{
  test_rotate(INPLACE, ROL);
  test_rotate(INPLACE_THIS, ROL);
  test_rotate(INPLACE_THIS_ALL, ROL);
}

TEST_F(TestBitVector, irori)
{
  test_rotate(INPLACE, RORI);
  test_rotate(INPLACE_THIS, RORI);
  test_rotate(INPLACE_THIS_ALL, RORI);
}

TEST_F(TestBitVector, iror)
{
  test_rotate(INPLACE, ROR);
  test_rotate(INPLACE_THIS, ROR);
  test_rotate(INPLACE_THIS_ALL, ROR);
}

TEST_F(TestBitVector, islt)
{
  test_binary_signed(INPLACE, SLT);
  test_binary_signed(INPLACE_THIS_ALL, SLT);
  test_binary_signed(INPLACE_THIS, SLT);
}

TEST_F(TestBitVector, isle)
{
  test_binary_signed(INPLACE, SLE);
  test_binary_signed(INPLACE_THIS_ALL, SLE);
  test_binary_signed(INPLACE_THIS, SLE);
}

TEST_F(TestBitVector, isgt)
{
  test_binary_signed(INPLACE, SGT);
  test_binary_signed(INPLACE_THIS_ALL, SGT);
  test_binary_signed(INPLACE_THIS, SGT);
}

TEST_F(TestBitVector, isge)
{
  test_binary_signed(INPLACE, SGE);
  test_binary_signed(INPLACE_THIS_ALL, SGE);
  test_binary_signed(INPLACE_THIS, SGE);
}

TEST_F(TestBitVector, isub)
{
  test_binary(INPLACE, SUB);
  test_binary(INPLACE_THIS_ALL, SUB);
  test_binary(INPLACE_THIS, SUB);
}

TEST_F(TestBitVector, isrem)
{
  test_binary_signed(INPLACE, SREM);
  test_binary_signed(INPLACE_THIS_ALL, SREM);
  test_binary_signed(INPLACE_THIS, SREM);
}

TEST_F(TestBitVector, ismod)
{
  test_binary_signed(INPLACE, SMOD);
  test_binary_signed(INPLACE_THIS_ALL, SMOD);
  test_binary_signed(INPLACE_THIS, SMOD);
}

TEST_F(TestBitVector, iudiv)
{
  test_binary(INPLACE, UDIV);
  test_binary(INPLACE_THIS_ALL, UDIV);
  test_binary(INPLACE_THIS, UDIV);
}

TEST_F(TestBitVector, iult)
{
  test_binary(INPLACE, ULT);
  test_binary(INPLACE_THIS_ALL, ULT);
  test_binary(INPLACE_THIS, ULT);
}

TEST_F(TestBitVector, iule)
{
  test_binary(INPLACE, ULE);
  test_binary(INPLACE_THIS_ALL, ULE);
  test_binary(INPLACE_THIS, ULE);
}

TEST_F(TestBitVector, iugt)
{
  test_binary(INPLACE, UGT);
  test_binary(INPLACE_THIS_ALL, UGT);
  test_binary(INPLACE_THIS, UGT);
}

TEST_F(TestBitVector, iuge)
{
  test_binary(INPLACE, UGE);
  test_binary(INPLACE_THIS_ALL, UGE);
  test_binary(INPLACE_THIS, UGE);
}

TEST_F(TestBitVector, iurem)
{
  test_binary(INPLACE, UREM);
  test_binary(INPLACE_THIS_ALL, UREM);
  test_binary(INPLACE_THIS, UREM);
}
TEST_F(TestBitVector, ixor)
{
  test_binary(INPLACE, XOR);
  test_binary(INPLACE_THIS_ALL, XOR);
  test_binary(INPLACE_THIS, XOR);
}

TEST_F(TestBitVector, ixnor)
{
  test_binary(INPLACE, XNOR);
  test_binary(INPLACE_THIS_ALL, XNOR);
  test_binary(INPLACE_THIS, XNOR);
}

TEST_F(TestBitVector, izext)
{
  test_extend(INPLACE, ZEXT);
  test_extend(INPLACE_THIS, ZEXT);
  test_extend(INPLACE_THIS_ALL, ZEXT);
}

TEST_F(TestBitVector, bvpow)
{
  ASSERT_EQ(BitVector::from_ui(128, 1).ibvshl(32),
            BitVector::from_ui(128, 2).ibvpow(util::Integer(32).gmp_value()));
  ASSERT_EQ(BitVector::from_ui(16, 0),
            BitVector::from_ui(16, 2).bvpow(util::Integer(16).gmp_value()));
  ASSERT_EQ(BitVector::from_ui(16, 9),
            BitVector::from_ui(16, 3).ibvpow(util::Integer(2).gmp_value()));
  ASSERT_EQ(BitVector::from_ui(16, 125),
            BitVector::from_ui(16, 5).bvpow(util::Integer(3).gmp_value()));
  ASSERT_EQ(BitVector::from_ui(8, 87),
            BitVector::from_ui(8, 7).ibvpow(util::Integer(3).gmp_value()));
  ASSERT_EQ(BitVector::from_ui(8, 43),
            BitVector::from_ui(8, 19).bvpow(util::Integer(331).gmp_value()));
}

/* -------------------------------------------------------------------------- */

#if 0
TEST_F(TestBitVector, add32)
{
  BitVector res;
  BitVector a0(32, *d_rng);
  BitVector a1(32, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvadd(a1);
  }
}

TEST_F(TestBitVector, iadd32)
{
  BitVector res(32);
  BitVector a0(32, *d_rng);
  BitVector a1(32, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res.ibvadd(a0, a1);
  }
}

TEST_F(TestBitVector, add64)
{
  BitVector res;
  BitVector a0(64, *d_rng);
  BitVector a1(64, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvadd(a1);
  }
}

TEST_F(TestBitVector, add65)
{
  BitVector res;
  BitVector a0(65, *d_rng);
  BitVector a1(65, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvadd(a1);
  }
}

TEST_F(TestBitVector, add129)
{
  BitVector res;
  BitVector a0(129, *d_rng);
  BitVector a1(129, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvadd(a1);
  }
}

TEST_F(TestBitVector, mul64)
{
  BitVector res;
  BitVector a0(64, *d_rng);
  BitVector a1(64, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvmul(a1);
  }
}

TEST_F(TestBitVector, mul65)
{
  BitVector res;
  BitVector a0(65, *d_rng);
  BitVector a1(65, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvmul(a1);
  }
}

TEST_F(TestBitVector, mul129)
{
  BitVector res;
  BitVector a0(129, *d_rng);
  BitVector a1(129, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res = a0.bvmul(a1);
  }
}

TEST_F(TestBitVector, iadd65)
{
  BitVector res(65);
  BitVector a0(65, *d_rng);
  BitVector a1(65, *d_rng);
  for (uint32_t i = 0; i < 10000000; ++i)
  {
    res.ibvadd(a0, a1);
  }
}
#endif

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVector, udivurem)
{
  test_udivurem(1);
  test_udivurem(7);
  test_udivurem(31);
  test_udivurem(64);
  test_udivurem(65);
  test_udivurem(127);
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
