/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <cstdint>

#include "test/unit/test.h"
#include "type/card.h"
#include "type/type.h"
#include "type/type_manager.h"

namespace bzla::test {

using namespace bzla::type;

class TestCardinality : public TestCommon
{
 protected:
  /**
   * Assert that the cardinality of `type` is exactly `card`. The boundary
   * between cardinality_lt() returning false and true uniquely pins down the
   * cardinality: it is false for bounds <= card and true for bounds > card.
   */
  void check_card(const Type& type, uint64_t card)
  {
    EXPECT_FALSE(cardinality_lt(type, card)) << "expected cardinality " << card;
    EXPECT_TRUE(cardinality_lt(type, card + 1))
        << "expected cardinality " << card;
  }

  /**
   * Assert that the cardinality of `type` is at least 2^64, i.e. larger than
   * any uint64_t bound. These are the cases whose exact cardinality is
   * unrepresentable (or astronomically large); cardinality_lt() must saturate
   * rather than overflow or crash.
   */
  void check_card_huge(const Type& type)
  {
    EXPECT_FALSE(cardinality_lt(type, 3));
    EXPECT_FALSE(cardinality_lt(type, 1000000));
    EXPECT_FALSE(cardinality_lt(type, UINT64_MAX));
  }

  TypeManager d_tm;
};

TEST_F(TestCardinality, boolean) { check_card(d_tm.mk_bool_type(), 2); }

TEST_F(TestCardinality, bv)
{
  check_card(d_tm.mk_bv_type(1), 2);
  check_card(d_tm.mk_bv_type(8), 256);
  check_card(d_tm.mk_bv_type(16), 65536);
  check_card(d_tm.mk_bv_type(32), UINT64_C(4294967296));
  check_card(d_tm.mk_bv_type(63), UINT64_C(9223372036854775808));
  // 2^64 exceeds uint64_t.
  check_card_huge(d_tm.mk_bv_type(64));
  // Very wide bit-vectors must saturate, not materialize a huge integer.
  check_card_huge(d_tm.mk_bv_type(1000));
}

TEST_F(TestCardinality, rm)
{
  // RNA, RNE, RTN, RTP, RTZ
  check_card(d_tm.mk_rm_type(), 5);
}

TEST_F(TestCardinality, fp)
{
  // card = 3 + 2^{sig_size} * (2^{exp_size} - 1)
  // Float16: 3 + 2^11 * (2^5 - 1) = 3 + 2048 * 31
  check_card(d_tm.mk_fp_type(5, 11), 63491);
  // Float32: 3 + 2^24 * (2^8 - 1) = 3 + 16777216 * 255
  check_card(d_tm.mk_fp_type(8, 24), UINT64_C(4278190083));
  // Float128: card far exceeds uint64_t.
  check_card_huge(d_tm.mk_fp_type(15, 113));
}

TEST_F(TestCardinality, array)
{
  Type bool_type = d_tm.mk_bool_type();
  Type bv2       = d_tm.mk_bv_type(2);
  Type bv3       = d_tm.mk_bv_type(3);
  Type bv8       = d_tm.mk_bv_type(8);
  Type bv64      = d_tm.mk_bv_type(64);

  // Cardinality of (index -> element) is |element|^|index|.
  // (Bool -> Bool): 2^2
  check_card(d_tm.mk_array_type(bool_type, bool_type), 4);
  // (BV2 -> Bool): 2^4, asymmetric: index and element are not interchangeable.
  check_card(d_tm.mk_array_type(bv2, bool_type), 16);
  // (Bool -> BV2): 4^2
  check_card(d_tm.mk_array_type(bool_type, bv2), 16);
  // (BV3 -> BV8): 256^8 = 2^64, exceeds uint64_t.
  check_card_huge(d_tm.mk_array_type(bv3, bv8));
  // (BV64 -> Bool): 2^(2^64). The index cardinality alone overflows a 64-bit
  // exponent; cardinality_lt() must saturate instead of crashing/truncating.
  check_card_huge(d_tm.mk_array_type(bv64, bool_type));
}

TEST_F(TestCardinality, array_nested)
{
  Type bool_type = d_tm.mk_bool_type();
  // (Bool -> (Bool -> Bool)): inner array has cardinality 2^2 = 4, so the
  // result is 4^2 = 16.
  Type inner = d_tm.mk_array_type(bool_type, bool_type);
  check_card(d_tm.mk_array_type(bool_type, inner), 16);
}

TEST_F(TestCardinality, fun)
{
  Type bool_type = d_tm.mk_bool_type();
  Type bv2       = d_tm.mk_bv_type(2);
  Type bv3       = d_tm.mk_bv_type(3);
  Type bv32      = d_tm.mk_bv_type(32);
  Type bv64      = d_tm.mk_bv_type(64);

  // Cardinality of (d_1, ..., d_n -> codomain) is
  // |codomain|^(|d_1| * ... * |d_n|).

  // (Bool -> Bool): 2^2
  check_card(d_tm.mk_fun_type({bool_type, bool_type}), 4);
  // (Bool, Bool -> Bool): 2^(2*2) = 2^4. Distinguishes the exponent (product
  // of domain cardinalities) from the codomain cardinality.
  check_card(d_tm.mk_fun_type({bool_type, bool_type, bool_type}), 16);
  // (BV2, Bool -> Bool): 2^(4*2) = 2^8. Also distinguishes base from exponent.
  check_card(d_tm.mk_fun_type({bv2, bool_type, bool_type}), 256);
  // (Bool -> BV2): 4^2
  check_card(d_tm.mk_fun_type({bool_type, bv2}), 16);
  // (BV3, Bool -> BV2): 4^(8*2) = 4^16 = 2^32
  check_card(d_tm.mk_fun_type({bv3, bool_type, bv2}), UINT64_C(4294967296));
  // (BV64 -> Bool): 2^(2^64), exponent overflows; must saturate.
  check_card_huge(d_tm.mk_fun_type({bv64, bool_type}));
  // (BV32, BV32, BV32 -> Bool): 2^(2^96). The domain product itself overflows
  // and must be saturated before being used as an exponent.
  check_card_huge(d_tm.mk_fun_type({bv32, bv32, bv32, bool_type}));
}

TEST_F(TestCardinality, fun_nested)
{
  Type bool_type = d_tm.mk_bool_type();
  // (Bool -> (Bool -> Bool)): codomain array has cardinality 2^2 = 4, domain
  // cardinality is 2, so the result is 4^2 = 16.
  Type array_type = d_tm.mk_array_type(bool_type, bool_type);
  check_card(d_tm.mk_fun_type({bool_type, array_type}), 16);
}

}  // namespace bzla::test
