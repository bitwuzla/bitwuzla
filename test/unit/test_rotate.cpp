/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlautil.h"
}

class TestRotate : public TestBitwuzla
{
 protected:
  void test_rot(uint32_t bw, uint32_t nbits, bool is_left)
  {
    int32_t res;
    BitwuzlaKind kind, kindi;

    const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, bw);
    const BitwuzlaTerm *e0   = bitwuzla_mk_const(d_bzla, sort, "e0");

    if (is_left)
    {
      kind  = BITWUZLA_KIND_BV_ROL;
      kindi = BITWUZLA_KIND_BV_ROLI;
    }
    else
    {
      kind  = BITWUZLA_KIND_BV_ROR;
      kindi = BITWUZLA_KIND_BV_RORI;
    }

    const BitwuzlaTerm *roti =
        bitwuzla_mk_term1_indexed1(d_bzla, kindi, e0, nbits);
    const BitwuzlaTerm *rot0 = bitwuzla_mk_term2(
        d_bzla, kind, e0, bitwuzla_mk_bv_value_uint64(d_bzla, sort, nbits));

    const BitwuzlaTerm *ne0 =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_DISTINCT, rot0, roti);

    bitwuzla_assert(d_bzla, ne0);
    res = bitwuzla_check_sat(d_bzla);
    (void) res;
    assert(res == BITWUZLA_UNSAT);
  }
};

TEST_F(TestRotate, rol_1_0) { test_rot(1, 0, true); }

TEST_F(TestRotate, rol_2_0) { test_rot(2, 0, true); }

TEST_F(TestRotate, rol_3_0) { test_rot(3, 0, true); }

TEST_F(TestRotate, rol_5_0) { test_rot(5, 0, true); }

TEST_F(TestRotate, rol_12_0) { test_rot(12, 0, true); }

TEST_F(TestRotate, rol_32_0) { test_rot(32, 0, true); }

TEST_F(TestRotate, rol_1_1) { test_rot(1, 1, true); }

TEST_F(TestRotate, rol_2_1) { test_rot(2, 1, true); }

TEST_F(TestRotate, rol_3_1) { test_rot(3, 1, true); }

TEST_F(TestRotate, rol_5_1) { test_rot(5, 1, true); }

TEST_F(TestRotate, rol_12_1) { test_rot(12, 1, true); }

TEST_F(TestRotate, rol_32_1) { test_rot(32, 1, true); }

TEST_F(TestRotate, rol_2_2) { test_rot(2, 2, true); }

TEST_F(TestRotate, rol_3_3) { test_rot(3, 3, true); }

TEST_F(TestRotate, rol_5_5) { test_rot(5, 5, true); }

TEST_F(TestRotate, rol_12_12) { test_rot(12, 12, true); }

TEST_F(TestRotate, rol_32_32) { test_rot(32, 32, true); }

TEST_F(TestRotate, ror_1_0) { test_rot(1, 0, false); }

TEST_F(TestRotate, ror_2_0) { test_rot(2, 0, false); }

TEST_F(TestRotate, ror_3_0) { test_rot(3, 0, false); }

TEST_F(TestRotate, ror_5_0) { test_rot(5, 0, false); }

TEST_F(TestRotate, ror_12_0) { test_rot(12, 0, false); }

TEST_F(TestRotate, ror_32_0) { test_rot(32, 0, false); }

TEST_F(TestRotate, ror_1_1) { test_rot(1, 1, false); }

TEST_F(TestRotate, ror_2_1) { test_rot(2, 1, false); }

TEST_F(TestRotate, ror_3_1) { test_rot(3, 1, false); }

TEST_F(TestRotate, ror_5_1) { test_rot(5, 1, false); }

TEST_F(TestRotate, ror_12_1) { test_rot(12, 1, false); }

TEST_F(TestRotate, ror_32_1) { test_rot(32, 1, false); }

TEST_F(TestRotate, ror_2_2) { test_rot(2, 2, false); }

TEST_F(TestRotate, ror_3_3) { test_rot(3, 3, false); }

TEST_F(TestRotate, ror_5_5) { test_rot(5, 5, false); }

TEST_F(TestRotate, ror_12_12) { test_rot(12, 12, false); }

TEST_F(TestRotate, ror_32_32) { test_rot(32, 32, false); }
