/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlautil.h"
}

class TestRotate : public TestBoolector
{
 protected:
  void test_rot(uint32_t bw, uint32_t nbits, bool is_left)
  {
    bool ispow2;
    int32_t res;
    uint32_t bw_log2;
    BoolectorSort sort, sort_log2;
    BoolectorNode *rot0, *rot0_e1;
    BoolectorNode *rot1, *rot1_e1;
    BoolectorNode *roti;
    BoolectorNode *e0;
    BoolectorNode *ne0, *ne1, *ne2;
    BoolectorNode *(*fun)(Bzla *, BoolectorNode *, BoolectorNode *);
    BoolectorNode *(*funi)(Bzla *, BoolectorNode *, uint32_t);

    fun  = is_left ? boolector_bv_rol : boolector_bv_ror;
    funi = is_left ? boolector_roli : boolector_rori;

    ispow2 = bzla_util_is_power_of_2(bw);
    sort   = boolector_bv_sort(d_bzla, bw);
    e0     = boolector_var(d_bzla, sort, "e0");

    roti = funi(d_bzla, e0, nbits);

    rot0_e1 = boolector_unsigned_int(d_bzla, nbits, sort);
    rot0    = fun(d_bzla, e0, rot0_e1);

    ne0 = boolector_ne(d_bzla, rot0, roti);

    if (ispow2)
    {
      bw_log2 = bzla_util_log_2(bw);
      if (bw_log2)
      {
        sort_log2 = boolector_bv_sort(d_bzla, bw_log2);
        rot1_e1   = boolector_unsigned_int(d_bzla, nbits, sort_log2);
        rot1      = fun(d_bzla, e0, rot1_e1);
        ne1       = boolector_ne(d_bzla, rot1, rot0);
        ne2       = boolector_ne(d_bzla, rot1, roti);
        boolector_assert(d_bzla, ne1);
        boolector_assert(d_bzla, ne2);
        boolector_release(d_bzla, ne1);
        boolector_release(d_bzla, ne2);
        boolector_release(d_bzla, rot1);
        boolector_release(d_bzla, rot1_e1);
        boolector_release_sort(d_bzla, sort_log2);
      }
    }

    boolector_assert(d_bzla, ne0);
    res = boolector_sat(d_bzla);
    (void) res;
    assert(res == BOOLECTOR_UNSAT);

    boolector_release(d_bzla, ne0);
    boolector_release(d_bzla, rot0);
    boolector_release(d_bzla, rot0_e1);
    boolector_release(d_bzla, roti);
    boolector_release(d_bzla, e0);
    boolector_release_sort(d_bzla, sort);
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
