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
#include "bzlaaig.h"
#include "dumper/bzladumpaig.h"
}

class TestSatMgr : public TestBzla
{
 protected:
  void SetUp() override
  {
    TestBzla::SetUp();
    d_smgr = bzla_sat_mgr_new(d_bzla);
  }
  void TearDown() override
  {
    bzla_sat_mgr_delete(d_smgr);
    TestBzla::TearDown();
  }
  BzlaSATMgr *d_smgr = nullptr;
};

TEST_F(TestSatMgr, new_delete) {}

TEST_F(TestSatMgr, next_cnf_id)
{
  bzla_sat_enable_solver(d_smgr);
  bzla_sat_init(d_smgr);
  ASSERT_EQ(bzla_sat_mgr_next_cnf_id(d_smgr), 2);
  ASSERT_EQ(bzla_sat_mgr_next_cnf_id(d_smgr), 3);
  ASSERT_EQ(bzla_sat_mgr_next_cnf_id(d_smgr), 4);
  bzla_sat_reset(d_smgr);
}
