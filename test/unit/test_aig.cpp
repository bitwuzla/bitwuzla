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

class TestAig : public TestBzla
{
 protected:
  void binary_commutative_aig_test(BzlaAIG *(*func)(BzlaAIGMgr *,
                                                    BzlaAIG *,
                                                    BzlaAIG *) )
  {
    BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
    BzlaAIG *aig1    = bzla_aig_var(amgr);
    BzlaAIG *aig2    = bzla_aig_var(amgr);
    BzlaAIG *aig3    = func(amgr, aig1, aig2);
    BzlaAIG *aig4    = func(amgr, aig1, aig2);
    BzlaAIG *aig5    = func(amgr, aig2, aig1);
    ASSERT_TRUE(aig3 == aig4);
    ASSERT_TRUE(aig4 == aig5);
    bzla_dumpaig_dump_aig(amgr, 0, d_log_file, aig5);
    bzla_aig_release(amgr, aig1);
    bzla_aig_release(amgr, aig2);
    bzla_aig_release(amgr, aig3);
    bzla_aig_release(amgr, aig4);
    bzla_aig_release(amgr, aig5);
    bzla_aig_mgr_delete(amgr);
  }
};

TEST_F(TestAig, new_delete_aig_mgr)
{
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, false)
{
  open_log_file("false_aig");
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  bzla_dumpaig_dump_aig(amgr, 0, d_log_file, BZLA_AIG_FALSE);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, true)
{
  open_log_file("true_aig");
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  bzla_dumpaig_dump_aig(amgr, 0, d_log_file, BZLA_AIG_TRUE);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, var)
{
  open_log_file("var_aig");
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  BzlaAIG *var     = bzla_aig_var(amgr);
  ASSERT_TRUE(bzla_aig_is_var(var));
  bzla_dumpaig_dump_aig(amgr, 0, d_log_file, var);
  bzla_aig_release(amgr, var);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, not )
{
  open_log_file("not_aig");
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  BzlaAIG *var     = bzla_aig_var(amgr);
  BzlaAIG *_not    = bzla_aig_not(amgr, var);
  bzla_dumpaig_dump_aig(amgr, 0, d_log_file, _not);
  bzla_aig_release(amgr, var);
  bzla_aig_release(amgr, _not);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, and)
{
  open_log_file("and_aig");
  binary_commutative_aig_test(bzla_aig_and);
}

TEST_F(TestAig, or)
{
  open_log_file("or_aig");
  binary_commutative_aig_test(bzla_aig_or);
}

TEST_F(TestAig, eq)
{
  open_log_file("eq_aig");
  binary_commutative_aig_test(bzla_aig_eq);
}

TEST_F(TestAig, cond)
{
  open_log_file("cond_aig");
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  BzlaAIG *aig1    = bzla_aig_var(amgr);
  BzlaAIG *aig2    = bzla_aig_var(amgr);
  BzlaAIG *aig3    = bzla_aig_var(amgr);
  BzlaAIG *aig4    = bzla_aig_cond(amgr, aig1, aig2, aig3);
  BzlaAIG *aig5    = bzla_aig_cond(amgr, aig1, aig2, aig3);
  ASSERT_TRUE(aig4 == aig5);
  bzla_dumpaig_dump_aig(amgr, 0, d_log_file, aig5);
  bzla_aig_release(amgr, aig1);
  bzla_aig_release(amgr, aig2);
  bzla_aig_release(amgr, aig3);
  bzla_aig_release(amgr, aig4);
  bzla_aig_release(amgr, aig5);
  bzla_aig_mgr_delete(amgr);
}

TEST_F(TestAig, aig_to_sat)
{
  BzlaAIGMgr *amgr = bzla_aig_mgr_new(d_bzla);
  BzlaSATMgr *smgr = bzla_aig_get_sat_mgr(amgr);
  BzlaAIG *var1    = bzla_aig_var(amgr);
  BzlaAIG *var2    = bzla_aig_var(amgr);
  BzlaAIG *var3    = bzla_aig_var(amgr);
  BzlaAIG *var4    = bzla_aig_var(amgr);
  BzlaAIG *and1    = bzla_aig_and(amgr, var1, var2);
  BzlaAIG *and2    = bzla_aig_and(amgr, var3, var4);
  BzlaAIG *and3    = bzla_aig_or(amgr, and1, and2);
  bzla_sat_enable_solver(smgr);
  bzla_sat_init(smgr);
  bzla_aig_to_sat(amgr, and3);
  bzla_sat_reset(smgr);
  bzla_aig_release(amgr, var1);
  bzla_aig_release(amgr, var2);
  bzla_aig_release(amgr, var3);
  bzla_aig_release(amgr, var4);
  bzla_aig_release(amgr, and1);
  bzla_aig_release(amgr, and2);
  bzla_aig_release(amgr, and3);
  bzla_aig_mgr_delete(amgr);
}
