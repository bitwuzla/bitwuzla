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

class TestSMTAxioms : public TestFile
{
 protected:
  void SetUp() override
  {
    TestFile::SetUp();
    d_check_log_file = false;
  }

  void run_smtaxioms_test(const std::string& s)
  {
    for (int32_t i = 1; i <= 8; i++)
    {
      run_smtaxioms_test_helper(s, i);
    }
    if (s != "bvsmod" && s != "bvsdiv" && s != "bvsrem")
    {
      run_smtaxioms_test_helper(s, 16);
      run_smtaxioms_test_helper(s, 32);
      run_smtaxioms_test_helper(s, 64);
    }
  }

 private:
  void run_smtaxioms_test_helper(const std::string& s, int32_t i)
  {
    std::stringstream ss_name;
    ss_name << "smtaxiom" << s << i;
    run_test(ss_name.str().c_str(), ".smt2", BZLA_RESULT_UNSAT);
    TearDown();
    SetUp();
  }
};

TEST_F(TestSMTAxioms, bvnand) { run_smtaxioms_test("bvnand"); }

TEST_F(TestSMTAxioms, bvnor) { run_smtaxioms_test("bvnor"); }

TEST_F(TestSMTAxioms, bvsge) { run_smtaxioms_test("bvsge"); }

TEST_F(TestSMTAxioms, bvsgt) { run_smtaxioms_test("bvsgt"); }

TEST_F(TestSMTAxioms, bvsle) { run_smtaxioms_test("bvsle"); }

TEST_F(TestSMTAxioms, bvslt) { run_smtaxioms_test("bvslt"); }

TEST_F(TestSMTAxioms, bvuge) { run_smtaxioms_test("bvuge"); }

TEST_F(TestSMTAxioms, bvugt) { run_smtaxioms_test("bvugt"); }

TEST_F(TestSMTAxioms, bvule) { run_smtaxioms_test("bvule"); }

TEST_F(TestSMTAxioms, bvxnor) { run_smtaxioms_test("bvxnor"); }

TEST_F(TestSMTAxioms, bvxor) { run_smtaxioms_test("bvxor"); }

TEST_F(TestSMTAxioms, bvsub) { run_smtaxioms_test("bvsub"); }

/* below are the 'hard' test cases (no 16, 32, 64 bits) */
TEST_F(TestSMTAxioms, bvsmod) { run_smtaxioms_test("bvsmod"); }

TEST_F(TestSMTAxioms, bvsdiv) { run_smtaxioms_test("bvsdiv"); }

TEST_F(TestSMTAxioms, bvsrem) { run_smtaxioms_test("bvsrem"); }
