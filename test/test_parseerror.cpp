/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2014-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "boolector.h"
}

class TestParseError : public TestFile
{
 protected:
  void SetUp() override
  {
    d_expect_parse_error = true;
    TestFile::SetUp();
  }

  void run_bzla_parse_error_test(const char *name)
  {
    boolector_set_opt(d_bzla, BZLA_OPT_INPUT_FORMAT, BZLA_INPUT_FORMAT_BTOR);
    run_test(name, ".btor", BOOLECTOR_UNKNOWN);
  }

  void run_smt_parse_error_test(const char *name)
  {
    boolector_set_opt(d_bzla, BZLA_OPT_INPUT_FORMAT, BZLA_INPUT_FORMAT_SMT2);
    run_test(name, ".smt2", BOOLECTOR_UNKNOWN);
  }
};

TEST_F(TestParseError, btorperr000)
{
  run_bzla_parse_error_test("btorperr000");
}

TEST_F(TestParseError, btorperr001)
{
  run_bzla_parse_error_test("btorperr001");
}

TEST_F(TestParseError, btorperr002)
{
  run_bzla_parse_error_test("btorperr002");
}

TEST_F(TestParseError, btorperr003)
{
  run_bzla_parse_error_test("btorperr003");
}

TEST_F(TestParseError, smt2perr000) { run_smt_parse_error_test("smt2perr000"); }

TEST_F(TestParseError, smt2perr001) { run_smt_parse_error_test("smt2perr001"); }

TEST_F(TestParseError, smt2perr002) { run_smt_parse_error_test("smt2perr002"); }

TEST_F(TestParseError, smt2perr003) { run_smt_parse_error_test("smt2perr003"); }

TEST_F(TestParseError, smt2perr004) { run_smt_parse_error_test("smt2perr004"); }

TEST_F(TestParseError, smt2perr005) { run_smt_parse_error_test("smt2perr005"); }

TEST_F(TestParseError, smt2perr006) { run_smt_parse_error_test("smt2perr006"); }

TEST_F(TestParseError, smt2perr007) { run_smt_parse_error_test("smt2perr007"); }

TEST_F(TestParseError, smt2perr008) { run_smt_parse_error_test("smt2perr008"); }

TEST_F(TestParseError, smt2perr009) { run_smt_parse_error_test("smt2perr009"); }

// no smt2perr010

TEST_F(TestParseError, smt2perr011) { run_smt_parse_error_test("smt2perr011"); }

TEST_F(TestParseError, smt2perr012) { run_smt_parse_error_test("smt2perr012"); }

TEST_F(TestParseError, smt2perr013) { run_smt_parse_error_test("smt2perr013"); }

TEST_F(TestParseError, smt2perr014) { run_smt_parse_error_test("smt2perr014"); }

TEST_F(TestParseError, smt2perr015) { run_smt_parse_error_test("smt2perr015"); }

TEST_F(TestParseError, smt2perr016) { run_smt_parse_error_test("smt2perr016"); }

TEST_F(TestParseError, smt2perr017) { run_smt_parse_error_test("smt2perr017"); }

TEST_F(TestParseError, smt2perr018) { run_smt_parse_error_test("smt2perr018"); }

TEST_F(TestParseError, smt2perr019) { run_smt_parse_error_test("smt2perr019"); }

TEST_F(TestParseError, smt2perr020) { run_smt_parse_error_test("smt2perr020"); }

TEST_F(TestParseError, smt2perr021) { run_smt_parse_error_test("smt2perr021"); }

TEST_F(TestParseError, smt2perr022) { run_smt_parse_error_test("smt2perr022"); }

TEST_F(TestParseError, smt2perr023) { run_smt_parse_error_test("smt2perr023"); }

TEST_F(TestParseError, smt2perr024) { run_smt_parse_error_test("smt2perr024"); }

TEST_F(TestParseError, smt2perr025) { run_smt_parse_error_test("smt2perr025"); }

TEST_F(TestParseError, smt2perr026) { run_smt_parse_error_test("smt2perr026"); }

TEST_F(TestParseError, smt2perr027) { run_smt_parse_error_test("smt2perr027"); }

TEST_F(TestParseError, smt2perr028) { run_smt_parse_error_test("smt2perr028"); }

TEST_F(TestParseError, smt2perr029) { run_smt_parse_error_test("smt2perr029"); }

TEST_F(TestParseError, smt2perr030) { run_smt_parse_error_test("smt2perr030"); }

TEST_F(TestParseError, smt2perr031) { run_smt_parse_error_test("smt2perr031"); }

TEST_F(TestParseError, smt2perr032) { run_smt_parse_error_test("smt2perr032"); }

TEST_F(TestParseError, smt2perr033) { run_smt_parse_error_test("smt2perr033"); }

TEST_F(TestParseError, smt2perr034) { run_smt_parse_error_test("smt2perr034"); }

TEST_F(TestParseError, smt2perr035) { run_smt_parse_error_test("smt2perr035"); }

TEST_F(TestParseError, smt2perr036) { run_smt_parse_error_test("smt2perr036"); }

TEST_F(TestParseError, smt2perr037) { run_smt_parse_error_test("smt2perr037"); }

TEST_F(TestParseError, smt2perr038) { run_smt_parse_error_test("smt2perr038"); }

TEST_F(TestParseError, smt2perr039) { run_smt_parse_error_test("smt2perr039"); }

TEST_F(TestParseError, smt2perr040) { run_smt_parse_error_test("smt2perr040"); }

TEST_F(TestParseError, smt2perr041) { run_smt_parse_error_test("smt2perr041"); }

TEST_F(TestParseError, smt2perr042) { run_smt_parse_error_test("smt2perr042"); }

TEST_F(TestParseError, smt2perr043) { run_smt_parse_error_test("smt2perr043"); }

TEST_F(TestParseError, smt2perr044) { run_smt_parse_error_test("smt2perr044"); }

TEST_F(TestParseError, smt2perr045) { run_smt_parse_error_test("smt2perr045"); }

TEST_F(TestParseError, smt2perr046) { run_smt_parse_error_test("smt2perr046"); }

TEST_F(TestParseError, smt2perr047) { run_smt_parse_error_test("smt2perr047"); }

TEST_F(TestParseError, smt2perr048) { run_smt_parse_error_test("smt2perr048"); }

TEST_F(TestParseError, smt2perr049) { run_smt_parse_error_test("smt2perr049"); }

TEST_F(TestParseError, smt2perr050) { run_smt_parse_error_test("smt2perr050"); }

TEST_F(TestParseError, smt2perr051) { run_smt_parse_error_test("smt2perr051"); }

TEST_F(TestParseError, smt2perr052) { run_smt_parse_error_test("smt2perr052"); }

TEST_F(TestParseError, smt2perr053) { run_smt_parse_error_test("smt2perr053"); }

TEST_F(TestParseError, smt2perr054) { run_smt_parse_error_test("smt2perr054"); }

TEST_F(TestParseError, smt2perr055) { run_smt_parse_error_test("smt2perr055"); }

TEST_F(TestParseError, smt2perr056) { run_smt_parse_error_test("smt2perr056"); }

TEST_F(TestParseError, smt2perr057) { run_smt_parse_error_test("smt2perr057"); }

TEST_F(TestParseError, smt2perr058) { run_smt_parse_error_test("smt2perr058"); }

TEST_F(TestParseError, smt2perr059) { run_smt_parse_error_test("smt2perr059"); }

TEST_F(TestParseError, smt2perr060) { run_smt_parse_error_test("smt2perr060"); }

TEST_F(TestParseError, smt2perr061) { run_smt_parse_error_test("smt2perr061"); }

TEST_F(TestParseError, smt2perr062) { run_smt_parse_error_test("smt2perr062"); }

TEST_F(TestParseError, smt2perr063) { run_smt_parse_error_test("smt2perr063"); }

TEST_F(TestParseError, smt2perr064) { run_smt_parse_error_test("smt2perr064"); }

TEST_F(TestParseError, smt2perr065) { run_smt_parse_error_test("smt2perr065"); }

TEST_F(TestParseError, smt2perr066) { run_smt_parse_error_test("smt2perr066"); }

TEST_F(TestParseError, smt2perr067) { run_smt_parse_error_test("smt2perr067"); }

TEST_F(TestParseError, smt2perr068) { run_smt_parse_error_test("smt2perr068"); }

TEST_F(TestParseError, smt2perr069) { run_smt_parse_error_test("smt2perr069"); }

TEST_F(TestParseError, smt2perr070) { run_smt_parse_error_test("smt2perr070"); }

TEST_F(TestParseError, smt2perr071) { run_smt_parse_error_test("smt2perr071"); }

TEST_F(TestParseError, smt2perr072) { run_smt_parse_error_test("smt2perr072"); }

TEST_F(TestParseError, smt2perr073) { run_smt_parse_error_test("smt2perr073"); }

TEST_F(TestParseError, smt2perr074) { run_smt_parse_error_test("smt2perr074"); }

TEST_F(TestParseError, smt2perr075) { run_smt_parse_error_test("smt2perr075"); }

TEST_F(TestParseError, smt2perr076) { run_smt_parse_error_test("smt2perr076"); }

TEST_F(TestParseError, smt2perr077) { run_smt_parse_error_test("smt2perr077"); }

TEST_F(TestParseError, smt2perr078) { run_smt_parse_error_test("smt2perr078"); }

TEST_F(TestParseError, smt2perr079) { run_smt_parse_error_test("smt2perr079"); }

TEST_F(TestParseError, smt2perr080) { run_smt_parse_error_test("smt2perr080"); }

TEST_F(TestParseError, smt2perr081) { run_smt_parse_error_test("smt2perr081"); }

TEST_F(TestParseError, smt2perr082) { run_smt_parse_error_test("smt2perr082"); }

TEST_F(TestParseError, smt2perr083) { run_smt_parse_error_test("smt2perr083"); }

TEST_F(TestParseError, smt2perr084) { run_smt_parse_error_test("smt2perr084"); }

TEST_F(TestParseError, smt2perr085) { run_smt_parse_error_test("smt2perr085"); }

TEST_F(TestParseError, smt2perr086) { run_smt_parse_error_test("smt2perr086"); }

TEST_F(TestParseError, smt2perr087) { run_smt_parse_error_test("smt2perr087"); }

TEST_F(TestParseError, smt2perr088) { run_smt_parse_error_test("smt2perr088"); }

TEST_F(TestParseError, smt2perr089) { run_smt_parse_error_test("smt2perr089"); }

TEST_F(TestParseError, smt2perr090) { run_smt_parse_error_test("smt2perr090"); }

TEST_F(TestParseError, smt2perr091) { run_smt_parse_error_test("smt2perr091"); }

TEST_F(TestParseError, smt2perr092) { run_smt_parse_error_test("smt2perr092"); }

TEST_F(TestParseError, smt2perr093) { run_smt_parse_error_test("smt2perr093"); }

TEST_F(TestParseError, smt2perr094) { run_smt_parse_error_test("smt2perr094"); }

TEST_F(TestParseError, smt2perr095) { run_smt_parse_error_test("smt2perr095"); }

TEST_F(TestParseError, smt2perr096) { run_smt_parse_error_test("smt2perr096"); }

TEST_F(TestParseError, smt2perr097) { run_smt_parse_error_test("smt2perr097"); }

TEST_F(TestParseError, smt2perr098) { run_smt_parse_error_test("smt2perr098"); }

TEST_F(TestParseError, smt2perr099) { run_smt_parse_error_test("smt2perr099"); }

TEST_F(TestParseError, smt2perr100) { run_smt_parse_error_test("smt2perr100"); }

TEST_F(TestParseError, smt2perr101) { run_smt_parse_error_test("smt2perr101"); }

TEST_F(TestParseError, smt2perr102) { run_smt_parse_error_test("smt2perr102"); }

TEST_F(TestParseError, smt2perr103) { run_smt_parse_error_test("smt2perr103"); }

TEST_F(TestParseError, smt2perr104) { run_smt_parse_error_test("smt2perr104"); }

TEST_F(TestParseError, smt2perr105) { run_smt_parse_error_test("smt2perr105"); }

TEST_F(TestParseError, smt2perr106) { run_smt_parse_error_test("smt2perr106"); }

TEST_F(TestParseError, smt2perr107) { run_smt_parse_error_test("smt2perr107"); }

TEST_F(TestParseError, smt2perr108) { run_smt_parse_error_test("smt2perr108"); }

TEST_F(TestParseError, smt2perr109) { run_smt_parse_error_test("smt2perr109"); }

TEST_F(TestParseError, smt2perr110) { run_smt_parse_error_test("smt2perr110"); }

TEST_F(TestParseError, smt2perr111) { run_smt_parse_error_test("smt2perr111"); }

TEST_F(TestParseError, smt2perr112) { run_smt_parse_error_test("smt2perr112"); }

TEST_F(TestParseError, smt2perr113) { run_smt_parse_error_test("smt2perr113"); }

TEST_F(TestParseError, smt2perr114) { run_smt_parse_error_test("smt2perr114"); }

TEST_F(TestParseError, smt2perr115) { run_smt_parse_error_test("smt2perr115"); }

TEST_F(TestParseError, smt2perr116) { run_smt_parse_error_test("smt2perr116"); }

TEST_F(TestParseError, smt2perr117) { run_smt_parse_error_test("smt2perr117"); }

TEST_F(TestParseError, smt2perr118) { run_smt_parse_error_test("smt2perr118"); }

TEST_F(TestParseError, smt2perr119) { run_smt_parse_error_test("smt2perr119"); }

TEST_F(TestParseError, smt2perr120) { run_smt_parse_error_test("smt2perr120"); }

TEST_F(TestParseError, smt2perr121) { run_smt_parse_error_test("smt2perr121"); }

TEST_F(TestParseError, smt2perr122) { run_smt_parse_error_test("smt2perr122"); }

TEST_F(TestParseError, smt2perr123) { run_smt_parse_error_test("smt2perr123"); }

TEST_F(TestParseError, smt2perr124) { run_smt_parse_error_test("smt2perr124"); }

TEST_F(TestParseError, smt2perr125) { run_smt_parse_error_test("smt2perr125"); }

TEST_F(TestParseError, smt2perr126) { run_smt_parse_error_test("smt2perr126"); }

TEST_F(TestParseError, smt2perr127) { run_smt_parse_error_test("smt2perr127"); }

TEST_F(TestParseError, smt2perr128) { run_smt_parse_error_test("smt2perr128"); }

TEST_F(TestParseError, smt2perr129) { run_smt_parse_error_test("smt2perr129"); }

TEST_F(TestParseError, smt2perr130) { run_smt_parse_error_test("smt2perr130"); }

TEST_F(TestParseError, smt2perr131) { run_smt_parse_error_test("smt2perr131"); }

TEST_F(TestParseError, smt2perr132) { run_smt_parse_error_test("smt2perr132"); }

TEST_F(TestParseError, smt2perr133) { run_smt_parse_error_test("smt2perr133"); }

TEST_F(TestParseError, smt2perr134) { run_smt_parse_error_test("smt2perr134"); }

TEST_F(TestParseError, smt2perr135) { run_smt_parse_error_test("smt2perr135"); }

TEST_F(TestParseError, smt2perr136) { run_smt_parse_error_test("smt2perr136"); }

TEST_F(TestParseError, smt2perr137) { run_smt_parse_error_test("smt2perr137"); }

TEST_F(TestParseError, smt2perr138) { run_smt_parse_error_test("smt2perr138"); }

TEST_F(TestParseError, smt2perr139) { run_smt_parse_error_test("smt2perr139"); }

TEST_F(TestParseError, smt2perr140) { run_smt_parse_error_test("smt2perr140"); }

TEST_F(TestParseError, smt2perr141) { run_smt_parse_error_test("smt2perr141"); }

TEST_F(TestParseError, smt2perr142) { run_smt_parse_error_test("smt2perr142"); }

TEST_F(TestParseError, smt2perr143) { run_smt_parse_error_test("smt2perr143"); }

TEST_F(TestParseError, smt2perr144) { run_smt_parse_error_test("smt2perr144"); }

TEST_F(TestParseError, smt2perr145) { run_smt_parse_error_test("smt2perr145"); }

TEST_F(TestParseError, smt2perr146) { run_smt_parse_error_test("smt2perr146"); }

TEST_F(TestParseError, smt2perr147) { run_smt_parse_error_test("smt2perr147"); }

TEST_F(TestParseError, smt2perr148) { run_smt_parse_error_test("smt2perr148"); }

TEST_F(TestParseError, smt2perr149) { run_smt_parse_error_test("smt2perr149"); }

TEST_F(TestParseError, smt2perr150) { run_smt_parse_error_test("smt2perr150"); }

TEST_F(TestParseError, smt2perr151) { run_smt_parse_error_test("smt2perr151"); }

TEST_F(TestParseError, smt2perr152) { run_smt_parse_error_test("smt2perr152"); }

TEST_F(TestParseError, smt2perr153) { run_smt_parse_error_test("smt2perr153"); }

// no smt2perr154

TEST_F(TestParseError, smt2perr155) { run_smt_parse_error_test("smt2perr155"); }

TEST_F(TestParseError, smt2perr156) { run_smt_parse_error_test("smt2perr156"); }

TEST_F(TestParseError, smt2perr157) { run_smt_parse_error_test("smt2perr157"); }

TEST_F(TestParseError, smt2perr158) { run_smt_parse_error_test("smt2perr158"); }

TEST_F(TestParseError, smt2perr159) { run_smt_parse_error_test("smt2perr159"); }

TEST_F(TestParseError, smt2perr160) { run_smt_parse_error_test("smt2perr160"); }

TEST_F(TestParseError, smt2perr161) { run_smt_parse_error_test("smt2perr161"); }

TEST_F(TestParseError, smt2perr162) { run_smt_parse_error_test("smt2perr162"); }

TEST_F(TestParseError, smt2perr163) { run_smt_parse_error_test("smt2perr163"); }

TEST_F(TestParseError, smt2perr164) { run_smt_parse_error_test("smt2perr164"); }

TEST_F(TestParseError, smt2perr173) { run_smt_parse_error_test("smt2perr173"); }
