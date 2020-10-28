/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

class TestApi : public TestBitwuzla
{
};

TEST_F(TestApi, term_fun_get_domain_sorts)
{
  BitwuzlaSort bv_sort32 = bitwuzla_mk_bv_sort(d_bzla, 32);
  BitwuzlaSort bv_sort8  = bitwuzla_mk_bv_sort(d_bzla, 8);
  BitwuzlaTerm *bv_term  = bitwuzla_mk_const(d_bzla, bv_sort32, "bv");

  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(nullptr), "must not be NULL");
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sort(bv_term),
               "expected function term");

  BitwuzlaSort array_sort = bitwuzla_mk_array_sort(d_bzla, bv_sort32, bv_sort8);
  BitwuzlaTerm *array_term   = bitwuzla_mk_const(d_bzla, array_sort, "array");
  const BitwuzlaSort *isorts = bitwuzla_term_fun_get_domain_sorts(array_term);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, isorts[0]));
  ASSERT_EQ(isorts[1], (BitwuzlaSort) 0);

  BitwuzlaSort domain[]  = {bv_sort32, bv_sort8, bv_sort32};
  BitwuzlaSort fun_sort  = bitwuzla_mk_fun_sort(d_bzla, 3, domain, bv_sort8);
  BitwuzlaTerm *fun_term = bitwuzla_mk_const(d_bzla, fun_sort, "fun");
  const BitwuzlaSort *dsorts = bitwuzla_term_fun_get_domain_sorts(fun_term);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, dsorts[0]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort8, dsorts[1]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, bv_sort32, dsorts[2]));
  ASSERT_EQ(dsorts[3], (BitwuzlaSort) 0);
}

TEST_F(TestApi, mk_term)
{
  const char *error_not_null  = "must not be NULL";
  const char *error_arg_cnt   = "invalid number of arguments";
  const char *error_inv_sort  = "unexpected sort";
  const char *error_mis_sort  = "mismatching sort";
  const char *error_rm_sort   = "expected rounding-mode term";
  const char *error_b_sort    = "expected boolean term";
  const char *error_var_sort  = "expected variable term";
  const char *error_bvar_term = "expected unbound variable term";
  const char *error_fun_term  = "unexpected function term";

  BitwuzlaSort bv_sort1  = bitwuzla_mk_bv_sort(d_bzla, 1);
  BitwuzlaSort bv_sort23 = bitwuzla_mk_bv_sort(d_bzla, 23);
  BitwuzlaSort bv_sort8  = bitwuzla_mk_bv_sort(d_bzla, 8);
  BitwuzlaSort fp_sort16 = bitwuzla_mk_fp_sort(d_bzla, 5, 11);
  BitwuzlaSort fp_sort32 = bitwuzla_mk_fp_sort(d_bzla, 8, 24);
  BitwuzlaSort rm_sort   = bitwuzla_mk_rm_sort(d_bzla);

  BitwuzlaSort arr_sort = bitwuzla_mk_array_sort(d_bzla, fp_sort16, bv_sort8);
  std::vector<BitwuzlaSort> domain = {bv_sort8, fp_sort16};
  BitwuzlaSort fun_sort =
      bitwuzla_mk_fun_sort(d_bzla, domain.size(), domain.data(), bv_sort8);

  BitwuzlaTerm *ttrue    = bitwuzla_mk_true(d_bzla);
  BitwuzlaTerm *bv_one   = bitwuzla_mk_bv_one(d_bzla, bv_sort1);
  BitwuzlaTerm *bv_ones  = bitwuzla_mk_bv_one(d_bzla, bv_sort23);
  BitwuzlaTerm *bv_zero  = bitwuzla_mk_bv_zero(d_bzla, bv_sort8);
  BitwuzlaTerm *fp_pzero = bitwuzla_mk_fp_pos_zero(d_bzla, fp_sort32);

  BitwuzlaTerm *bv_const = bitwuzla_mk_const(d_bzla, bv_sort8, "bv_const");
  BitwuzlaTerm *fp_const = bitwuzla_mk_const(d_bzla, fp_sort16, "fp_const");
  BitwuzlaTerm *rm_const = bitwuzla_mk_const(d_bzla, rm_sort, "rm_const");
  BitwuzlaTerm *fun      = bitwuzla_mk_const(d_bzla, fun_sort, "fun");
  BitwuzlaTerm *array    = bitwuzla_mk_const(d_bzla, arr_sort, "array");
  BitwuzlaTerm *var      = bitwuzla_mk_var(d_bzla, bv_sort8, "var");
  BitwuzlaTerm *bvar     = bitwuzla_mk_var(d_bzla, bv_sort8, "bvar");

  BitwuzlaTerm *body =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_ADD, bvar, bv_const);
  BitwuzlaTerm *lambda =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_LAMBDA, bvar, body);

  std::vector<BitwuzlaTerm *> b_args1     = {ttrue};
  std::vector<BitwuzlaTerm *> b_args2     = {ttrue, ttrue};
  std::vector<BitwuzlaTerm *> bv_args1    = {bv_one};
  std::vector<BitwuzlaTerm *> bv_args2    = {bv_zero, bv_const};
  std::vector<BitwuzlaTerm *> fp_args2    = {fp_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_args2_rm = {rm_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_args3    = {rm_const, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> ite_args    = {ttrue, bv_const, bv_const};

  std::vector<BitwuzlaTerm *> app_argsd1    = {bv_one};
  std::vector<BitwuzlaTerm *> app_argsd2    = {bv_const, fun, fun};
  std::vector<BitwuzlaTerm *> argsd1        = {nullptr};
  std::vector<BitwuzlaTerm *> argsd2        = {bv_zero, nullptr};
  std::vector<BitwuzlaTerm *> argsd3        = {rm_const, nullptr, fp_const};
  std::vector<BitwuzlaTerm *> arr_argsd1    = {array};
  std::vector<BitwuzlaTerm *> arr_argsd2_1  = {fp_const, array};
  std::vector<BitwuzlaTerm *> arr_argsd2_2  = {array, bv_const};
  std::vector<BitwuzlaTerm *> arr_argsd3_1  = {fp_const, array, bv_const};
  std::vector<BitwuzlaTerm *> arr_argsd3_2  = {array, bv_const, bv_const};
  std::vector<BitwuzlaTerm *> arr_argsd3_3  = {array, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> b_argsd2      = {ttrue, bv_const};
  std::vector<BitwuzlaTerm *> bv_argsd2     = {bv_one, bv_const};
  std::vector<BitwuzlaTerm *> fp_argsd1     = {rm_const};
  std::vector<BitwuzlaTerm *> fp_argsd2     = {fp_pzero, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd2_inv = {rm_const, bv_const};
  std::vector<BitwuzlaTerm *> fp_argsd3     = {rm_const, fp_pzero, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd3_inv = {rm_const, bv_zero, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd3_rm  = {fp_const, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd4     = {
      rm_const, fp_pzero, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd4_inv = {
      rm_const, bv_zero, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_argsd4_rm = {
      fp_const, fp_const, fp_const, fp_const};
  std::vector<BitwuzlaTerm *> fp_fp_argsd3_1 = {bv_const, bv_zero, bv_ones};
  std::vector<BitwuzlaTerm *> fp_fp_argsd3_2 = {bv_one, fp_pzero, bv_ones};
  std::vector<BitwuzlaTerm *> fp_fp_argsd3_3 = {bv_one, bv_zero, fp_pzero};
  std::vector<BitwuzlaTerm *> fp_fp_argsd3_4 = {fp_pzero, bv_zero, bv_ones};
  std::vector<BitwuzlaTerm *> fun_argsd1     = {var};
  std::vector<BitwuzlaTerm *> ite_argsd2     = {ttrue, bv_const};
  std::vector<BitwuzlaTerm *> ite_argsd3_1   = {ttrue, bv_const, bv_one};
  std::vector<BitwuzlaTerm *> ite_argsd3_2   = {bv_const, bv_const, bv_const};
  std::vector<BitwuzlaTerm *> lam_argsd2_1   = {bvar, bv_const};
  std::vector<BitwuzlaTerm *> lam_argsd2_2   = {var, fun};
  std::vector<BitwuzlaTerm *> q_argsd2_1     = {ttrue, ttrue};
  std::vector<BitwuzlaTerm *> q_argsd2_2     = {var, bv_const};

  std::vector<uint32_t> idxs1    = {1};
  std::vector<uint32_t> idxs2    = {2, 0};
  std::vector<uint32_t> fp_idxs2 = {5, 8};
  std::vector<uint32_t> idxsd2_1 = {0, 2};
  std::vector<uint32_t> idxsd2_2 = {9, 0};

  /* null checks ------------------------------------------------------------ */
  ASSERT_DEATH(
      bitwuzla_mk_term(
          nullptr, BITWUZLA_KIND_BV_AND, bv_args2.size(), bv_args2.data()),
      error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_AND, bv_args2.size(), argsd2.data()),
      error_not_null);

  ASSERT_DEATH(bitwuzla_mk_term1(nullptr, BITWUZLA_KIND_BV_NOT, bv_one),
               error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, nullptr),
               error_not_null);

  ASSERT_DEATH(
      bitwuzla_mk_term2(nullptr, BITWUZLA_KIND_BV_AND, bv_zero, bv_const),
      error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_AND, nullptr, bv_const),
      error_not_null);

  ASSERT_DEATH(bitwuzla_mk_term3(
                   nullptr, BITWUZLA_KIND_FP_ADD, rm_const, fp_const, fp_const),
               error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term3(
                   d_bzla, BITWUZLA_KIND_FP_ADD, nullptr, fp_const, fp_const),
               error_not_null);

  /* number of args checks -------------------------------------------------- */
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_AND, b_args1.size(), b_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_APPLY, app_argsd1.size(), app_argsd1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                arr_argsd1.size(),
                                arr_argsd1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                arr_argsd1.size(),
                                arr_argsd1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ADD, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_AND, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ASHR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_CONCAT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_DEC, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_INC, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_MUL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NAND, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NEG, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NOT, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDAND, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDOR, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDXOR, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SDIV, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SMOD, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SREM, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SUB, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UDIV, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UREM, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XNOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_DISTINCT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_EQUAL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_EXISTS, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FORALL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_ABS, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_ADD, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_DIV, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_EQ, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_FMA, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_FP, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GEQ, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GT, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_INF, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NAN, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NEG, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NORMAL, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_POS, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_SUBNORMAL,
                                fp_args2.size(),
                                fp_args2.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_ZERO, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LEQ, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LT, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MAX, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MIN, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_ZERO, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MUL, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_REM, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_RTI, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SQRT, fp_args3.size(), fp_args3.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SUB, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_IFF, b_args1.size(), b_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IMPLIES, b_args1.size(), b_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_ITE, ite_argsd2.size(), ite_argsd2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_LAMBDA, fun_argsd1.size(), fun_argsd1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_NOT, b_args2.size(), b_args2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_OR, b_args1.size(), b_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_XOR, b_args1.size(), b_args1.data()),
               error_arg_cnt);
  // indexed
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs2.size(),
                                        idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_REPEAT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_ROLI,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_RORI,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args3.size(),
                                        fp_args3.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_INT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_argsd1.size(),
                                        fp_argsd1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_argsd1.size(),
                                        fp_argsd1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);

  /* sort (and more) checks ------------------------------------------------- */
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_AND, bv_args2.size(), bv_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_AND, b_argsd2.size(), b_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_APPLY, app_argsd2.size(), app_argsd2.data()),
      error_fun_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                arr_argsd2_1.size(),
                                arr_argsd2_1.data()),
               "expected array term");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                arr_argsd2_2.size(),
                                arr_argsd2_2.data()),
               "sort of index term does not match index sort of array");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                arr_argsd3_1.size(),
                                arr_argsd3_1.data()),
               "expected array term");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                arr_argsd3_2.size(),
                                arr_argsd3_2.data()),
               "sort of index term does not match index sort of array");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                arr_argsd3_3.size(),
                                arr_argsd3_3.data()),
               "sort of element term does not match element sort of array");
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ADD, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ADD, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_AND, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_AND, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ASHR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ASHR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_DEC, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_INC, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_MUL, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_MUL, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NAND, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NAND, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NEG, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NOR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NOR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_NOT, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDAND, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDOR, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_REDXOR, fp_argsd1.size(), fp_argsd1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_OR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROL, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROL, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ROR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SDIV, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SDIV, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGE, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGE, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGT, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SGT, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHL, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHL, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SHR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLE, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLE, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLT, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SLT, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SMOD, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SMOD, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SREM, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SREM, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SUB, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_SUB, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UDIV, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UDIV, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGE, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGE, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGT, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UGT, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULE, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULE, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULT, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_ULT, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UREM, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_UREM, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                fp_args2.size(),
                                fp_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_argsd2.size(),
                                bv_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XNOR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XNOR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XOR, fp_args2.size(), fp_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_BV_XOR, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_DISTINCT, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_EQUAL, bv_argsd2.size(), bv_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_EXISTS, q_argsd2_1.size(), q_argsd2_1.data()),
      error_var_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_EXISTS, q_argsd2_2.size(), q_argsd2_2.data()),
      error_b_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FORALL, q_argsd2_1.size(), q_argsd2_1.data()),
      error_var_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FORALL, q_argsd2_2.size(), q_argsd2_2.data()),
      error_b_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_ABS, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                fp_argsd3_inv.size(),
                                fp_argsd3_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                fp_argsd3_rm.size(),
                                fp_argsd3_rm.data()),
               error_rm_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_ADD, fp_argsd3.size(), fp_argsd3.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_DIV,
                                fp_argsd3_inv.size(),
                                fp_argsd3_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_DIV,
                                fp_argsd3_rm.size(),
                                fp_argsd3_rm.data()),
               error_rm_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_DIV, fp_argsd3.size(), fp_argsd3.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_EQ, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_EQ, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FMA,
                                fp_argsd4_inv.size(),
                                fp_argsd4_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FMA,
                                fp_argsd4_rm.size(),
                                fp_argsd4_rm.data()),
               error_rm_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_FMA, fp_argsd4.size(), fp_argsd4.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_argsd3_1.size(),
                                fp_fp_argsd3_1.data()),
               "invalid bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_argsd3_2.size(),
                                fp_fp_argsd3_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_argsd3_3.size(),
                                fp_fp_argsd3_3.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_argsd3_4.size(),
                                fp_fp_argsd3_4.data()),
               error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GEQ, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GEQ, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GT, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GT, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_INF, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NAN, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NEG, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_NORMAL, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_POS, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_SUBNORMAL,
                                bv_args1.size(),
                                bv_args1.data()),
               error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_ZERO, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LEQ, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LEQ, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LT, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LT, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MAX, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MAX, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MIN, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MIN, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_IS_ZERO, bv_args1.size(), bv_args1.data()),
      error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MUL,
                                fp_argsd3_inv.size(),
                                fp_argsd3_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MUL,
                                fp_argsd3_rm.size(),
                                fp_argsd3_rm.data()),
               error_rm_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MUL, fp_argsd3.size(), fp_argsd3.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_REM, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_REM, fp_argsd2.size(), fp_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_RTI, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_RTI, fp_argsd2.size(), fp_argsd2.data()),
      error_rm_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_argsd2_inv.size(),
                                fp_argsd2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SQRT, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SQRT, fp_argsd2.size(), fp_argsd2.data()),
      error_rm_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_argsd2_inv.size(),
                                fp_argsd2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SUB,
                                fp_argsd3_inv.size(),
                                fp_argsd3_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SUB,
                                fp_argsd3_rm.size(),
                                fp_argsd3_rm.data()),
               error_rm_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SUB, fp_argsd3.size(), fp_argsd3.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_IFF, bv_args2.size(), bv_args2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_bzla, BITWUZLA_KIND_IFF, b_argsd2.size(), b_argsd2.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IMPLIES, bv_args2.size(), bv_args2.data()),
      error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IMPLIES, b_argsd2.size(), b_argsd2.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_ITE, ite_argsd3_2.size(), ite_argsd3_2.data()),
      error_b_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_ITE, ite_argsd3_1.size(), ite_argsd3_1.data()),
      error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_LAMBDA, bv_args2.size(), bv_args2.data()),
      error_var_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lam_argsd2_1.size(),
                                lam_argsd2_1.data()),
               error_bvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lam_argsd2_2.size(),
                                lam_argsd2_2.data()),
               error_fun_term);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term (
  //          d_bzla, BITWUZLA_KIND_NOT, b_args2.size (), b_args2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (bitwuzla_mk_term (
  //                    d_bzla, BITWUZLA_KIND_OR, b_args1.size (), b_args1.data
  //                    ()),
  //                inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term (
  //          d_bzla, BITWUZLA_KIND_XOR, b_args1.size (), b_args1.data ()),
  //      inv_sort);
  //  // indexed
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_EXTRACT, bv_args2.size (), bv_args2.data
  //          (),
  //      idxs2.size (),
  //      idxs2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_REPEAT, bv_args2.size (), bv_args2.data
  //          (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_ROLI, bv_args2.size (), bv_args2.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_RORI, bv_args2.size (), bv_args2.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_SIGN_EXTEND, bv_args2.size (),
  //          bv_args2.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_BV_ZERO_EXTEND, bv_args2.size (),
  //          bv_args2.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_FP_FROM_BV, bv_args2.size (),
  //          bv_args2.data (),
  //      fp_idxs2.size (),
  //      fp_idxs2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_FP_FROM_FP, fp_args3.size (),
  //          fp_args3.data (),
  //      fp_idxs2.size (),
  //      fp_idxs2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_FP_FROM_INT, bv_args2.size (),
  //          bv_args2.data (),
  //      fp_idxs2.size (),
  //      fp_idxs2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_FP_FROM_UINT, bv_args2.size (),
  //          bv_args2.data (),
  //      fp_idxs2.size (),
  //      fp_idxs2.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_SBV, fp_argsd1_rm.size (),
  //          fp_argsd1_rm.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
  //  ASSERT_DEATH (
  //      bitwuzla_mk_term_indexed (
  //          d_bzla, BITWUZLA_KIND_FP_TO_UBV, fp_argsd1_rm.size (),
  //          fp_argsd1_rm.data (),
  //      idxs1.size (),
  //      idxs1.data ()),
  //      inv_sort);
}
