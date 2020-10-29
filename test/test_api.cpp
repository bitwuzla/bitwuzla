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
 protected:
  void SetUp() override
  {
    TestBitwuzla::SetUp();
    d_bv_sort1  = bitwuzla_mk_bv_sort(d_bzla, 1);
    d_bv_sort8  = bitwuzla_mk_bv_sort(d_bzla, 8);
    d_bv_sort23 = bitwuzla_mk_bv_sort(d_bzla, 23);
    d_bv_sort32 = bitwuzla_mk_bv_sort(d_bzla, 32);

    d_fp_sort16 = bitwuzla_mk_fp_sort(d_bzla, 5, 11);
    d_fp_sort32 = bitwuzla_mk_fp_sort(d_bzla, 8, 24);
    d_rm_sort   = bitwuzla_mk_rm_sort(d_bzla);

    d_arr_sort_fpbv = bitwuzla_mk_array_sort(d_bzla, d_fp_sort16, d_bv_sort8);
    d_array_sort_bv = bitwuzla_mk_array_sort(d_bzla, d_bv_sort32, d_bv_sort8);

    d_fun_domain_sort = {d_bv_sort8, d_fp_sort16, d_bv_sort32};
    d_fun_sort        = bitwuzla_mk_fun_sort(
        d_bzla, d_fun_domain_sort.size(), d_fun_domain_sort.data(), d_bv_sort8);
    d_true       = bitwuzla_mk_true(d_bzla);
    d_bv_one1    = bitwuzla_mk_bv_one(d_bzla, d_bv_sort1);
    d_bv_ones23  = bitwuzla_mk_bv_one(d_bzla, d_bv_sort23);
    d_bv_zero8   = bitwuzla_mk_bv_zero(d_bzla, d_bv_sort8);
    d_fp_pzero32 = bitwuzla_mk_fp_pos_zero(d_bzla, d_fp_sort32);

    d_bv_const8  = bitwuzla_mk_const(d_bzla, d_bv_sort8, "bv_const");
    d_fp_const16 = bitwuzla_mk_const(d_bzla, d_fp_sort16, "fp_const");
    d_rm_const   = bitwuzla_mk_const(d_bzla, d_rm_sort, "rm_const");
    d_fun        = bitwuzla_mk_const(d_bzla, d_fun_sort, "fun");
    d_array_fpbv = bitwuzla_mk_const(d_bzla, d_arr_sort_fpbv, "array_fpbv");
    d_array      = bitwuzla_mk_const(d_bzla, d_array_sort_bv, "array");
    d_var        = bitwuzla_mk_var(d_bzla, d_bv_sort8, "var");
    d_bvar       = bitwuzla_mk_var(d_bzla, d_bv_sort8, "bvar");

    d_lambda_body =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_ADD, d_bvar, d_bv_const8);
    d_lambda =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_LAMBDA, d_bvar, d_lambda_body);
  }

  /* sorts */
  BitwuzlaSort d_bv_sort1;
  BitwuzlaSort d_bv_sort8;
  BitwuzlaSort d_bv_sort23;
  BitwuzlaSort d_bv_sort32;

  BitwuzlaSort d_fp_sort16;
  BitwuzlaSort d_fp_sort32;
  BitwuzlaSort d_rm_sort;

  BitwuzlaSort d_arr_sort_fpbv;
  BitwuzlaSort d_array_sort_bv;

  std::vector<BitwuzlaSort> d_fun_domain_sort;
  BitwuzlaSort d_fun_sort;

  /* terms */
  BitwuzlaTerm *d_true;
  BitwuzlaTerm *d_bv_one1;
  BitwuzlaTerm *d_bv_ones23;
  BitwuzlaTerm *d_bv_zero8;
  BitwuzlaTerm *d_fp_pzero32;

  BitwuzlaTerm *d_bv_const8;
  BitwuzlaTerm *d_fp_const16;
  BitwuzlaTerm *d_rm_const;
  BitwuzlaTerm *d_fun;
  BitwuzlaTerm *d_array_fpbv;
  BitwuzlaTerm *d_array;
  BitwuzlaTerm *d_var;
  BitwuzlaTerm *d_bvar;

  BitwuzlaTerm *d_lambda_body;
  BitwuzlaTerm *d_lambda;
};

TEST_F(TestApi, term_fun_get_domain_sorts)
{
  BitwuzlaTerm *bv_term = bitwuzla_mk_const(d_bzla, d_bv_sort32, "bv");

  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(nullptr), "must not be NULL");
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sort(bv_term),
               "expected function term");

  const BitwuzlaSort *index_sorts = bitwuzla_term_fun_get_domain_sorts(d_array);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, d_bv_sort32, index_sorts[0]));
  ASSERT_EQ(index_sorts[1], (BitwuzlaSort) 0);

  const BitwuzlaSort *domain_sorts = bitwuzla_term_fun_get_domain_sorts(d_fun);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, d_bv_sort8, domain_sorts[0]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, d_fp_sort16, domain_sorts[1]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bzla, d_bv_sort32, domain_sorts[2]));
  ASSERT_EQ(domain_sorts[3], (BitwuzlaSort) 0);
}

TEST_F(TestApi, mk_term_check_null)
{
  const char *error_not_null = "must not be NULL";

  std::vector<BitwuzlaTerm *> bv_args2 = {d_bv_zero8, d_bv_const8};

  std::vector<BitwuzlaTerm *> null_death_args1 = {nullptr};
  std::vector<BitwuzlaTerm *> null_death_args2 = {d_bv_zero8, nullptr};
  std::vector<BitwuzlaTerm *> null_death_args3 = {
      d_rm_const, nullptr, d_fp_const16};

  // mk_term
  ASSERT_DEATH(
      bitwuzla_mk_term(
          nullptr, BITWUZLA_KIND_BV_AND, bv_args2.size(), bv_args2.data()),
      error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NOT,
                                null_death_args1.size(),
                                null_death_args1.data()),
               error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_AND,
                                null_death_args2.size(),
                                null_death_args2.data()),
               error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                null_death_args3.size(),
                                null_death_args3.data()),
               error_not_null);
  // mk_term1
  ASSERT_DEATH(bitwuzla_mk_term1(nullptr, BITWUZLA_KIND_BV_NOT, d_bv_one1),
               error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, nullptr),
               error_not_null);
  // mk_term2
  ASSERT_DEATH(
      bitwuzla_mk_term2(nullptr, BITWUZLA_KIND_BV_AND, d_bv_zero8, d_bv_const8),
      error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_AND, nullptr, d_bv_const8),
      error_not_null);
  // mk_term3
  ASSERT_DEATH(bitwuzla_mk_term3(nullptr,
                                 BITWUZLA_KIND_FP_ADD,
                                 d_rm_const,
                                 d_fp_const16,
                                 d_fp_const16),
               error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term3(
          d_bzla, BITWUZLA_KIND_FP_ADD, nullptr, d_fp_const16, d_fp_const16),
      error_not_null);
}

TEST_F(TestApi, mk_term_check_cnt)
{
  const char *error_arg_cnt = "invalid number of arguments";

  std::vector<BitwuzlaTerm *> apply_args1 = {d_bv_one1};
  std::vector<BitwuzlaTerm *> apply_args2 = {d_bv_const8, d_fun};
  std::vector<BitwuzlaTerm *> array_args1 = {d_array_fpbv};
  std::vector<BitwuzlaTerm *> bool_args1  = {d_true};
  std::vector<BitwuzlaTerm *> bool_args2  = {d_true, d_true};
  std::vector<BitwuzlaTerm *> bv_args1    = {d_bv_one1};
  std::vector<BitwuzlaTerm *> bv_args1_rm = {d_rm_const};
  std::vector<BitwuzlaTerm *> bv_args2    = {d_bv_zero8, d_bv_const8};
  std::vector<BitwuzlaTerm *> ite_args2   = {d_true, d_bv_const8};
  std::vector<BitwuzlaTerm *> fp_args1    = {d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args2    = {d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args2_rm = {d_rm_const, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args3_rm = {
      d_rm_const, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> fun_args1 = {d_var};

  std::vector<uint32_t> idxs1    = {1};
  std::vector<uint32_t> idxs2    = {2, 0};
  std::vector<uint32_t> fp_idxs2 = {5, 8};

  // bool
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_AND, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IFF, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IMPLIES, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_NOT, bool_args2.size(), bool_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_OR, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_XOR, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);

  // bit-vectors
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_APPLY, apply_args1.size(), apply_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_APPLY, apply_args2.size(), apply_args2.data()),
      "number of given arguments to function must match arity of function");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_args1.size(),
                                array_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_args1.size(),
                                array_args1.data()),
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

  // floating-point
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
          d_bzla, BITWUZLA_KIND_FP_EQ, fp_args3_rm.size(), fp_args3_rm.data()),
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
          d_bzla, BITWUZLA_KIND_FP_GEQ, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GT, fp_args3_rm.size(), fp_args3_rm.data()),
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
          d_bzla, BITWUZLA_KIND_FP_LEQ, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LT, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MAX, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_MIN, fp_args3_rm.size(), fp_args3_rm.data()),
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
          d_bzla, BITWUZLA_KIND_FP_REM, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_RTI, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args3_rm.size(),
                                fp_args3_rm.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_SUB, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);

  // others
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
          d_bzla, BITWUZLA_KIND_ITE, ite_args2.size(), ite_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_LAMBDA, fun_args1.size(), fun_args1.data()),
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
                                        fp_args3_rm.size(),
                                        fp_args3_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_INT,
                                        bv_args1_rm.size(),
                                        bv_args1_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
                                        bv_args1_rm.size(),
                                        bv_args1_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args1.size(),
                                        fp_args1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args1.size(),
                                        fp_args1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
}

TEST_F(TestApi, mk_term_check_args)
{
  const char *error_inv_sort  = "unexpected sort";
  const char *error_mis_sort  = "mismatching sort";
  const char *error_rm_term   = "expected rounding-mode term";
  const char *error_arr_term  = "expected array term";
  const char *error_bool_term = "expected boolean term";
  const char *error_bvar_term = "expected unbound variable term";
  const char *error_dvar_term = "given variables are not distinct";
  const char *error_fun_term  = "unexpected function term";
  const char *error_var_term  = "expected variable term";

  const char *error_arr_index_sort =
      "sort of index term does not match index sort of array";
  const char *error_arr_element_sort =
      "sort of element term does not match element sort of array";

  std::vector<BitwuzlaTerm *> array_select_args2_inv_1 = {d_fp_const16,
                                                          d_array_fpbv};
  std::vector<BitwuzlaTerm *> array_select_args2_inv_2 = {d_array_fpbv,
                                                          d_bv_const8};

  std::vector<BitwuzlaTerm *> array_store_args3_inv_1 = {
      d_fp_const16, d_array_fpbv, d_bv_const8};
  std::vector<BitwuzlaTerm *> array_store_args3_inv_2 = {
      d_array_fpbv, d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm *> array_store_args3_inv_3 = {
      d_array_fpbv, d_fp_const16, d_fp_const16};

  std::vector<BitwuzlaTerm *> apply_args3_inv_1 = {d_bv_const8, d_fun, d_fun};
  std::vector<BitwuzlaTerm *> apply_args3_inv_2 = {
      d_bv_const8, d_bv_const8, d_fp_pzero32, d_fun};

  std::vector<BitwuzlaTerm *> bool_args1_inv = {d_bv_const8};
  std::vector<BitwuzlaTerm *> bool_args2_inv = {d_fp_pzero32, d_fp_pzero32};
  std::vector<BitwuzlaTerm *> bool_args2_mis = {d_true, d_bv_const8};

  std::vector<BitwuzlaTerm *> bv_args1          = {d_bv_const8};
  std::vector<BitwuzlaTerm *> bv_args1_inv      = {d_fp_const16};
  std::vector<BitwuzlaTerm *> bv_args2_inv      = {d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> bv_args2_mis      = {d_bv_one1, d_bv_const8};
  std::vector<BitwuzlaTerm *> bv_args2_rm_inv_1 = {d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm *> bv_args2_rm_inv_2 = {d_rm_const, d_fp_const16};

  std::vector<BitwuzlaTerm *> ite_death_args3_1 = {
      d_true, d_bv_const8, d_bv_one1};
  std::vector<BitwuzlaTerm *> ite_args3_inv_2 = {
      d_bv_const8, d_bv_const8, d_bv_const8};

  std::vector<BitwuzlaTerm *> lambda_args2_inv_1 = {d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm *> lambda_args2_inv_2 = {d_bvar, d_bv_const8};
  std::vector<BitwuzlaTerm *> lambda_args2_inv_3 = {d_var, d_fun};
  std::vector<BitwuzlaTerm *> lambda_args3_inv   = {d_var, d_var, d_bv_const8};

  std::vector<BitwuzlaTerm *> fp_args1_inv      = {d_bv_one1};
  std::vector<BitwuzlaTerm *> fp_args2_inv      = {d_bv_zero8, d_bv_const8};
  std::vector<BitwuzlaTerm *> fp_args2_mis      = {d_fp_pzero32, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args2_rm_inv_1 = {d_bv_const8, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args2_rm_inv_2 = {d_rm_const, d_bv_const8};
  std::vector<BitwuzlaTerm *> fp_args3_rm_mis   = {
      d_rm_const, d_fp_pzero32, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args3_rm_inv_1 = {
      d_fp_const16, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args3_rm_inv_2 = {
      d_rm_const, d_bv_zero8, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args4_mis = {
      d_rm_const, d_fp_pzero32, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args4_rm_inv_1 = {
      d_rm_const, d_bv_zero8, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm *> fp_args4_rm_inv_2 = {
      d_fp_const16, d_fp_const16, d_fp_const16, d_fp_const16};

  std::vector<BitwuzlaTerm *> fp_fp_args3_inv_1 = {
      d_bv_const8, d_bv_zero8, d_bv_ones23};
  std::vector<BitwuzlaTerm *> fp_fp_args3_inv_2 = {
      d_bv_one1, d_fp_pzero32, d_bv_ones23};
  std::vector<BitwuzlaTerm *> fp_fp_args3_inv_3 = {
      d_bv_one1, d_bv_zero8, d_fp_pzero32};
  std::vector<BitwuzlaTerm *> fp_fp_args3_inv_4 = {
      d_fp_pzero32, d_bv_zero8, d_bv_ones23};

  std::vector<BitwuzlaTerm *> quant_args2_inv_1 = {d_true, d_true};
  std::vector<BitwuzlaTerm *> quant_args2_inv_2 = {d_var, d_bv_const8};
  std::vector<BitwuzlaTerm *> quant_args2_inv_3 = {d_bvar, d_bv_const8};
  std::vector<BitwuzlaTerm *> quant_args3_inv   = {d_var, d_var, d_bv_const8};

  std::vector<uint32_t> bv_idxs1                 = {3};
  std::vector<uint32_t> bv_idxs2                 = {2, 0};
  std::vector<uint32_t> bv_extract_death_idxs2_1 = {0, 2};
  std::vector<uint32_t> bv_extract_death_idxs2_2 = {9, 0};
  std::vector<uint32_t> bv_repeat_death_idxs1    = {536870913};
  std::vector<uint32_t> bv_extend_death_idxs1    = {UINT32_MAX};
  std::vector<uint32_t> fp_idxs2                 = {5, 8};

  // bool
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_AND,
                                bool_args2_inv.size(),
                                bool_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_AND,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_IFF, fp_args2_inv.size(), fp_args2_inv.data()),
      error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_IFF,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_IMPLIES,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_IMPLIES,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_NOT,
                                bool_args1_inv.size(),
                                bool_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_OR,
                                bool_args2_inv.size(),
                                bool_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_XOR,
                                bool_args2_inv.size(),
                                bool_args2_inv.data()),
               error_inv_sort);
  // bit-vectors
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ADD,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ADD,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_AND,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_AND,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ASHR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ASHR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_DEC,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_INC,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_MUL,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_MUL,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NAND,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NAND,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NEG,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NOR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NOR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NOT,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_REDAND,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_REDOR,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_REDXOR,
                                bv_args1_inv.size(),
                                bv_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ROL,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ROL,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ROR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ROR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SDIV,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SGE,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SGE,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SGT,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SGT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SHL,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SHL,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SHR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SHR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SLE,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SLE,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SLT,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SLT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMOD,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMOD,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SREM,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SREM,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SUB,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_SUB,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UDIV,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UDIV,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UGE,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UGE,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UGT,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UGT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ULE,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ULE,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ULT,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_ULT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UREM,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_UREM,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_XNOR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_XNOR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_XOR,
                                bv_args2_inv.size(),
                                bv_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_XOR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  // floating-point
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ABS,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_inv_2.size(),
                                fp_args3_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_inv_1.size(),
                                fp_args3_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_inv_2.size(),
                                fp_args3_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_inv_1.size(),
                                fp_args3_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_EQ,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_EQ,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FMA,
                                fp_args4_rm_inv_1.size(),
                                fp_args4_rm_inv_1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FMA,
                                fp_args4_rm_inv_2.size(),
                                fp_args4_rm_inv_2.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FMA,
                                fp_args4_mis.size(),
                                fp_args4_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_inv_1.size(),
                                fp_fp_args3_inv_1.data()),
               "invalid bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_inv_2.size(),
                                fp_fp_args3_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_inv_3.size(),
                                fp_fp_args3_inv_3.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_inv_4.size(),
                                fp_fp_args3_inv_4.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_GEQ,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_GEQ,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_GT,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_GT,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_INF,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_NAN,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_NEG,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_NORMAL,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_POS,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_SUBNORMAL,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_ZERO,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_LEQ,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_LEQ,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_LT,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_LT,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MAX,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MAX,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MIN,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MIN,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_IS_ZERO,
                                fp_args1_inv.size(),
                                fp_args1_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_inv_2.size(),
                                fp_args3_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_inv_1.size(),
                                fp_args3_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_REM,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_REM,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_rm_inv_1.size(),
                                fp_args2_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_rm_inv_2.size(),
                                fp_args2_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_inv.size(),
                                fp_args2_inv.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_rm_inv_1.size(),
                                fp_args2_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_rm_inv_2.size(),
                                fp_args2_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_inv_2.size(),
                                fp_args3_rm_inv_2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_inv_1.size(),
                                fp_args3_rm_inv_1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  // others
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_APPLY,
                                apply_args3_inv_1.size(),
                                apply_args3_inv_1.data()),
               error_fun_term);
  ASSERT_DEATH(
      bitwuzla_mk_term(d_bzla,
                       BITWUZLA_KIND_APPLY,
                       apply_args3_inv_2.size(),
                       apply_args3_inv_2.data()),
      "sorts of arguments to apply don't match domain sorts of given function");
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_select_args2_inv_1.size(),
                                array_select_args2_inv_1.data()),
               error_arr_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_select_args2_inv_2.size(),
                                array_select_args2_inv_2.data()),
               error_arr_index_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_inv_1.size(),
                                array_store_args3_inv_1.data()),
               error_arr_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_inv_2.size(),
                                array_store_args3_inv_2.data()),
               error_arr_index_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_inv_3.size(),
                                array_store_args3_inv_3.data()),
               error_arr_element_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_DISTINCT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_EQUAL,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_inv_1.size(),
                                quant_args2_inv_1.data()),
               error_var_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_inv_2.size(),
                                quant_args2_inv_2.data()),
               error_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_inv_3.size(),
                                quant_args2_inv_3.data()),
               error_bvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_EXISTS,
                                quant_args3_inv.size(),
                                quant_args3_inv.data()),
               error_dvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_inv_1.size(),
                                quant_args2_inv_1.data()),
               error_var_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_inv_2.size(),
                                quant_args2_inv_2.data()),
               error_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_inv_3.size(),
                                quant_args2_inv_3.data()),
               error_bvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FORALL,
                                quant_args3_inv.size(),
                                quant_args3_inv.data()),
               error_dvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ITE,
                                ite_args3_inv_2.size(),
                                ite_args3_inv_2.data()),
               error_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ITE,
                                ite_death_args3_1.size(),
                                ite_death_args3_1.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args2_inv_1.size(),
                                lambda_args2_inv_1.data()),
               error_var_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args2_inv_2.size(),
                                lambda_args2_inv_2.data()),
               error_bvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args2_inv_3.size(),
                                lambda_args2_inv_3.data()),
               error_fun_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args3_inv.size(),
                                lambda_args3_inv.data()),
               error_dvar_term);
  // indexed
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs2.size(),
                                        bv_idxs2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extract_death_idxs2_1.size(),
                                        bv_extract_death_idxs2_1.data()),
               "upper index must be >= lower index");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extract_death_idxs2_2.size(),
                                        bv_extract_death_idxs2_2.data()),
               "upper index must be < bit-vector size of given term");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_REPEAT,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term_indexed(d_bzla,
                               BITWUZLA_KIND_BV_REPEAT,
                               bv_args1.size(),
                               bv_args1.data(),
                               bv_repeat_death_idxs1.size(),
                               bv_repeat_death_idxs1.data()),
      "resulting bit-vector size of 'repeat' exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_ROLI,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_RORI,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extend_death_idxs1.size(),
                                        bv_extend_death_idxs1.data()),
               "exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extend_death_idxs1.size(),
                                        bv_extend_death_idxs1.data()),
               "exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args1_inv.size(),
                                        bv_args1_inv.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm_inv_1.size(),
                                        fp_args2_rm_inv_1.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm_inv_2.size(),
                                        fp_args2_rm_inv_2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_INT,
                                        bv_args2_rm_inv_1.size(),
                                        bv_args2_rm_inv_1.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_INT,
                                        bv_args2_rm_inv_2.size(),
                                        bv_args2_rm_inv_2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
                                        bv_args2_rm_inv_1.size(),
                                        bv_args2_rm_inv_1.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
                                        bv_args2_rm_inv_2.size(),
                                        bv_args2_rm_inv_2.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args2_rm_inv_1.size(),
                                        fp_args2_rm_inv_1.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args2_rm_inv_2.size(),
                                        fp_args2_rm_inv_2.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args2_rm_inv_1.size(),
                                        fp_args2_rm_inv_1.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args2_rm_inv_2.size(),
                                        fp_args2_rm_inv_2.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
}
