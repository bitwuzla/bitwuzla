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

    d_arr_sort_bvfp = bitwuzla_mk_array_sort(d_bzla, d_bv_sort8, d_fp_sort16);
    d_arr_sort_fpbv = bitwuzla_mk_array_sort(d_bzla, d_fp_sort16, d_bv_sort8);
    d_arr_sort_bv   = bitwuzla_mk_array_sort(d_bzla, d_bv_sort32, d_bv_sort8);

    d_fun_domain_sort = {d_bv_sort8, d_fp_sort16, d_bv_sort32};
    d_fun_sort        = bitwuzla_mk_fun_sort(
        d_bzla, d_fun_domain_sort.size(), d_fun_domain_sort.data(), d_bv_sort8);
    d_fun_sort_fp = bitwuzla_mk_fun_sort(d_bzla,
                                         d_fun_domain_sort.size(),
                                         d_fun_domain_sort.data(),
                                         d_fp_sort16);
    d_true        = bitwuzla_mk_true(d_bzla);
    d_bv_one1     = bitwuzla_mk_bv_one(d_bzla, d_bv_sort1);
    d_bv_ones23   = bitwuzla_mk_bv_one(d_bzla, d_bv_sort23);
    d_bv_zero8    = bitwuzla_mk_bv_zero(d_bzla, d_bv_sort8);
    d_fp_pzero32  = bitwuzla_mk_fp_pos_zero(d_bzla, d_fp_sort32);

    d_bv_const1  = bitwuzla_mk_const(d_bzla, d_bv_sort1, "bv_const1");
    d_bv_const8  = bitwuzla_mk_const(d_bzla, d_bv_sort8, "bv_const8");
    d_fp_const16 = bitwuzla_mk_const(d_bzla, d_fp_sort16, "fp_const16");
    d_rm_const   = bitwuzla_mk_const(d_bzla, d_rm_sort, "rm_const");

    d_fun        = bitwuzla_mk_const(d_bzla, d_fun_sort, "fun");
    d_fun_fp     = bitwuzla_mk_const(d_bzla, d_fun_sort_fp, "fun_fp");
    d_array_fpbv = bitwuzla_mk_const(d_bzla, d_arr_sort_fpbv, "array_fpbv");
    d_array      = bitwuzla_mk_const(d_bzla, d_arr_sort_bv, "array");

    d_var1      = bitwuzla_mk_var(d_bzla, d_bv_sort8, "var1");
    d_var2      = bitwuzla_mk_var(d_bzla, d_bv_sort8, "var2");
    d_bound_var = bitwuzla_mk_var(d_bzla, d_bv_sort8, "bount_var");
    d_bool_var =
        bitwuzla_mk_var(d_bzla, bitwuzla_mk_bool_sort(d_bzla), "bool_var");

    d_not_bv_const1 = bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_NOT, d_bv_const1);
    d_and_bv_const1 =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_AND, d_true, d_bv_const1);
    d_eq_bv_const8 =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, d_bv_const8, d_bv_zero8);

    BitwuzlaTerm *lambda_body = bitwuzla_mk_term2(
        d_bzla, BITWUZLA_KIND_BV_ADD, d_bound_var, d_bv_const8);
    d_lambda = bitwuzla_mk_term2(
        d_bzla, BITWUZLA_KIND_LAMBDA, d_bound_var, lambda_body);
    d_bool_lambda_body =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, d_bool_var, d_true);
    d_bool_lambda = bitwuzla_mk_term2(
        d_bzla, BITWUZLA_KIND_LAMBDA, d_bool_var, d_bool_lambda_body);
    d_bool_apply =
        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_APPLY, d_true, d_bool_lambda);

    /* associated with other Bitwuzla instance */
    d_other_bzla            = bitwuzla_new();
    d_other_bv_sort1        = bitwuzla_mk_bv_sort(d_other_bzla, 1);
    d_other_bv_sort8        = bitwuzla_mk_bv_sort(d_other_bzla, 8);
    d_other_fp_sort16       = bitwuzla_mk_fp_sort(d_other_bzla, 5, 11);
    d_other_fun_domain_sort = {d_other_bv_sort8, d_other_bv_sort8};
    d_other_arr_sort_bv = bitwuzla_mk_array_sort(
        d_other_bzla, d_other_bv_sort8, d_other_bv_sort8);

    d_other_true = bitwuzla_mk_true(d_other_bzla);
    d_other_bv_one1  = bitwuzla_mk_bv_one(d_other_bzla, d_other_bv_sort1);
    d_other_bv_zero8 = bitwuzla_mk_bv_zero(d_other_bzla, d_other_bv_sort8);

    d_other_bv_const8 =
        bitwuzla_mk_const(d_other_bzla, d_other_bv_sort8, "bv_const8");

    d_other_exists_var =
        bitwuzla_mk_var(d_other_bzla, d_other_bv_sort8, "exists_var");
    d_other_exists = bitwuzla_mk_term2(
        d_other_bzla,
        BITWUZLA_KIND_EXISTS,
        d_other_exists_var,
        bitwuzla_mk_term2(d_other_bzla,
                          BITWUZLA_KIND_EQUAL,
                          d_other_bv_zero8,
                          bitwuzla_mk_term2(d_other_bzla,
                                            BITWUZLA_KIND_BV_MUL,
                                            d_other_bv_const8,
                                            d_other_exists_var)));
  }

  /* sorts */
  BitwuzlaSort *d_arr_sort_bv;
  BitwuzlaSort *d_arr_sort_bvfp;
  BitwuzlaSort *d_arr_sort_fpbv;
  BitwuzlaSort *d_bv_sort1;
  BitwuzlaSort *d_bv_sort23;
  BitwuzlaSort *d_bv_sort32;
  BitwuzlaSort *d_bv_sort8;
  BitwuzlaSort *d_fp_sort16;
  BitwuzlaSort *d_fp_sort32;
  BitwuzlaSort *d_fun_sort;
  BitwuzlaSort *d_fun_sort_fp;
  std::vector<const BitwuzlaSort *> d_fun_domain_sort;
  BitwuzlaSort *d_rm_sort;

  /* terms */
  BitwuzlaTerm *d_true;
  BitwuzlaTerm *d_bv_one1;
  BitwuzlaTerm *d_bv_ones23;
  BitwuzlaTerm *d_bv_zero8;
  BitwuzlaTerm *d_fp_pzero32;

  BitwuzlaTerm *d_bv_const1;
  BitwuzlaTerm *d_bv_const8;
  BitwuzlaTerm *d_fp_const16;
  BitwuzlaTerm *d_rm_const;

  BitwuzlaTerm *d_fun;
  BitwuzlaTerm *d_fun_fp;
  BitwuzlaTerm *d_array_fpbv;
  BitwuzlaTerm *d_array;

  BitwuzlaTerm *d_var1;
  BitwuzlaTerm *d_var2;
  BitwuzlaTerm *d_bound_var;
  BitwuzlaTerm *d_bool_var;

  BitwuzlaTerm *d_not_bv_const1;
  BitwuzlaTerm *d_and_bv_const1;
  BitwuzlaTerm *d_eq_bv_const8;
  BitwuzlaTerm *d_lambda;
  BitwuzlaTerm *d_bool_lambda;
  BitwuzlaTerm *d_bool_lambda_body;
  BitwuzlaTerm *d_bool_apply;

  /* not associated with d_bzla */
  Bitwuzla *d_other_bzla;
  BitwuzlaSort *d_other_arr_sort_bv;
  BitwuzlaSort *d_other_bv_sort1;
  BitwuzlaSort *d_other_bv_sort8;
  BitwuzlaSort *d_other_fp_sort16;
  std::vector<const BitwuzlaSort *> d_other_fun_domain_sort;
  BitwuzlaTerm *d_other_bv_one1;
  BitwuzlaTerm *d_other_bv_zero8;
  BitwuzlaTerm *d_other_exists_var;
  BitwuzlaTerm *d_other_bv_const8;
  BitwuzlaTerm *d_other_true;
  BitwuzlaTerm *d_other_exists;

  /* error messages */
  const char *d_error_not_null = "must not be NULL";
  const char *d_error_solver   = "is not associated with given solver instance";
  const char *d_error_exp_arr_sort   = "expected array sort";
  const char *d_error_exp_bv_sort    = "expected bit-vector sort";
  const char *d_error_exp_fp_sort    = "expected floating-point sort";
  const char *d_error_exp_fun_sort   = "expected function sort";
  const char *d_error_exp_str        = "expected non-empty string";
  const char *d_error_unexp_arr_sort = "unexpected array sort";
  const char *d_error_unexp_fun_sort = "unexpected function sort";
  const char *d_error_zero           = "must be > 0";
  const char *d_error_bv_fit         = "does not fit into a bit-vector of size";
  const char *d_error_exp_bool_term  = "expected boolean term";
  const char *d_error_exp_bv_term    = "expected bit-vector term";
  const char *d_error_exp_bv_value   = "expected bit-vector value";
  const char *d_error_exp_rm_term    = "expected rounding-mode term";
  const char *d_error_exp_arr_term   = "expected array term";
  const char *d_error_exp_assumption = "must be an assumption";
  const char *d_error_rm             = "invalid rounding mode";
  const char *d_error_unexp_arr_term = "unexpected array term";
  const char *d_error_unexp_fun_term = "unexpected function term";
  const char *d_error_unexp_param_term = "term must not be parameterized";
  const char *d_error_incremental      = "incremental usage not enabled";
  const char *d_error_produce_models   = "model production not enabled";
  const char *d_error_unsat            = "if input formula is not unsat";
  const char *d_error_sat              = "if input formula is not sat";
  const char *d_error_format           = "unknown format";
  const char *d_error_inc_quant =
      "incremental solving is currently not supported with quantifiers";
};

TEST_F(TestApi, set_option)
{
  Bitwuzla *bzla_inc   = bitwuzla_new();
  Bitwuzla *bzla_dp    = bitwuzla_new();
  Bitwuzla *bzla_just  = bitwuzla_new();
  Bitwuzla *bzla_mg    = bitwuzla_new();
  Bitwuzla *bzla_non   = bitwuzla_new();
  Bitwuzla *bzla_uc    = bitwuzla_new();
  Bitwuzla *bzla_ucopt = bitwuzla_new();

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_inc, BITWUZLA_OPT_INCREMENTAL, 1));
  ASSERT_DEATH(bitwuzla_set_option(bzla_inc, BITWUZLA_OPT_UCOPT, 1),
               "unconstrained optimization cannot be enabled in incremental "
               "mode");
  bitwuzla_check_sat(bzla_inc);
  ASSERT_DEATH(bitwuzla_set_option(bzla_inc, BITWUZLA_OPT_INCREMENTAL, 0),
               "enabling/disabling incremental usage after having called "
               "'bitwuzla_check_sat' is not allowed");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_dp, BITWUZLA_OPT_FUN_DUAL_PROP, 1));
  ASSERT_DEATH(bitwuzla_set_option(bzla_dp, BITWUZLA_OPT_FUN_JUST, 1),
               "enabling multiple optimization techniques is not allowed");
  ASSERT_DEATH(
      bitwuzla_set_option(bzla_dp, BITWUZLA_OPT_NONDESTR_SUBST, 1),
      "non-destructive substitution is not supported with dual propagation");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_just, BITWUZLA_OPT_FUN_JUST, 1));
  ASSERT_DEATH(bitwuzla_set_option(bzla_just, BITWUZLA_OPT_FUN_DUAL_PROP, 1),
               "enabling multiple optimization techniques is not allowed");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_mg, BITWUZLA_OPT_PRODUCE_MODELS, 1));
  ASSERT_DEATH(bitwuzla_set_option(bzla_mg, BITWUZLA_OPT_UCOPT, 1),
               "unconstrained optimization cannot be enabled if model "
               "generation is enabled");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_non, BITWUZLA_OPT_NONDESTR_SUBST, 1));
  ASSERT_DEATH(
      bitwuzla_set_option(bzla_non, BITWUZLA_OPT_FUN_DUAL_PROP, 1),
      "non-destructive substitution is not supported with dual propagation");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_ucopt, BITWUZLA_OPT_UCOPT, 1));
  ASSERT_DEATH(bitwuzla_set_option(bzla_ucopt, BITWUZLA_OPT_INCREMENTAL, 1),
               "incremental solving cannot be enabled if unconstrained "
               "optimization is enabled");
  ASSERT_DEATH(bitwuzla_set_option(bzla_ucopt, BITWUZLA_OPT_PRODUCE_MODELS, 1),
               "model generation cannot be enabled if unconstrained "
               "optimization is enabled");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_set_option(bzla_uc, BITWUZLA_OPT_PRODUCE_UNSAT_CORES, 1));
}

TEST_F(TestApi, mk_array_sort)
{
  ASSERT_DEATH(bitwuzla_mk_array_sort(nullptr, d_bv_sort1, d_bv_sort8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, nullptr, d_bv_sort8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, d_bv_sort1, nullptr),
               d_error_not_null);

  ASSERT_DEATH(
      bitwuzla_mk_array_sort(d_other_bzla, d_other_bv_sort8, d_bv_sort8),
      d_error_solver);
  ASSERT_DEATH(
      bitwuzla_mk_array_sort(d_other_bzla, d_bv_sort8, d_other_bv_sort8),
      d_error_solver);

  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, d_arr_sort_bv, d_bv_sort8),
               d_error_unexp_arr_sort);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, d_bv_sort8, d_arr_sort_bv),
               d_error_unexp_arr_sort);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, d_fun_sort, d_bv_sort8),
               d_error_unexp_fun_sort);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_bzla, d_bv_sort8, d_fun_sort),
               d_error_unexp_fun_sort);
}

TEST_F(TestApi, mk_bool_sort)
{
  ASSERT_DEATH(bitwuzla_mk_bool_sort(nullptr), d_error_not_null);
}

TEST_F(TestApi, mk_bv_sort)
{
  ASSERT_DEATH(bitwuzla_mk_bv_sort(nullptr, 4), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_sort(d_bzla, 0), d_error_zero);
}

TEST_F(TestApi, mk_fp_sort)
{
  ASSERT_DEATH(bitwuzla_mk_fp_sort(nullptr, 5, 8), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_bzla, 0, 8), d_error_zero);
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_bzla, 5, 0), d_error_zero);
}

TEST_F(TestApi, mk_fun_sort)
{
  ASSERT_DEATH(bitwuzla_mk_fun_sort(nullptr,
                                    d_fun_domain_sort.size(),
                                    d_fun_domain_sort.data(),
                                    d_bv_sort8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fun_sort(
                   d_bzla, d_fun_domain_sort.size(), nullptr, d_bv_sort8),
               d_error_not_null);

  std::vector<const BitwuzlaSort *> empty = {};
  ASSERT_DEATH(
      bitwuzla_mk_fun_sort(d_bzla, empty.size(), empty.data(), d_bv_sort8),
      d_error_zero);

  ASSERT_DEATH(bitwuzla_mk_fun_sort(d_bzla,
                                    d_other_fun_domain_sort.size(),
                                    d_other_fun_domain_sort.data(),
                                    d_bv_sort8),
               d_error_solver);
  ASSERT_DEATH(bitwuzla_mk_fun_sort(d_bzla,
                                    d_fun_domain_sort.size(),
                                    d_fun_domain_sort.data(),
                                    d_other_bv_sort8),
               d_error_solver);
}

TEST_F(TestApi, mk_rm_sort)
{
  ASSERT_DEATH(bitwuzla_mk_rm_sort(nullptr), d_error_not_null);
}

TEST_F(TestApi, mk_true)
{
  ASSERT_DEATH(bitwuzla_mk_true(nullptr), d_error_not_null);
}

TEST_F(TestApi, mk_false)
{
  ASSERT_DEATH(bitwuzla_mk_false(nullptr), d_error_not_null);
}

TEST_F(TestApi, mk_bv_zero)
{
  ASSERT_DEATH(bitwuzla_mk_bv_zero(nullptr, d_bv_sort8), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_zero(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_zero(d_bzla, d_fp_sort16), d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_zero(d_bzla, d_other_bv_sort8), d_error_solver);
}

TEST_F(TestApi, mk_bv_one)
{
  ASSERT_DEATH(bitwuzla_mk_bv_one(nullptr, d_bv_sort8), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_one(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_one(d_bzla, d_fp_sort16), d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_one(d_bzla, d_other_bv_sort8), d_error_solver);
}

TEST_F(TestApi, mk_bv_ones)
{
  ASSERT_DEATH(bitwuzla_mk_bv_ones(nullptr, d_bv_sort8), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_ones(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_ones(d_bzla, d_fp_sort16), d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_ones(d_bzla, d_other_bv_sort8), d_error_solver);
}

TEST_F(TestApi, mk_bv_min_signed)
{
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(nullptr, d_bv_sort8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(d_bzla, d_fp_sort16),
               d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(d_bzla, d_other_bv_sort8),
               d_error_solver);
}

TEST_F(TestApi, mk_bv_max_signed)
{
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(nullptr, d_fp_sort16),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(d_bzla, d_fp_sort16),
               d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(d_bzla, d_other_bv_sort8),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_pos_zero)
{
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(nullptr, d_fp_sort16), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(d_bzla, d_bv_sort8),
               d_error_exp_fp_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(d_bzla, d_other_fp_sort16),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_neg_zero)
{
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(nullptr, d_fp_sort16), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(d_bzla, d_bv_sort8),
               d_error_exp_fp_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(d_bzla, d_other_fp_sort16),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_pos_inf)
{
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(nullptr, d_fp_sort16), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(d_bzla, d_bv_sort8), d_error_exp_fp_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(d_bzla, d_other_fp_sort16),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_neg_inf)
{
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(nullptr, d_fp_sort16), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(d_bzla, d_bv_sort8), d_error_exp_fp_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(d_bzla, d_other_fp_sort16),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_nan)
{
  ASSERT_DEATH(bitwuzla_mk_fp_nan(nullptr, d_fp_sort16), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_nan(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_nan(d_bzla, d_bv_sort8), d_error_exp_fp_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_nan(d_bzla, d_other_fp_sort16), d_error_solver);
}

TEST_F(TestApi, mk_bv_value)
{
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(nullptr, d_bv_sort8, "010", BITWUZLA_BV_BASE_BIN),
      d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(d_bzla, nullptr, "010", BITWUZLA_BV_BASE_BIN),
      d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(d_bzla, d_bv_sort8, nullptr, BITWUZLA_BV_BASE_BIN),
      d_error_exp_str);
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(d_bzla, d_bv_sort8, "", BITWUZLA_BV_BASE_BIN),
      d_error_exp_str);

  ASSERT_DEATH(
      bitwuzla_mk_bv_value(d_bzla, d_fp_sort16, "010", BITWUZLA_BV_BASE_BIN),
      d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_other_bv_sort8, "010", BITWUZLA_BV_BASE_BIN),
               d_error_solver);

  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_bv_sort8, "11111111010", BITWUZLA_BV_BASE_BIN),
               d_error_bv_fit);
  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_bv_sort8, "1234567890", BITWUZLA_BV_BASE_DEC),
               d_error_bv_fit);
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(
          d_bzla, d_bv_sort8, "1234567890aAbBcCdDeEfF", BITWUZLA_BV_BASE_HEX),
      d_error_bv_fit);
  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_bv_sort8, "1234567890", BITWUZLA_BV_BASE_BIN),
               "invalid binary string");
  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_bv_sort8, "12z4567890", BITWUZLA_BV_BASE_DEC),
               "invalid decimal string");
  ASSERT_DEATH(bitwuzla_mk_bv_value(
                   d_bzla, d_bv_sort8, "12z4567890", BITWUZLA_BV_BASE_HEX),
               "invalid hex string");
}

TEST_F(TestApi, mk_bv_value_uint64)
{
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(nullptr, d_bv_sort8, 23),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(d_bzla, nullptr, 23),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(d_bzla, d_fp_sort16, 23),
               d_error_exp_bv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(d_bzla, d_other_bv_sort8, 23),
               d_error_solver);
}

TEST_F(TestApi, mk_fp_value)
{
  ASSERT_DEATH(bitwuzla_mk_fp_value(nullptr, d_bv_one1, d_bv_zero8, d_bv_zero8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_bzla, nullptr, d_bv_zero8, d_bv_zero8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_bzla, d_bv_one1, nullptr, d_bv_zero8),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_bv_zero8, nullptr),
               d_error_not_null);

  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_other_bv_one1, d_bv_zero8, d_bv_zero8),
      d_error_solver);
  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_other_bv_zero8, d_bv_zero8),
      d_error_solver);
  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_bv_zero8, d_other_bv_zero8),
      d_error_solver);

  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_zero8, d_bv_zero8, d_bv_zero8),
      "invalid bit-vector size for argument 'bv_sign', expected size one");
  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_fp_const16, d_bv_zero8, d_bv_zero8),
      d_error_exp_bv_term);
  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_fp_const16, d_bv_zero8),
      d_error_exp_bv_term);
  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_bv_zero8, d_fp_const16),
      d_error_exp_bv_term);

  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_bzla, d_bv_const1, d_bv_zero8, d_bv_zero8),
      d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_bv_const8, d_bv_zero8),
               d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_bzla, d_bv_one1, d_bv_zero8, d_bv_const8),
               d_error_exp_bv_value);
}

TEST_F(TestApi, mk_rm_value)
{
  ASSERT_DEATH(bitwuzla_mk_rm_value(nullptr, BITWUZLA_RM_RNA),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_MAX), d_error_rm);
}

TEST_F(TestApi, mk_term_check_null)
{
  std::vector<const BitwuzlaTerm *> bv_args2 = {d_bv_zero8, d_bv_const8};

  std::vector<const BitwuzlaTerm *> null_death_args1 = {nullptr};
  std::vector<const BitwuzlaTerm *> null_death_args2 = {d_bv_zero8, nullptr};
  std::vector<const BitwuzlaTerm *> null_death_args3 = {
      d_rm_const, nullptr, d_fp_const16};

  // mk_term
  ASSERT_DEATH(
      bitwuzla_mk_term(
          nullptr, BITWUZLA_KIND_BV_AND, bv_args2.size(), bv_args2.data()),
      d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_NOT,
                                null_death_args1.size(),
                                null_death_args1.data()),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_BV_AND,
                                null_death_args2.size(),
                                null_death_args2.data()),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_ADD,
                                null_death_args3.size(),
                                null_death_args3.data()),
               d_error_not_null);
  // mk_term1
  ASSERT_DEATH(bitwuzla_mk_term1(nullptr, BITWUZLA_KIND_BV_NOT, d_bv_one1),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, nullptr),
               d_error_not_null);
  // mk_term2
  ASSERT_DEATH(
      bitwuzla_mk_term2(nullptr, BITWUZLA_KIND_BV_AND, d_bv_zero8, d_bv_const8),
      d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_AND, nullptr, d_bv_const8),
      d_error_not_null);
  // mk_term3
  ASSERT_DEATH(bitwuzla_mk_term3(nullptr,
                                 BITWUZLA_KIND_FP_ADD,
                                 d_rm_const,
                                 d_fp_const16,
                                 d_fp_const16),
               d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_mk_term3(
          d_bzla, BITWUZLA_KIND_FP_ADD, nullptr, d_fp_const16, d_fp_const16),
      d_error_not_null);
}

TEST_F(TestApi, mk_term_check_cnt)
{
  const char *error_arg_cnt = "invalid number of arguments";

  std::vector<const BitwuzlaTerm *> apply_args1 = {d_bv_one1};
  std::vector<const BitwuzlaTerm *> apply_args2 = {d_bv_const8, d_fun};
  std::vector<const BitwuzlaTerm *> array_args1 = {d_array_fpbv};
  std::vector<const BitwuzlaTerm *> bool_args1  = {d_true};
  std::vector<const BitwuzlaTerm *> bool_args2  = {d_true, d_true};
  std::vector<const BitwuzlaTerm *> bv_args1    = {d_bv_one1};
  std::vector<const BitwuzlaTerm *> bv_args1_rm = {d_rm_const};
  std::vector<const BitwuzlaTerm *> bv_args2    = {d_bv_zero8, d_bv_const8};
  std::vector<const BitwuzlaTerm *> ite_args2   = {d_true, d_bv_const8};
  std::vector<const BitwuzlaTerm *> fp_args1    = {d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args1_rm = {d_rm_const};
  std::vector<const BitwuzlaTerm *> fp_args2    = {d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args2_rm = {d_rm_const, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args3_rm = {
      d_rm_const, d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fun_args1 = {d_var1};

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
          d_bzla, BITWUZLA_KIND_FP_EQ, fp_args1_rm.size(), fp_args1_rm.data()),
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
          d_bzla, BITWUZLA_KIND_FP_GEQ, fp_args1.size(), fp_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_GT, fp_args1.size(), fp_args1.data()),
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
          d_bzla, BITWUZLA_KIND_FP_LEQ, fp_args1.size(), fp_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_bzla, BITWUZLA_KIND_FP_LT, fp_args1.size(), fp_args1.data()),
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
  const char *error_bvar_term = "expected unbound variable term";
  const char *error_dvar_term = "given variables are not distinct";
  const char *error_var_term  = "expected variable term";

  const char *error_arr_index_sort =
      "sort of index term does not match index sort of array";
  const char *error_arr_element_sort =
      "sort of element term does not match element sort of array";

  std::vector<const BitwuzlaTerm *> array_select_args2_inv_1 = {d_fp_const16,
                                                                d_array_fpbv};
  std::vector<const BitwuzlaTerm *> array_select_args2_inv_2 = {d_array_fpbv,
                                                                d_bv_const8};

  std::vector<const BitwuzlaTerm *> array_store_args3_inv_1 = {
      d_fp_const16, d_array_fpbv, d_bv_const8};
  std::vector<const BitwuzlaTerm *> array_store_args3_inv_2 = {
      d_array_fpbv, d_bv_const8, d_bv_const8};
  std::vector<const BitwuzlaTerm *> array_store_args3_inv_3 = {
      d_array_fpbv, d_fp_const16, d_fp_const16};

  std::vector<const BitwuzlaTerm *> apply_args3_inv_1 = {
      d_bv_const8, d_fun, d_fun};
  std::vector<const BitwuzlaTerm *> apply_args3_inv_2 = {
      d_bv_const8, d_bv_const8, d_fp_pzero32, d_fun};

  std::vector<const BitwuzlaTerm *> bool_args1_inv = {d_bv_const8};
  std::vector<const BitwuzlaTerm *> bool_args2_inv = {d_fp_pzero32,
                                                      d_fp_pzero32};
  std::vector<const BitwuzlaTerm *> bool_args2_mis = {d_true, d_bv_const8};

  std::vector<const BitwuzlaTerm *> bv_args1     = {d_bv_const8};
  std::vector<const BitwuzlaTerm *> bv_args1_inv = {d_fp_const16};
  std::vector<const BitwuzlaTerm *> bv_args2_inv = {d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> bv_args2_mis = {d_bv_one1, d_bv_const8};
  std::vector<const BitwuzlaTerm *> bv_args2_rm_inv_1 = {d_bv_const8,
                                                         d_bv_const8};
  std::vector<const BitwuzlaTerm *> bv_args2_rm_inv_2 = {d_rm_const,
                                                         d_fp_const16};

  std::vector<const BitwuzlaTerm *> ite_death_args3_1 = {
      d_true, d_bv_const8, d_bv_one1};
  std::vector<const BitwuzlaTerm *> ite_args3_inv_2 = {
      d_bv_const8, d_bv_const8, d_bv_const8};

  std::vector<const BitwuzlaTerm *> lambda_args2_inv_1 = {d_bv_const8,
                                                          d_bv_const8};
  std::vector<const BitwuzlaTerm *> lambda_args2_inv_2 = {d_bound_var,
                                                          d_bv_const8};
  std::vector<const BitwuzlaTerm *> lambda_args2_inv_3 = {d_var1, d_fun};
  std::vector<const BitwuzlaTerm *> lambda_args3_inv_1 = {
      d_var1, d_var1, d_bv_const8};

  BitwuzlaTerm *lambda_body =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_ADD, d_var2, d_bv_const8);
  std::vector<const BitwuzlaTerm *> lambda_args3_inv_2 = {
      d_var1,
      d_var2,
      bitwuzla_mk_term2_indexed2(d_bzla,
                                 BITWUZLA_KIND_FP_TO_FP_FROM_UINT,
                                 d_rm_const,
                                 lambda_body,
                                 5,
                                 8)};

  std::vector<const BitwuzlaTerm *> fp_args1_inv = {d_bv_one1};
  std::vector<const BitwuzlaTerm *> fp_args2_inv = {d_bv_zero8, d_bv_const8};
  std::vector<const BitwuzlaTerm *> fp_args2_mis = {d_fp_pzero32, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args2_rm_inv_1 = {d_bv_const8,
                                                         d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args2_rm_inv_2 = {d_rm_const,
                                                         d_bv_const8};
  std::vector<const BitwuzlaTerm *> fp_args3_rm_mis   = {
      d_rm_const, d_fp_pzero32, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args3_rm_inv_1 = {
      d_fp_const16, d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args3_rm_inv_2 = {
      d_rm_const, d_bv_zero8, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args4_mis = {
      d_rm_const, d_fp_pzero32, d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args4_rm_inv_1 = {
      d_rm_const, d_bv_zero8, d_fp_const16, d_fp_const16};
  std::vector<const BitwuzlaTerm *> fp_args4_rm_inv_2 = {
      d_fp_const16, d_fp_const16, d_fp_const16, d_fp_const16};

  std::vector<const BitwuzlaTerm *> fp_fp_args3_inv_1 = {
      d_bv_const8, d_bv_zero8, d_bv_ones23};
  std::vector<const BitwuzlaTerm *> fp_fp_args3_inv_2 = {
      d_bv_one1, d_fp_pzero32, d_bv_ones23};
  std::vector<const BitwuzlaTerm *> fp_fp_args3_inv_3 = {
      d_bv_one1, d_bv_zero8, d_fp_pzero32};
  std::vector<const BitwuzlaTerm *> fp_fp_args3_inv_4 = {
      d_fp_pzero32, d_bv_zero8, d_bv_ones23};

  std::vector<const BitwuzlaTerm *> quant_args2_inv_1 = {d_true, d_true};
  std::vector<const BitwuzlaTerm *> quant_args2_inv_2 = {d_var1, d_bv_const8};
  std::vector<const BitwuzlaTerm *> quant_args2_inv_3 = {d_bound_var,
                                                         d_bv_const8};
  std::vector<const BitwuzlaTerm *> quant_args3_inv   = {
      d_var1, d_var1, d_bv_const8};

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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_rm_inv_1.size(),
                                fp_args2_rm_inv_1.data()),
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_rm_inv_1.size(),
                                fp_args2_rm_inv_1.data()),
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_unexp_fun_term);
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
               d_error_exp_arr_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_select_args2_inv_2.size(),
                                array_select_args2_inv_2.data()),
               error_arr_index_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_inv_1.size(),
                                array_store_args3_inv_1.data()),
               d_error_exp_arr_term);
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
               d_error_exp_bool_term);
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
               d_error_exp_bool_term);
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
               d_error_exp_bool_term);
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
               d_error_unexp_fun_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args3_inv_1.size(),
                                lambda_args3_inv_1.data()),
               error_dvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_bzla,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args3_inv_2.size(),
                                lambda_args3_inv_2.data()),
               "expected bit-vector term or bit-vector function term");
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
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
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_bzla,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args2_rm_inv_2.size(),
                                        fp_args2_rm_inv_2.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_inv_sort);
}

TEST_F(TestApi, mk_const)
{
  ASSERT_DEATH(bitwuzla_mk_const(nullptr, d_bv_sort8, "asdf"),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_const(d_bzla, nullptr, "asdf"), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_const(d_bzla, d_bv_sort8, "bv_const8"),
               "already in use in the current context");
  ASSERT_DEATH(bitwuzla_mk_const(d_bzla, d_other_bv_sort8, "asdf"),
               d_error_solver);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_mk_const(d_bzla, d_bv_sort8, nullptr));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_mk_const(d_bzla, d_bv_sort8, ""));
}

TEST_F(TestApi, mk_const_array)
{
  ASSERT_DEATH(bitwuzla_mk_const_array(nullptr, d_arr_sort_bv, d_bv_one1),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, nullptr, d_bv_one1),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_arr_sort_bv, nullptr),
               d_error_not_null);

  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_arr_sort_bv, d_other_bv_one1),
               d_error_solver);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_other_arr_sort_bv, d_bv_one1),
               d_error_solver);

  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_bv_sort8, d_bv_one1),
               d_error_exp_arr_sort);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_other_arr_sort_bv, d_bv_one1),
               d_error_solver);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_arr_sort_bv, d_array),
               d_error_unexp_arr_term);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_bzla, d_arr_sort_bvfp, d_fp_pzero32),
               "sort of 'value' does not match array element sort");

  ASSERT_NO_FATAL_FAILURE(
      bitwuzla_mk_const_array(d_bzla, d_arr_sort_bvfp, d_fp_const16));
}

TEST_F(TestApi, mk_var)
{
  ASSERT_DEATH(bitwuzla_mk_var(nullptr, d_bv_sort8, "asdf"), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_var(d_bzla, nullptr, "asdf"), d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_var(d_bzla, d_other_bv_sort8, "asdf"),
               d_error_solver);
  ASSERT_DEATH(bitwuzla_mk_var(d_bzla, d_bv_sort8, "bv_const8"),
               "already in use in the current context");

  ASSERT_NO_FATAL_FAILURE(bitwuzla_mk_var(d_bzla, d_bv_sort8, nullptr));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_mk_var(d_bzla, d_bv_sort8, ""));
}

TEST_F(TestApi, push)
{
  ASSERT_DEATH(bitwuzla_push(d_bzla, 2), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_push(nullptr, 2), d_error_not_null);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_push(d_bzla, 0));
}

TEST_F(TestApi, pop)
{
  ASSERT_DEATH(bitwuzla_pop(d_bzla, 2), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_pop(nullptr, 2), d_error_not_null);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_pop(d_bzla, 0));
}

TEST_F(TestApi, assert)
{
  ASSERT_DEATH(bitwuzla_assert(nullptr, d_true), d_error_not_null);
  ASSERT_DEATH(bitwuzla_assert(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_assert(d_bzla, d_other_true), d_error_solver);
  ASSERT_DEATH(bitwuzla_assert(d_bzla, d_bv_const8), d_error_exp_bool_term);

  ASSERT_DEATH(bitwuzla_assert(d_bzla, d_bool_var), d_error_unexp_param_term);
  ASSERT_DEATH(bitwuzla_assert(d_bzla, d_bool_lambda), d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_assert(d_bzla, d_bool_lambda_body),
               d_error_unexp_param_term);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_assert(d_bzla, d_bool_apply));

  ASSERT_NO_FATAL_FAILURE(bitwuzla_assert(d_bzla, d_bv_one1));
}

TEST_F(TestApi, assume)
{
  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_bv_const1), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  ASSERT_DEATH(bitwuzla_assume(nullptr, d_true), d_error_not_null);
  ASSERT_DEATH(bitwuzla_assume(d_bzla, nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_other_true), d_error_solver);
  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_bv_const8), d_error_exp_bool_term);

  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_bool_var), d_error_unexp_param_term);
  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_bool_lambda), d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_assume(d_bzla, d_bool_lambda_body),
               d_error_unexp_param_term);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_assume(d_bzla, d_bool_apply));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_assume(d_bzla, d_bv_one1));
}

TEST_F(TestApi, is_unsat_assumption)
{
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1),
               d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  ASSERT_DEATH(bitwuzla_is_unsat_assumption(nullptr, d_true), d_error_not_null);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, nullptr), d_error_not_null);

  bitwuzla_assert(d_bzla, d_true);
  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_check_sat(d_bzla);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1),
               d_error_unsat);

  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla,
                  bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_NOT, d_bv_const1));
  bitwuzla_check_sat(d_bzla);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_other_true),
               d_error_solver);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const8),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_true),
               d_error_exp_assumption);

  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bool_var),
               d_error_exp_assumption);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bool_lambda),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_is_unsat_assumption(d_bzla, d_bool_lambda_body),
               d_error_exp_assumption);

  ASSERT_NO_FATAL_FAILURE(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1));
}

TEST_F(TestApi, get_unsat_assumptions)
{
  size_t size;
  ASSERT_DEATH(bitwuzla_get_unsat_assumptions(d_bzla, &size),
               d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  ASSERT_DEATH(bitwuzla_get_unsat_assumptions(nullptr, &size),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_get_unsat_assumptions(d_bzla, nullptr),
               d_error_not_null);

  bitwuzla_assert(d_bzla, d_true);
  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_check_sat(d_bzla);
  ASSERT_DEATH(bitwuzla_get_unsat_assumptions(d_bzla, &size), d_error_unsat);

  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla, d_not_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  bitwuzla_assume(d_bzla, d_eq_bv_const8);
  bitwuzla_check_sat(d_bzla);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1));
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_not_bv_const1));
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_and_bv_const1));
  ASSERT_FALSE(bitwuzla_is_unsat_assumption(d_bzla, d_eq_bv_const8));
  BitwuzlaTerm **unsat_ass = bitwuzla_get_unsat_assumptions(d_bzla, &size);
  size_t i = 0;
  for (; i < size; ++i)
  {
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, unsat_ass[i]));
  }
  ASSERT_EQ(i, 3);
  for (i = 0; i < size; ++i)
  {
    bitwuzla_assert(d_bzla, unsat_ass[i]);
  }
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
}

TEST_F(TestApi, get_unsat_core)
{
  size_t size;
  ASSERT_DEATH(bitwuzla_get_unsat_core(d_bzla, &size), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_get_unsat_core(d_bzla, &size),
               "unsat core production not enabled");
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_PRODUCE_UNSAT_CORES, 1);

  ASSERT_DEATH(bitwuzla_get_unsat_core(nullptr, &size), d_error_not_null);
  ASSERT_DEATH(bitwuzla_get_unsat_core(d_bzla, nullptr), d_error_not_null);

  bitwuzla_assert(d_bzla, d_true);
  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_check_sat(d_bzla);
  ASSERT_DEATH(bitwuzla_get_unsat_core(d_bzla, &size), d_error_unsat);

  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assert(d_bzla, d_not_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  bitwuzla_assert(d_bzla, d_eq_bv_const8);
  bitwuzla_check_sat(d_bzla);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1));
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_and_bv_const1));
  BitwuzlaTerm **unsat_core = bitwuzla_get_unsat_core(d_bzla, &size);
  ASSERT_TRUE(unsat_core[0] == d_not_bv_const1);
  ASSERT_TRUE(size == 1);

  BitwuzlaTerm **unsat_ass = bitwuzla_get_unsat_assumptions(d_bzla, &size);
  ASSERT_TRUE(unsat_ass[0] == d_bv_const1);
  ASSERT_TRUE(unsat_ass[1] == d_and_bv_const1);
  ASSERT_TRUE(size == 2);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
  bitwuzla_assert(d_bzla, unsat_ass[0]);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
}

TEST_F(TestApi, fixate_assumptions)
{
  ASSERT_DEATH(bitwuzla_fixate_assumptions(d_bzla), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  ASSERT_DEATH(bitwuzla_fixate_assumptions(nullptr), d_error_not_null);

  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assert(d_bzla, d_not_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  bitwuzla_assert(d_bzla, d_eq_bv_const8);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1));
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_and_bv_const1));
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
  bitwuzla_fixate_assumptions(d_bzla);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
}

TEST_F(TestApi, reset_assumptions)
{
  ASSERT_DEATH(bitwuzla_reset_assumptions(d_bzla), d_error_incremental);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

  ASSERT_DEATH(bitwuzla_reset_assumptions(nullptr), d_error_not_null);

  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assert(d_bzla, d_not_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  bitwuzla_assert(d_bzla, d_eq_bv_const8);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_bv_const1));
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, d_and_bv_const1));
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
  bitwuzla_assume(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla, d_and_bv_const1);
  bitwuzla_reset_assumptions(d_bzla);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
}

TEST_F(TestApi, simplify)
{
  ASSERT_DEATH(bitwuzla_simplify(nullptr), d_error_not_null);
  bitwuzla_assert(d_bzla, d_bv_const1);
  bitwuzla_assert(d_bzla, d_and_bv_const1);
  ASSERT_TRUE(bitwuzla_simplify(d_bzla) == BITWUZLA_SAT);
}

TEST_F(TestApi, check_sat)
{
  ASSERT_DEATH(bitwuzla_check_sat(nullptr), d_error_not_null);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_check_sat(d_bzla));
  ASSERT_DEATH(bitwuzla_check_sat(d_bzla), d_error_incremental);

  bitwuzla_set_option(d_other_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  bitwuzla_assert(d_other_bzla, d_other_exists);
  ASSERT_DEATH(bitwuzla_check_sat(d_other_bzla), d_error_inc_quant);

  Bitwuzla *bzla = bitwuzla_new();
  bitwuzla_set_option(bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_check_sat(bzla));
}

TEST_F(TestApi, get_value)
{
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_get_value(d_bzla, d_bv_const8), d_error_produce_models);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  ASSERT_DEATH(bitwuzla_get_value(nullptr, d_bv_const8), d_error_not_null);
  ASSERT_DEATH(bitwuzla_get_value(d_bzla, nullptr), d_error_not_null);
  bitwuzla_assert(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla, d_not_bv_const1);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
  ASSERT_DEATH(bitwuzla_get_value(d_bzla, d_bv_const1), d_error_sat);
  bitwuzla_check_sat(d_bzla);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_get_value(d_bzla, d_bv_const1));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_get_value(d_bzla, d_not_bv_const1));

  bitwuzla_set_option(d_other_bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  bitwuzla_assert(d_other_bzla, d_other_exists);
  ASSERT_DEATH(bitwuzla_get_value(d_other_bzla, d_other_bv_const8),
               d_error_sat);
  ASSERT_EQ(bitwuzla_check_sat(d_other_bzla), BITWUZLA_SAT);
  ASSERT_DEATH(bitwuzla_get_value(d_other_bzla, d_other_bv_const8),
               "'get-value' is currently not supported with quantifiers");
}

TEST_F(TestApi, print_model)
{
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_print_model(d_bzla, "btor", stdout),
               d_error_produce_models);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  ASSERT_DEATH(bitwuzla_print_model(nullptr, "btor", stdout), d_error_not_null);
  ASSERT_DEATH(bitwuzla_print_model(d_bzla, nullptr, stdout), d_error_exp_str);
  ASSERT_DEATH(bitwuzla_print_model(d_bzla, "smt2", nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_print_model(d_bzla, "asdf", stdout),
               "invalid model output format");

  bitwuzla_assert(d_bzla, d_bv_const1);
  bitwuzla_assume(d_bzla, d_not_bv_const1);
  ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_UNSAT);
  ASSERT_DEATH(bitwuzla_print_model(d_bzla, "btor", stdout), d_error_sat);
  bitwuzla_check_sat(d_bzla);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_print_model(d_bzla, "btor", stdout));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_print_model(d_bzla, "smt2", stdout));

  bitwuzla_set_option(d_other_bzla, BITWUZLA_OPT_PRODUCE_MODELS, 1);
  bitwuzla_assert(d_other_bzla, d_other_exists);
  ASSERT_EQ(bitwuzla_check_sat(d_other_bzla), BITWUZLA_SAT);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_print_model(d_other_bzla, "btor", stdout));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_print_model(d_other_bzla, "smt2", stdout));
}

TEST_F(TestApi, dump_formula)
{
  ASSERT_DEATH(bitwuzla_dump_formula(nullptr, "btor", stdout),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_dump_formula(d_bzla, nullptr, stdout), d_error_exp_str);
  ASSERT_DEATH(bitwuzla_dump_formula(d_bzla, "smt2", nullptr),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_dump_formula(d_bzla, "asdf", stdout), d_error_format);

  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_REWRITE_LEVEL, 0);

  bitwuzla_assert(d_bzla, d_bv_const1);
  bitwuzla_assert(
      d_bzla,
      bitwuzla_mk_term2(
          d_bzla,
          BITWUZLA_KIND_EQUAL,
          bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_APPLY, d_bv_const8, d_lambda),
          d_bv_zero8));

  ASSERT_NO_FATAL_FAILURE(bitwuzla_dump_formula(d_bzla, "btor", stdout));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_dump_formula(d_bzla, "smt2", stdout));

  bitwuzla_assert(d_other_bzla, d_other_exists);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_dump_formula(d_other_bzla, "btor", stdout));
  ASSERT_NO_FATAL_FAILURE(bitwuzla_dump_formula(d_other_bzla, "smt2", stdout));
  bitwuzla_set_option(d_other_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  ASSERT_DEATH(bitwuzla_dump_formula(d_other_bzla, "btor", stdout),
               "dumping in incremental mode is currently not supported");
}

TEST_F(TestApi, parse)
{
  bool is_smt2;
  int32_t status;
  char *error_msg;
  std::string infile_name = "fp_regr1.smt2";
  std::stringstream ss;
  ss << BZLA_OUT_DIR << infile_name;
  FILE *infile = fopen(ss.str().c_str(), "r");

  ASSERT_DEATH(bitwuzla_parse(nullptr,
                              infile,
                              infile_name.c_str(),
                              stdout,
                              &error_msg,
                              &status,
                              &is_smt2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse(d_bzla,
                              nullptr,
                              infile_name.c_str(),
                              stdout,
                              &error_msg,
                              &status,
                              &is_smt2),
               d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_parse(
          d_bzla, infile, nullptr, stdout, &error_msg, &status, &is_smt2),
      d_error_exp_str);
  ASSERT_DEATH(bitwuzla_parse(d_bzla,
                              infile,
                              infile_name.c_str(),
                              stdout,
                              nullptr,
                              &status,
                              &is_smt2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse(d_bzla,
                              infile,
                              infile_name.c_str(),
                              stdout,
                              &error_msg,
                              nullptr,
                              &is_smt2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse(d_bzla,
                              infile,
                              infile_name.c_str(),
                              stdout,
                              &error_msg,
                              &status,
                              nullptr),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse(d_bzla,
                              infile,
                              infile_name.c_str(),
                              stdout,
                              &error_msg,
                              &status,
                              &is_smt2),
               "file parsing after having created expressions is not allowed");

  Bitwuzla *bzla = bitwuzla_new();
  ASSERT_NO_FATAL_FAILURE(bitwuzla_parse(bzla,
                                         infile,
                                         infile_name.c_str(),
                                         stdout,
                                         &error_msg,
                                         &status,
                                         &is_smt2));
  ASSERT_TRUE(is_smt2);
}

TEST_F(TestApi, parse_format)
{
  int32_t status;
  char *error_msg;
  std::string infile_name = "fp_regr1.smt2";
  std::stringstream ss;
  ss << BZLA_OUT_DIR << infile_name;
  FILE *infile = fopen(ss.str().c_str(), "r");

  ASSERT_DEATH(bitwuzla_parse_format(nullptr,
                                     "btor",
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     &status),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse_format(d_bzla,
                                     nullptr,
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     &status),
               d_error_exp_str);
  ASSERT_DEATH(bitwuzla_parse_format(d_bzla,
                                     "smt2",
                                     nullptr,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     &status),
               d_error_not_null);
  ASSERT_DEATH(
      bitwuzla_parse_format(
          d_bzla, "btor", infile, nullptr, stdout, &error_msg, &status),
      d_error_exp_str);
  ASSERT_DEATH(bitwuzla_parse_format(d_bzla,
                                     "smt2",
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     nullptr,
                                     &status),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse_format(d_bzla,
                                     "btor",
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     nullptr),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parse_format(d_bzla,
                                     "smt2",
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     &status),
               "file parsing after having created expressions is not allowed");

  Bitwuzla *bzla = bitwuzla_new();
  ASSERT_DEATH(bitwuzla_parse_format(bzla,
                                     "asdf",
                                     infile,
                                     infile_name.c_str(),
                                     stdout,
                                     &error_msg,
                                     &status),
               d_error_format);
  ASSERT_NO_FATAL_FAILURE(bitwuzla_parse_format(
      bzla, "smt2", infile, infile_name.c_str(), stdout, &error_msg, &status));
}

TEST_F(TestApi, sort_fun_get_domain_sorts)
{
  ASSERT_DEATH(bitwuzla_sort_fun_get_domain_sorts(nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_sort_fun_get_domain_sorts(d_bv_sort32),
               d_error_exp_fun_sort);

  BitwuzlaSort **index_sorts =
      bitwuzla_sort_fun_get_domain_sorts(d_arr_sort_bv);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort32, index_sorts[0]));
  ASSERT_EQ(index_sorts[1], nullptr);

  BitwuzlaSort **domain_sorts =
      bitwuzla_sort_fun_get_domain_sorts(d_fun_sort);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort8, domain_sorts[0]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_fp_sort16, domain_sorts[1]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort32, domain_sorts[2]));
  ASSERT_EQ(domain_sorts[3], nullptr);
}

TEST_F(TestApi, term_fun_get_domain_sorts)
{
  BitwuzlaTerm *bv_term = bitwuzla_mk_const(d_bzla, d_bv_sort32, "bv");

  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(nullptr), d_error_not_null);
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(bv_term),
               "expected function term");

  const BitwuzlaSort **index_sorts =
      bitwuzla_term_fun_get_domain_sorts(d_array);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort32, index_sorts[0]));
  ASSERT_EQ(index_sorts[1], nullptr);

  const BitwuzlaSort **domain_sorts = bitwuzla_term_fun_get_domain_sorts(d_fun);
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort8, domain_sorts[0]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_fp_sort16, domain_sorts[1]));
  ASSERT_TRUE(bitwuzla_sort_is_equal(d_bv_sort32, domain_sorts[2]));
  ASSERT_EQ(domain_sorts[3], nullptr);
}
