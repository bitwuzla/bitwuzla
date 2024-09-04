/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

extern "C" {
#include <bitwuzla/c/bitwuzla.h>
#include <bitwuzla/c/parser.h>
#include <sys/time.h>
}

#include <fstream>

#include "api/c/bitwuzla_structs.h"
#include "test/unit/test.h"

namespace bzla::test {

class TestCApi : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm        = bitwuzla_term_manager_new();
    d_bool_sort = bitwuzla_mk_bool_sort(d_tm);

    d_bv_sort1  = bitwuzla_mk_bv_sort(d_tm, 1);
    d_bv_sort8  = bitwuzla_mk_bv_sort(d_tm, 8);
    d_bv_sort16 = bitwuzla_mk_bv_sort(d_tm, 16);
    d_bv_sort23 = bitwuzla_mk_bv_sort(d_tm, 23);
    d_bv_sort32 = bitwuzla_mk_bv_sort(d_tm, 32);

    d_fp_sort16 = bitwuzla_mk_fp_sort(d_tm, 5, 11);
    d_fp_sort32 = bitwuzla_mk_fp_sort(d_tm, 8, 24);
    d_rm_sort   = bitwuzla_mk_rm_sort(d_tm);
    d_un_sort   = bitwuzla_mk_uninterpreted_sort(d_tm, nullptr);

    d_arr_sort_bvfp = bitwuzla_mk_array_sort(d_tm, d_bv_sort8, d_fp_sort16);
    d_arr_sort_fpbv = bitwuzla_mk_array_sort(d_tm, d_fp_sort16, d_bv_sort8);
    d_arr_sort_bv   = bitwuzla_mk_array_sort(d_tm, d_bv_sort32, d_bv_sort8);

    d_fun_domain_sort = {d_bv_sort8, d_fp_sort16, d_bv_sort32};
    d_fun_sort        = bitwuzla_mk_fun_sort(
        d_tm, d_fun_domain_sort.size(), d_fun_domain_sort.data(), d_bv_sort8);
    d_fun_sort_fp = bitwuzla_mk_fun_sort(
        d_tm, d_fun_domain_sort.size(), d_fun_domain_sort.data(), d_fp_sort16);
    d_true       = bitwuzla_mk_true(d_tm);
    d_bv_one1    = bitwuzla_mk_bv_one(d_tm, d_bv_sort1);
    d_bv_ones23  = bitwuzla_mk_bv_ones(d_tm, d_bv_sort23);
    d_bv_mins8   = bitwuzla_mk_bv_min_signed(d_tm, d_bv_sort8);
    d_bv_maxs8   = bitwuzla_mk_bv_max_signed(d_tm, d_bv_sort8);
    d_bv_zero1   = bitwuzla_mk_bv_zero(d_tm, d_bv_sort1);
    d_bv_zero8   = bitwuzla_mk_bv_zero(d_tm, d_bv_sort8);
    d_fp_pzero32 = bitwuzla_mk_fp_pos_zero(d_tm, d_fp_sort32);
    d_fp_nzero32 = bitwuzla_mk_fp_neg_zero(d_tm, d_fp_sort32);
    d_fp_pinf32  = bitwuzla_mk_fp_pos_inf(d_tm, d_fp_sort32);
    d_fp_ninf32  = bitwuzla_mk_fp_neg_inf(d_tm, d_fp_sort32);
    d_fp_nan32   = bitwuzla_mk_fp_nan(d_tm, d_fp_sort32);

    d_bool_const = bitwuzla_mk_const(d_tm, bitwuzla_mk_bool_sort(d_tm), "b");
    d_bv_const1  = bitwuzla_mk_const(d_tm, d_bv_sort1, "bv1");
    d_bv_const8  = bitwuzla_mk_const(d_tm, d_bv_sort8, "bv8");
    d_fp_const16 = bitwuzla_mk_const(d_tm, d_fp_sort16, "fp16");
    d_rm_const   = bitwuzla_mk_const(d_tm, d_rm_sort, "rm");
    d_un_const   = bitwuzla_mk_const(d_tm, d_un_sort, "u");

    d_rm_rna = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RNA);
    d_rm_rne = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RNE);
    d_rm_rtn = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RTN);
    d_rm_rtp = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RTP);
    d_rm_rtz = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RTZ);

    d_fun        = bitwuzla_mk_const(d_tm, d_fun_sort, "fun");
    d_fun_fp     = bitwuzla_mk_const(d_tm, d_fun_sort_fp, "fun_fp");
    d_array_fpbv = bitwuzla_mk_const(d_tm, d_arr_sort_fpbv, "array_fpbv");
    d_array      = bitwuzla_mk_const(d_tm, d_arr_sort_bv, "array");
    d_store      = bitwuzla_mk_term3(d_tm,
                                BITWUZLA_KIND_ARRAY_STORE,
                                d_array,
                                bitwuzla_mk_const(d_tm, d_bv_sort32, "store"),
                                d_bv_zero8);

    d_var1      = bitwuzla_mk_var(d_tm, d_bv_sort8, "x");
    d_var2      = bitwuzla_mk_var(d_tm, d_bv_sort8, "y");
    d_bound_var = bitwuzla_mk_var(d_tm, d_bv_sort8, "z");
    d_bool_var  = bitwuzla_mk_var(d_tm, bitwuzla_mk_bool_sort(d_tm), "p");

    d_bv_const1_true =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_EQUAL, d_bv_one1, d_bv_const1);
    d_bv_const1_false = bitwuzla_mk_term2(
        d_tm,
        BITWUZLA_KIND_EQUAL,
        d_bv_one1,
        bitwuzla_mk_term1(d_tm, BITWUZLA_KIND_BV_NOT, d_bv_const1));
    d_and_bv_const1 = bitwuzla_mk_term2(
        d_tm,
        BITWUZLA_KIND_EQUAL,
        d_bv_one1,
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_AND, d_bv_one1, d_bv_const1));
    d_eq_bv_const8 =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_EQUAL, d_bv_const8, d_bv_zero8);

    BitwuzlaTerm lambda_body =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, d_bound_var, d_bv_const8);
    d_lambda =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_LAMBDA, d_bound_var, lambda_body);
    d_bool_lambda_body =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_EQUAL, d_bool_var, d_true);
    d_bool_lambda = bitwuzla_mk_term2(
        d_tm, BITWUZLA_KIND_LAMBDA, d_bool_var, d_bool_lambda_body);
    d_bool_apply =
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_APPLY, d_bool_lambda, d_true);

    d_exists_var = bitwuzla_mk_var(d_tm, d_bv_sort8, "q");
    d_exists     = bitwuzla_mk_term2(
        d_tm,
        BITWUZLA_KIND_EXISTS,
        d_exists_var,
        bitwuzla_mk_term2(
            d_tm,
            BITWUZLA_KIND_EQUAL,
            d_bv_zero8,
            bitwuzla_mk_term2(
                d_tm, BITWUZLA_KIND_BV_MUL, d_bv_const8, d_exists_var)));
  }

  void TearDown() override { bitwuzla_term_manager_delete(d_tm); }

  BitwuzlaTermManager *d_tm;

  /* sorts */
  BitwuzlaSort d_arr_sort_bv;
  BitwuzlaSort d_arr_sort_bvfp;
  BitwuzlaSort d_arr_sort_fpbv;
  BitwuzlaSort d_bool_sort;
  BitwuzlaSort d_bv_sort1;
  BitwuzlaSort d_bv_sort8;
  BitwuzlaSort d_bv_sort16;
  BitwuzlaSort d_bv_sort23;
  BitwuzlaSort d_bv_sort32;
  BitwuzlaSort d_fp_sort16;
  BitwuzlaSort d_fp_sort32;
  BitwuzlaSort d_fun_sort;
  BitwuzlaSort d_fun_sort_fp;
  std::vector<BitwuzlaSort> d_fun_domain_sort;
  BitwuzlaSort d_rm_sort;
  BitwuzlaSort d_un_sort;

  /* terms */
  BitwuzlaTerm d_true;
  BitwuzlaTerm d_bv_one1;
  BitwuzlaTerm d_bv_ones23;
  BitwuzlaTerm d_bv_zero1;
  BitwuzlaTerm d_bv_zero8;
  BitwuzlaTerm d_bv_mins8;
  BitwuzlaTerm d_bv_maxs8;
  BitwuzlaTerm d_fp_pzero32;
  BitwuzlaTerm d_fp_nzero32;
  BitwuzlaTerm d_fp_pinf32;
  BitwuzlaTerm d_fp_ninf32;
  BitwuzlaTerm d_fp_nan32;

  BitwuzlaTerm d_bool_const;
  BitwuzlaTerm d_bv_const1;
  BitwuzlaTerm d_bv_const8;
  BitwuzlaTerm d_fp_const16;
  BitwuzlaTerm d_rm_const;
  BitwuzlaTerm d_un_const;

  BitwuzlaTerm d_rm_rna;
  BitwuzlaTerm d_rm_rne;
  BitwuzlaTerm d_rm_rtn;
  BitwuzlaTerm d_rm_rtp;
  BitwuzlaTerm d_rm_rtz;

  BitwuzlaTerm d_fun;
  BitwuzlaTerm d_fun_fp;
  BitwuzlaTerm d_array_fpbv;
  BitwuzlaTerm d_array;
  BitwuzlaTerm d_store;

  BitwuzlaTerm d_var1;
  BitwuzlaTerm d_var2;
  BitwuzlaTerm d_bound_var;
  BitwuzlaTerm d_bool_var;

  BitwuzlaTerm d_bv_const1_true;
  BitwuzlaTerm d_bv_const1_false;
  BitwuzlaTerm d_and_bv_const1;
  BitwuzlaTerm d_eq_bv_const8;
  BitwuzlaTerm d_lambda;
  BitwuzlaTerm d_bool_lambda;
  BitwuzlaTerm d_bool_lambda_body;
  BitwuzlaTerm d_bool_apply;

  BitwuzlaTerm d_exists_var;
  BitwuzlaTerm d_exists;

  /* error messages */
  const char *d_error_not_null = "expected non-null object";
  const char *d_error_solver   = "is not associated with given solver instance";
  const char *d_error_inv_sort = "invalid sort";
  const char *d_error_exp_arr_sort   = "expected array sort";
  const char *d_error_exp_bv_sort    = "expected bit-vector sort";
  const char *d_error_exp_fp_sort    = "expected floating-point sort";
  const char *d_error_exp_fun_sort   = "expected function sort";
  const char *d_error_exp_str        = "must not be an empty string";
  const char *d_error_unexp_arr_sort = "unexpected array sort";
  const char *d_error_unexp_fun_sort = "unexpected function sort";
  const char *d_error_zero           = "must be > 0";
  const char *d_error_bv_fit         = "does not fit into a bit-vector of size";
  const char *d_error_inv_term       = "invalid term";
  const char *d_error_exp_bool_term  = "expected Boolean term";
  const char *d_error_exp_bv_term    = "expected bit-vector term";
  const char *d_error_exp_bv_value   = "expected bit-vector value";
  const char *d_error_exp_fp_term    = "expected floating-point term";
  const char *d_error_exp_rm_term    = "expected rounding-mode term";
  const char *d_error_exp_arr_term   = "expected array term";
  const char *d_error_exp_fun_term   = "expected function term";
  const char *d_error_exp_var_term   = "expected variable";
  const char *d_error_exp_assumption = "must be an assumption";
  const char *d_error_rm             = "invalid rounding mode";
  const char *d_error_unexp_arr_term = "unexpected array term";
  const char *d_error_unexp_fun_term = "expected non-function term";
  const char *d_error_unexp_param_term = "term must not be parameterized";
  const char *d_error_produce_models   = "model production not enabled";
  const char *d_error_unsat            = "if input formula is not unsat";
  const char *d_error_unsat_cores      = "unsat core production not enabled";
  const char *d_error_sat              = "if input formula is not sat";
  const char *d_error_model_quant =
      "model printing is currently not supported with quantifiers";
};

/* -------------------------------------------------------------------------- */
/* BitwuzlaKind                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, kind_to_string)
{
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_CONSTANT),
            std::string("BITWUZLA_KIND_CONSTANT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_CONST_ARRAY),
            std::string("BITWUZLA_KIND_CONST_ARRAY"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_VARIABLE),
            std::string("BITWUZLA_KIND_VARIABLE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_VALUE),
            std::string("BITWUZLA_KIND_VALUE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_AND),
            std::string("BITWUZLA_KIND_AND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_APPLY),
            std::string("BITWUZLA_KIND_APPLY"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_ARRAY_SELECT),
            std::string("BITWUZLA_KIND_SELECT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_ARRAY_STORE),
            std::string("BITWUZLA_KIND_STORE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ADD),
            std::string("BITWUZLA_KIND_BV_ADD"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_AND),
            std::string("BITWUZLA_KIND_BV_AND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ASHR),
            std::string("BITWUZLA_KIND_BV_ASHR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_COMP),
            std::string("BITWUZLA_KIND_BV_COMP"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_CONCAT),
            std::string("BITWUZLA_KIND_BV_CONCAT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_DEC),
            std::string("BITWUZLA_KIND_BV_DEC"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_INC),
            std::string("BITWUZLA_KIND_BV_INC"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_MUL),
            std::string("BITWUZLA_KIND_BV_MUL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_NAND),
            std::string("BITWUZLA_KIND_BV_NAND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_NEG),
            std::string("BITWUZLA_KIND_BV_NEG"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_NOR),
            std::string("BITWUZLA_KIND_BV_NOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_NOT),
            std::string("BITWUZLA_KIND_BV_NOT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_OR),
            std::string("BITWUZLA_KIND_BV_OR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_REDAND),
            std::string("BITWUZLA_KIND_BV_REDAND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_REDOR),
            std::string("BITWUZLA_KIND_BV_REDOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_REDXOR),
            std::string("BITWUZLA_KIND_BV_REDXOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ROL),
            std::string("BITWUZLA_KIND_BV_ROL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ROR),
            std::string("BITWUZLA_KIND_BV_ROR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SADD_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_SADDO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SDIV_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_SDIVO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SDIV),
            std::string("BITWUZLA_KIND_BV_SDIV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SGE),
            std::string("BITWUZLA_KIND_BV_SGE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SGT),
            std::string("BITWUZLA_KIND_BV_SGT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SHL),
            std::string("BITWUZLA_KIND_BV_SHL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SHR),
            std::string("BITWUZLA_KIND_BV_SHR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SLE),
            std::string("BITWUZLA_KIND_BV_SLE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SLT),
            std::string("BITWUZLA_KIND_BV_SLT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SMOD),
            std::string("BITWUZLA_KIND_BV_SMOD"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SMUL_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_SMULO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SREM),
            std::string("BITWUZLA_KIND_BV_SREM"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SSUB_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_SSUBO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SUB),
            std::string("BITWUZLA_KIND_BV_SUB"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UADD_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_UADDO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UDIV),
            std::string("BITWUZLA_KIND_BV_UDIV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UGE),
            std::string("BITWUZLA_KIND_BV_UGE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UGT),
            std::string("BITWUZLA_KIND_BV_UGT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ULE),
            std::string("BITWUZLA_KIND_BV_ULE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ULT),
            std::string("BITWUZLA_KIND_BV_ULT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UMUL_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_UMULO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_UREM),
            std::string("BITWUZLA_KIND_BV_UREM"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_USUB_OVERFLOW),
            std::string("BITWUZLA_KIND_BV_USUBO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_XNOR),
            std::string("BITWUZLA_KIND_BV_XNOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_XOR),
            std::string("BITWUZLA_KIND_BV_XOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_DISTINCT),
            std::string("BITWUZLA_KIND_DISTINCT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_EQUAL),
            std::string("BITWUZLA_KIND_EQUAL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_EXISTS),
            std::string("BITWUZLA_KIND_EXISTS"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FORALL),
            std::string("BITWUZLA_KIND_FORALL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_ABS),
            std::string("BITWUZLA_KIND_FP_ABS"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_ADD),
            std::string("BITWUZLA_KIND_FP_ADD"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_DIV),
            std::string("BITWUZLA_KIND_FP_DIV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_EQUAL),
            std::string("BITWUZLA_KIND_FP_EQUAL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_FMA),
            std::string("BITWUZLA_KIND_FP_FMA"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_FP),
            std::string("BITWUZLA_KIND_FP_FP"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_GEQ),
            std::string("BITWUZLA_KIND_FP_GEQ"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_GT),
            std::string("BITWUZLA_KIND_FP_GT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_INF),
            std::string("BITWUZLA_KIND_FP_IS_INF"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_NAN),
            std::string("BITWUZLA_KIND_FP_IS_NAN"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_NEG),
            std::string("BITWUZLA_KIND_FP_IS_NEG"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_NORMAL),
            std::string("BITWUZLA_KIND_FP_IS_NORMAL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_POS),
            std::string("BITWUZLA_KIND_FP_IS_POS"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_SUBNORMAL),
            std::string("BITWUZLA_KIND_FP_IS_SUBNORMAL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_IS_ZERO),
            std::string("BITWUZLA_KIND_FP_IS_ZERO"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_LEQ),
            std::string("BITWUZLA_KIND_FP_LEQ"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_LT),
            std::string("BITWUZLA_KIND_FP_LT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_MAX),
            std::string("BITWUZLA_KIND_FP_MAX"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_MIN),
            std::string("BITWUZLA_KIND_FP_MIN"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_MUL),
            std::string("BITWUZLA_KIND_FP_MUL"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_NEG),
            std::string("BITWUZLA_KIND_FP_NEG"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_REM),
            std::string("BITWUZLA_KIND_FP_REM"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_RTI),
            std::string("BITWUZLA_KIND_FP_RTI"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_SQRT),
            std::string("BITWUZLA_KIND_FP_SQRT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_SUB),
            std::string("BITWUZLA_KIND_FP_SUB"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_IFF),
            std::string("BITWUZLA_KIND_IFF"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_IMPLIES),
            std::string("BITWUZLA_KIND_IMPLIES"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_ITE),
            std::string("BITWUZLA_KIND_ITE"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_LAMBDA),
            std::string("BITWUZLA_KIND_LAMBDA"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_NOT),
            std::string("BITWUZLA_KIND_NOT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_OR),
            std::string("BITWUZLA_KIND_OR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_XOR),
            std::string("BITWUZLA_KIND_XOR"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_EXTRACT),
            std::string("BITWUZLA_KIND_BV_EXTRACT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_REPEAT),
            std::string("BITWUZLA_KIND_BV_REPEAT"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ROLI),
            std::string("BITWUZLA_KIND_BV_ROLI"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_RORI),
            std::string("BITWUZLA_KIND_BV_RORI"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_SIGN_EXTEND),
            std::string("BITWUZLA_KIND_BV_SIGN_EXTEND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_BV_ZERO_EXTEND),
            std::string("BITWUZLA_KIND_BV_ZERO_EXTEND"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_FP_FROM_BV),
            std::string("BITWUZLA_KIND_FP_TO_FP_FROM_BV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_FP_FROM_FP),
            std::string("BITWUZLA_KIND_FP_TO_FP_FROM_FP"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_FP_FROM_SBV),
            std::string("BITWUZLA_KIND_FP_TO_FP_FROM_SBV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_FP_FROM_UBV),
            std::string("BITWUZLA_KIND_FP_TO_FP_FROM_UBV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_SBV),
            std::string("BITWUZLA_KIND_FP_TO_SBV"));
  ASSERT_EQ(bitwuzla_kind_to_string(BITWUZLA_KIND_FP_TO_UBV),
            std::string("BITWUZLA_KIND_FP_TO_UBV"));
  ASSERT_DEATH(bitwuzla_kind_to_string(BITWUZLA_KIND_NUM_KINDS),
               std::string("invalid term kind"));
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, rm_to_string)
{
  ASSERT_EQ(bitwuzla_rm_to_string(BITWUZLA_RM_RNA),
            std::string("BITWUZLA_RM_RNA"));
  ASSERT_EQ(bitwuzla_rm_to_string(BITWUZLA_RM_RNE),
            std::string("BITWUZLA_RM_RNE"));
  ASSERT_EQ(bitwuzla_rm_to_string(BITWUZLA_RM_RTN),
            std::string("BITWUZLA_RM_RTN"));
  ASSERT_EQ(bitwuzla_rm_to_string(BITWUZLA_RM_RTP),
            std::string("BITWUZLA_RM_RTP"));
  ASSERT_EQ(bitwuzla_rm_to_string(BITWUZLA_RM_RTZ),
            std::string("BITWUZLA_RM_RTZ"));
  ASSERT_DEATH(bitwuzla_rm_to_string(BITWUZLA_RM_MAX),
               std::string("invalid rounding mode"));
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, result_to_string)
{
  ASSERT_EQ(bitwuzla_result_to_string(BITWUZLA_SAT), std::string("sat"));
  ASSERT_EQ(bitwuzla_result_to_string(BITWUZLA_UNSAT), std::string("unsat"));
  ASSERT_EQ(bitwuzla_result_to_string(BITWUZLA_UNKNOWN),
            std::string("unknown"));
  ASSERT_DEATH(bitwuzla_result_to_string((BitwuzlaResult) 1),
               std::string("invalid result"));
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaOptions                                                            */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, set_option)
{
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    ASSERT_DEATH(bitwuzla_set_option(options, BITWUZLA_OPT_VERBOSITY, 5),
                 "expected value <=");
    //  ASSERT_DEATH(bitwuzla_set_option(
    //                   options, BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION,
    //                   1),
    //               "unconstrained optimization cannot be enabled in
    //               incremental " "mode");
    bitwuzla_options_delete(options);
  }
  //{
  //  BitwuzlaOptions *options = bitwuzla_options_new();
  //  bitwuzla_set_option(options, BITWUZLA_OPT_FUN_DUAL_PROP, 1);
  //  ASSERT_DEATH(bitwuzla_set_option(options, BITWUZLA_OPT_FUN_JUST, 1),
  //               "enabling multiple optimization techniques is not allowed");
  //  ASSERT_DEATH(
  //      bitwuzla_set_option(options, BITWUZLA_OPT_PP_NONDESTR_SUBST, 1),
  //      "non-destructive substitution is not supported with dual
  //      propagation");
  //  bitwuzla_options_delete(options);
  //}
  //{
  //  BitwuzlaOptions *options = bitwuzla_options_new();
  //  bitwuzla_set_option(options, BITWUZLA_OPT_FUN_JUST, 1);
  //  ASSERT_DEATH(bitwuzla_set_option(options, BITWUZLA_OPT_FUN_DUAL_PROP, 1),
  //               "enabling multiple optimization techniques is not allowed");
  //  bitwuzla_options_delete(options);
  //}
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    // ASSERT_DEATH(bitwuzla_set_option(
    //                  options, BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION, 1),
    //              "unconstrained optimization cannot be enabled if model "
    //              "generation is enabled");
    bitwuzla_options_delete(options);
  }
  //{
  //  BitwuzlaOptions *options = bitwuzla_options_new();
  //  bitwuzla_set_option(options, BITWUZLA_OPT_PP_NONDESTR_SUBST, 1);
  //  ASSERT_DEATH(
  //      bitwuzla_set_option(options, BITWUZLA_OPT_FUN_DUAL_PROP, 1),
  //      "non-destructive substitution is not supported with dual
  //      propagation");
  //  bitwuzla_options_delete(options);
  //}
  //{
  //  BitwuzlaOptions *options = bitwuzla_options_new();
  //  bitwuzla_set_option(
  //    options, BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION, 1);
  //  ASSERT_DEATH(bitwuzla_set_option(options, BITWUZLA_OPT_INCREMENTAL, 1),
  //               "incremental solving cannot be enabled if unconstrained "
  //               "optimization is enabled");
  //  ASSERT_DEATH(bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1),
  //               "model generation cannot be enabled if unconstrained "
  //               "optimization is enabled");
  //  bitwuzla_options_delete(options);
  //}
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    ASSERT_EQ(bitwuzla_get_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_CORES),
              0);
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_CORES, 1);
    ASSERT_EQ(bitwuzla_get_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_CORES),
              1);
    ASSERT_EQ(bitwuzla_get_option(options, BITWUZLA_OPT_VERBOSITY), 0);
    bitwuzla_set_option(options, BITWUZLA_OPT_VERBOSITY, 2);
    ASSERT_EQ(bitwuzla_get_option(options, BITWUZLA_OPT_VERBOSITY), 2);
    ASSERT_EQ(
        std::string(bitwuzla_get_option_mode(options, BITWUZLA_OPT_BV_SOLVER)),
        "bitblast");
    bitwuzla_set_option_mode(options, BITWUZLA_OPT_BV_SOLVER, "prop");
    ASSERT_EQ(
        std::string(bitwuzla_get_option_mode(options, BITWUZLA_OPT_BV_SOLVER)),
        "prop");
    bitwuzla_set_option_mode(options, BITWUZLA_OPT_BV_SOLVER, "bitblast");
    ASSERT_EQ(
        std::string(bitwuzla_get_option_mode(options, BITWUZLA_OPT_BV_SOLVER)),
        "bitblast");
    bitwuzla_set_option_mode(options, BITWUZLA_OPT_SAT_SOLVER, "cadical");
    ASSERT_EQ(
        std::string(bitwuzla_get_option_mode(options, BITWUZLA_OPT_SAT_SOLVER)),
        "cadical");
    ASSERT_DEATH(
        bitwuzla_set_option_mode(options, BITWUZLA_OPT_BV_SOLVER, "asdf"),
        "invalid mode for option");
    bitwuzla_options_delete(options);
  }
}

TEST_F(TestCApi, option_info)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaOptionInfo info;

  for (int32_t i = 0; i < BITWUZLA_OPT_NUM_OPTS; ++i)
  {
    BitwuzlaOption opt = static_cast<BitwuzlaOption>(i);
    bitwuzla_get_option_info(options, opt, &info);
    if (info.is_numeric)
    {
      ASSERT_EQ(info.numeric.cur, bitwuzla_get_option(options, opt));
      ASSERT_GE(info.numeric.cur, info.numeric.min);
      ASSERT_LE(info.numeric.cur, info.numeric.max);
    }
    else
    {
      ASSERT_EQ(std::string(bitwuzla_get_option_mode(options, opt)),
                std::string(info.mode.cur));
      size_t nmodes      = info.mode.num_modes;
      const char **modes = info.mode.modes;
      bool in_modes      = false;
      for (size_t i = 0; i < nmodes; ++i)
      {
        if (std::string(modes[i]) == std::string(info.mode.cur))
        {
          in_modes = true;
          break;
        }
      }
      ASSERT_TRUE(in_modes);
    }
    ASSERT_TRUE(info.description && !std::string(info.description).empty());
  }
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, option_is_valid)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  ASSERT_FALSE(bitwuzla_option_is_valid(options, "incremental"));
  ASSERT_TRUE(bitwuzla_option_is_valid(options, "produce-models"));
  bitwuzla_options_delete(options);
}

/* -------------------------------------------------------------------------- */
/* Create Sorts                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, mk_array_sort)
{
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_tm, 0, d_bv_sort8), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_tm, d_bv_sort1, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_array_sort(d_tm, d_arr_sort_bv, d_bv_sort8),
               "array sorts not supported as index");

  bitwuzla_mk_array_sort(d_tm, d_bv_sort8, d_arr_sort_bv);
  bitwuzla_mk_array_sort(d_tm, d_fun_sort, d_bv_sort8);
  bitwuzla_mk_array_sort(d_tm, d_bv_sort8, d_fun_sort);
}

TEST_F(TestCApi, mk_bool_sort) { bitwuzla_mk_bool_sort(d_tm); }

TEST_F(TestCApi, mk_bv_sort)
{
  ASSERT_DEATH(bitwuzla_mk_bv_sort(d_tm, 0), d_error_zero);
}

TEST_F(TestCApi, mk_fp_sort)
{
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_tm, 0, 8),
               "argument 'exp_size' must be > 1");
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_tm, 5, 0),
               "argument 'sig_size' must be > 1");
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_tm, 1, 2),
               "argument 'exp_size' must be > 1");
  ASSERT_DEATH(bitwuzla_mk_fp_sort(d_tm, 2, 1),
               "argument 'sig_size' must be > 1");
}

TEST_F(TestCApi, mk_fun_sort)
{
  ASSERT_DEATH(
      bitwuzla_mk_fun_sort(d_tm, d_fun_domain_sort.size(), 0, d_bv_sort8),
      d_error_not_null);
  std::vector<BitwuzlaSort> empty = {};
  ASSERT_DEATH(
      bitwuzla_mk_fun_sort(d_tm, empty.size(), empty.data(), d_bv_sort8),
      d_error_not_null);
}

TEST_F(TestCApi, mk_rm_sort) { bitwuzla_mk_rm_sort(d_tm); }

TEST_F(TestCApi, mk_uninterpreted_sort)
{
  BitwuzlaSort s1 = bitwuzla_mk_uninterpreted_sort(d_tm, nullptr);
  BitwuzlaSort s2 = bitwuzla_mk_uninterpreted_sort(d_tm, "foo");
  BitwuzlaSort s3 = bitwuzla_mk_uninterpreted_sort(d_tm, "foo");
  ASSERT_TRUE(bitwuzla_sort_is_uninterpreted(s1));
  ASSERT_TRUE(bitwuzla_sort_is_uninterpreted(s2));
  ASSERT_TRUE(bitwuzla_sort_is_uninterpreted(s3));
  ASSERT_NE(s1, s2);
  ASSERT_NE(s1, s3);
  ASSERT_NE(s2, s3);
}

/* -------------------------------------------------------------------------- */
/* Create Terms                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, mk_true) { bitwuzla_mk_true(d_tm); }

TEST_F(TestCApi, mk_false) { bitwuzla_mk_false(d_tm); }

TEST_F(TestCApi, mk_bv_zero)
{
  ASSERT_DEATH(bitwuzla_mk_bv_zero(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_zero(d_tm, d_fp_sort16), d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_bv_one)
{
  ASSERT_DEATH(bitwuzla_mk_bv_one(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_one(d_tm, d_fp_sort16), d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_bv_ones)
{
  ASSERT_DEATH(bitwuzla_mk_bv_ones(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_ones(d_tm, d_fp_sort16), d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_bv_min_signed)
{
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_min_signed(d_tm, d_fp_sort16),
               d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_bv_max_signed)
{
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_max_signed(d_tm, d_fp_sort16),
               d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_fp_pos_zero)
{
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_zero(d_tm, d_bv_sort8), d_error_exp_fp_sort);
}

TEST_F(TestCApi, mk_fp_neg_zero)
{
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_zero(d_tm, d_bv_sort8), d_error_exp_fp_sort);
}

TEST_F(TestCApi, mk_fp_pos_inf)
{
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_pos_inf(d_tm, d_bv_sort8), d_error_exp_fp_sort);
}

TEST_F(TestCApi, mk_fp_neg_inf)
{
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_neg_inf(d_tm, d_bv_sort8), d_error_exp_fp_sort);
}

TEST_F(TestCApi, mk_fp_nan)
{
  ASSERT_DEATH(bitwuzla_mk_fp_nan(d_tm, 0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_fp_nan(d_tm, d_bv_sort8), d_error_exp_fp_sort);
}

TEST_F(TestCApi, mk_bv_value)
{
  bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "127", 10);
  bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-128", 10);
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "256", 10),
               "does not fit into");
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-129", 10),
               "does not fit into");
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-128", 12),
               "invalid base");

  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, nullptr, "010", 2), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, nullptr, 2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "", 2), d_error_exp_str);

  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_fp_sort16, "010", 2),
               d_error_exp_bv_sort);

  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "11111111010", 2),
               d_error_bv_fit);
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "1234567890", 10),
               d_error_bv_fit);
  ASSERT_DEATH(
      bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "1234567890aAbBcCdDeEfF", 16),
      d_error_bv_fit);
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "1234567890", 2),
               "invalid binary string");
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "12z4567890", 10),
               "invalid decimal string");
  ASSERT_DEATH(bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "12z4567890", 16),
               "invalid hexadecimal string");
}

TEST_F(TestCApi, mk_bv_value_uint64)
{
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(d_tm, 0, 23), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_bv_value_uint64(d_tm, d_fp_sort16, 23),
               d_error_exp_bv_sort);
}

TEST_F(TestCApi, mk_fp_value)
{
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, 0, d_bv_zero8, d_bv_zero8),
               d_error_inv_term);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, 0, d_bv_zero8),
               d_error_inv_term);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, d_bv_zero8, 0),
               d_error_inv_term);

  ASSERT_DEATH(
      bitwuzla_mk_fp_value(d_tm, d_bv_zero8, d_bv_zero8, d_bv_zero8),
      "invalid bit-vector size for argument 'bv_sign', expected size 1");
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_fp_const16, d_bv_zero8, d_bv_zero8),
               d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, d_fp_const16, d_bv_zero8),
               d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, d_bv_zero8, d_fp_const16),
               d_error_exp_bv_value);

  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_const1, d_bv_zero8, d_bv_zero8),
               d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, d_bv_const8, d_bv_zero8),
               d_error_exp_bv_value);
  ASSERT_DEATH(bitwuzla_mk_fp_value(d_tm, d_bv_one1, d_bv_zero8, d_bv_const8),
               d_error_exp_bv_value);
}

TEST_F(TestCApi, mk_rm_value)
{
  ASSERT_DEATH(bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_MAX), d_error_rm);
}

TEST_F(TestCApi, mk_term_check_null)
{
  std::vector<BitwuzlaTerm> bv_args2 = {d_bv_zero8, d_bv_const8};

  std::vector<BitwuzlaTerm> null_death_args1 = {0};
  std::vector<BitwuzlaTerm> null_death_args2 = {d_bv_zero8, 0};
  std::vector<BitwuzlaTerm> null_death_args3 = {d_rm_const, 0, d_fp_const16};

  // mk_term
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NOT,
                                null_death_args1.size(),
                                null_death_args1.data()),
               d_error_inv_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_AND,
                                null_death_args2.size(),
                                null_death_args2.data()),
               d_error_inv_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_ADD,
                                null_death_args3.size(),
                                null_death_args3.data()),
               d_error_inv_term);
  // mk_term1
  ASSERT_DEATH(bitwuzla_mk_term1(d_tm, BITWUZLA_KIND_BV_NOT, 0),
               d_error_inv_term);
  // mk_term2
  ASSERT_DEATH(bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_AND, 0, d_bv_const8),
               d_error_inv_term);
  // mk_term3
  ASSERT_DEATH(bitwuzla_mk_term3(
                   d_tm, BITWUZLA_KIND_FP_ADD, 0, d_fp_const16, d_fp_const16),
               d_error_inv_term);
}

TEST_F(TestCApi, mk_term_check_cnt)
{
  const char *error_arg_cnt = "invalid number of arguments";

  std::vector<BitwuzlaTerm> apply_args1 = {d_bv_one1};
  std::vector<BitwuzlaTerm> apply_args2 = {d_fun, d_bv_const8};
  std::vector<BitwuzlaTerm> array_args1 = {d_array_fpbv};
  std::vector<BitwuzlaTerm> bool_args1  = {d_true};
  std::vector<BitwuzlaTerm> bool_args2  = {d_true, d_true};
  std::vector<BitwuzlaTerm> bv_args1    = {d_bv_one1};
  std::vector<BitwuzlaTerm> bv_args1_rm = {d_rm_const};
  std::vector<BitwuzlaTerm> bv_args2    = {d_bv_zero8, d_bv_const8};
  std::vector<BitwuzlaTerm> ite_args2   = {d_true, d_bv_const8};
  std::vector<BitwuzlaTerm> fp_args1    = {d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args1_rm = {d_rm_const};
  std::vector<BitwuzlaTerm> fp_args2    = {d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args2_rm = {d_rm_const, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args3_rm = {
      d_rm_const, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> fun_args1 = {d_var1};

  std::vector<uint64_t> idxs1    = {1};
  std::vector<uint64_t> idxs2    = {2, 0};
  std::vector<uint64_t> fp_idxs1 = {5, 8};

  // bool
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_AND, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_IFF, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_IMPLIES, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_NOT, bool_args2.size(), bool_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_OR, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_XOR, bool_args1.size(), bool_args1.data()),
      error_arg_cnt);

  // bit-vectors
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_APPLY, apply_args1.size(), apply_args1.data()),
      "expected at least two arguments");
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_APPLY, apply_args2.size(), apply_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_args1.size(),
                                array_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_args1.size(),
                                array_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ADD, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_AND, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ASHR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_CONCAT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_DEC, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_INC, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_MUL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_NAND, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_NEG, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_NOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_NOT, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_BV_OR, bv_args1.size(), bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_REDAND, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_REDOR, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_REDXOR, bv_args2.size(), bv_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_BV_OR, bv_args1.size(), bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ROL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ROR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SDIV, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SGE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SGT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SHL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SHR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SLE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SLT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SMOD, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SREM, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SUB, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UDIV, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UGE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UGT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ULE, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ULT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UREM, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args1.size(),
                                bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_XNOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_XOR, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);

  // floating-point
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_ABS, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_ADD, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_DIV, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_EQUAL, fp_args1_rm.size(), fp_args1_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_FMA, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_FP_FP, fp_args2.size(), fp_args2.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_GEQ, fp_args1.size(), fp_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_FP_GT, fp_args1.size(), fp_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_INF, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_NAN, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_NEG, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_NORMAL, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_POS, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_SUBNORMAL,
                                fp_args2.size(),
                                fp_args2.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_ZERO, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_LEQ, fp_args1.size(), fp_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_FP_LT, fp_args1.size(), fp_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_MAX, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_MIN, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_IS_ZERO, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_MUL, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_REM, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_RTI, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_SQRT, fp_args3_rm.size(), fp_args3_rm.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_SUB, fp_args2.size(), fp_args2.data()),
      error_arg_cnt);

  // others
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_DISTINCT, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_EQUAL, bv_args1.size(), bv_args1.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_EXISTS, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FORALL, bv_args1.size(), bv_args1.data()),
      error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term(
                   d_tm, BITWUZLA_KIND_ITE, ite_args2.size(), ite_args2.data()),
               error_arg_cnt);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_LAMBDA, fun_args1.size(), fun_args1.data()),
      error_arg_cnt);

  // indexed
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs2.size(),
                                        idxs2.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_REPEAT,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_ROLI,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_RORI,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args2.size(),
                                        bv_args2.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args3_rm.size(),
                                        fp_args3_rm.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                                        bv_args1_rm.size(),
                                        bv_args1_rm.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                        bv_args1_rm.size(),
                                        bv_args1_rm.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args1.size(),
                                        fp_args1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args1.size(),
                                        fp_args1.data(),
                                        idxs1.size(),
                                        idxs1.data()),
               error_arg_cnt);
}

TEST_F(TestCApi, mk_term_check_args)
{
  const char *error_invalid_sort = "unexpected sort";
  const char *error_mis_sort  = "mismatching sort";
  // const char *error_bvar_term = "expected unbound variable term";
  const char *error_dvar_term    = "expected set of distinct variables";
  const char *error_fp_size      = "must be > 1";

  const char *error_arr_index_sort =
      "sort of index term does not match index sort of array";
  const char *error_arr_element_sort =
      "sort of element term does not match element sort of array";

  std::vector<BitwuzlaTerm> array_select_args2_invalid_1 = {d_fp_const16,
                                                            d_array_fpbv};
  std::vector<BitwuzlaTerm> array_select_args2_invalid_2 = {d_array_fpbv,
                                                            d_bv_const8};

  std::vector<BitwuzlaTerm> array_store_args3_invalid_1 = {
      d_fp_const16, d_array_fpbv, d_bv_const8};
  std::vector<BitwuzlaTerm> array_store_args3_invalid_2 = {
      d_array_fpbv, d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm> array_store_args3_invalid_3 = {
      d_array_fpbv, d_fp_const16, d_fp_const16};

  std::vector<BitwuzlaTerm> apply_args3_invalid_1 = {d_fun, d_bv_const8, d_fun};
  std::vector<BitwuzlaTerm> apply_args3_invalid_2 = {
      d_fun, d_bv_const8, d_bv_const8, d_fp_pzero32};

  std::vector<BitwuzlaTerm> bool_args1_invalid = {d_bv_const8};
  std::vector<BitwuzlaTerm> bool_args2_invalid = {d_fp_pzero32, d_fp_pzero32};
  std::vector<BitwuzlaTerm> bool_args2_mis     = {d_true, d_bv_const8};

  std::vector<BitwuzlaTerm> bv_args1         = {d_bv_const8};
  std::vector<BitwuzlaTerm> bv_args1_invalid = {d_fp_const16};
  std::vector<BitwuzlaTerm> bv_args2_invalid = {d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> bv_args2_mis     = {d_bv_one1, d_bv_const8};
  std::vector<BitwuzlaTerm> bv_args2_rm      = {d_rm_const, d_bv_const8};
  std::vector<BitwuzlaTerm> bv_args2_rm_invalid_1 = {d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm> bv_args2_rm_invalid_2 = {d_rm_const, d_fp_const16};

  std::vector<BitwuzlaTerm> ite_death_args3_1 = {
      d_true, d_bv_const8, d_bv_one1};
  std::vector<BitwuzlaTerm> ite_args3_invalid_2 = {
      d_bv_const8, d_bv_const8, d_bv_const8};

  std::vector<BitwuzlaTerm> lambda_args2_invalid_1 = {d_bv_const8, d_bv_const8};
  std::vector<BitwuzlaTerm> lambda_args2           = {d_bound_var, d_bv_const8};
  std::vector<BitwuzlaTerm> lambda_args3_invalid_1 = {
      d_var1, d_var1, d_bv_const8};

  BitwuzlaTerm lambda_body =
      bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, d_var2, d_bv_const8);
  std::vector<BitwuzlaTerm> lambda_args3 = {
      d_var1,
      d_var2,
      bitwuzla_mk_term2_indexed2(d_tm,
                                 BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                 d_rm_const,
                                 lambda_body,
                                 5,
                                 8)};

  std::vector<BitwuzlaTerm> fp_args2_rm = {d_rm_const, d_fp_const16};

  std::vector<BitwuzlaTerm> fp_args1_invalid = {d_bv_one1};
  std::vector<BitwuzlaTerm> fp_args2_invalid = {d_bv_zero8, d_bv_const8};
  std::vector<BitwuzlaTerm> fp_args2_mis     = {d_fp_pzero32, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args2_rm_invalid_1 = {d_bv_const8, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args2_rm_invalid_2 = {d_rm_const, d_bv_const8};
  std::vector<BitwuzlaTerm> fp_args3_rm_mis       = {
            d_rm_const, d_fp_pzero32, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args3_rm_invalid_1 = {
      d_fp_const16, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args3_rm_invalid_2 = {
      d_rm_const, d_bv_zero8, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args4_mis = {
      d_rm_const, d_fp_pzero32, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args4_rm_invalid_1 = {
      d_rm_const, d_bv_zero8, d_fp_const16, d_fp_const16};
  std::vector<BitwuzlaTerm> fp_args4_rm_invalid_2 = {
      d_fp_const16, d_fp_const16, d_fp_const16, d_fp_const16};

  std::vector<BitwuzlaTerm> fp_fp_args3_invalid_1 = {
      d_bv_const8, d_bv_zero8, d_bv_ones23};
  std::vector<BitwuzlaTerm> fp_fp_args3_invalid_2 = {
      d_bv_one1, d_fp_pzero32, d_bv_ones23};
  std::vector<BitwuzlaTerm> fp_fp_args3_invalid_3 = {
      d_bv_one1, d_bv_zero8, d_fp_pzero32};
  std::vector<BitwuzlaTerm> fp_fp_args3_invalid_4 = {
      d_fp_pzero32, d_bv_zero8, d_bv_ones23};

  std::vector<BitwuzlaTerm> quant_args2_invalid_1 = {d_true, d_true};
  std::vector<BitwuzlaTerm> quant_args2_invalid_2 = {d_var1, d_bv_const8};
  std::vector<BitwuzlaTerm> quant_args2_invalid_3 = {d_bound_var, d_bv_const8};
  std::vector<BitwuzlaTerm> quant_args3_invalid   = {
        d_var1, d_var1, d_bool_const};

  std::vector<uint64_t> bv_idxs1                 = {3};
  std::vector<uint64_t> bv_idxs2                 = {2, 0};
  std::vector<uint64_t> bv_extract_death_idxs2_1 = {0, 2};
  std::vector<uint64_t> bv_extract_death_idxs2_2 = {9, 0};
  std::vector<uint64_t> bv_repeat_idxs_invalid_1 = {2305843009213693953};
  std::vector<uint64_t> bv_extend_idxs_invalid_1 = {UINT64_MAX};
  std::vector<uint64_t> fp_idxs1                 = {5, 8};
  std::vector<uint64_t> fp_idxs2                 = {1, 8};
  std::vector<uint64_t> fp_idxs3                 = {5, 1};

  // bool
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_AND,
                                bool_args2_invalid.size(),
                                bool_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_AND,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_IFF,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_IFF,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_IMPLIES,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_IMPLIES,
                                bool_args2_mis.size(),
                                bool_args2_mis.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_NOT,
                                bool_args1_invalid.size(),
                                bool_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_OR,
                                bool_args2_invalid.size(),
                                bool_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_XOR,
                                bool_args2_invalid.size(),
                                bool_args2_invalid.data()),
               error_invalid_sort);
  // bit-vectors
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ADD,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ADD, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_AND,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_AND, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ASHR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ASHR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_DEC,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_INC,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_MUL,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_MUL, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NAND,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NAND,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NEG,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NOR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_NOR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_NOT,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_OR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_REDAND,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_REDOR,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_REDXOR,
                                bv_args1_invalid.size(),
                                bv_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_OR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_OR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ROL,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ROL, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ROR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ROR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SADD_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SDIV,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SDIV,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SGE,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SGE, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SGT,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SGT, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SHL,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SHL, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SHR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SHR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SLE,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SLE, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SLT,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SLT, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SMOD,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SMOD,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SREM,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SREM,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_SUB,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_SUB, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UADD_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UDIV,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UDIV,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UGE,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UGE, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UGT,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_UGT, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ULE,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ULE, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_ULT,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_ULT, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UREM,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_UREM,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_USUB_OVERFLOW,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_XNOR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_XNOR,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_BV_XOR,
                                bv_args2_invalid.size(),
                                bv_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_BV_XOR, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  // floating-point
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_ABS,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_invalid_2.size(),
                                fp_args3_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_invalid_1.size(),
                                fp_args3_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_ADD,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_invalid_2.size(),
                                fp_args3_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_invalid_1.size(),
                                fp_args3_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_DIV,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_EQUAL,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_EQUAL,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FMA,
                                fp_args4_rm_invalid_1.size(),
                                fp_args4_rm_invalid_1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FMA,
                                fp_args4_rm_invalid_2.size(),
                                fp_args4_rm_invalid_2.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_FMA, fp_args4_mis.size(), fp_args4_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_invalid_1.size(),
                                fp_fp_args3_invalid_1.data()),
               "expected bit-vector term of size 1 at index 0");
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_invalid_2.size(),
                                fp_fp_args3_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_invalid_3.size(),
                                fp_fp_args3_invalid_3.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_FP,
                                fp_fp_args3_invalid_4.size(),
                                fp_fp_args3_invalid_4.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_GEQ,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_GEQ, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_GT,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_GT, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_INF,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_NAN,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_NEG,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_NORMAL,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_POS,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_SUBNORMAL,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_ZERO,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_LEQ,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_LEQ, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_LT,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_LT, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_MAX,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_MAX, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_MIN,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_MIN, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_IS_ZERO,
                                fp_args1_invalid.size(),
                                fp_args1_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_invalid_2.size(),
                                fp_args3_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_invalid_1.size(),
                                fp_args3_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_MUL,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_REM,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_REM, fp_args2_mis.size(), fp_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_FP_RTI, fp_args2_mis.size(), fp_args2_mis.data()),
      d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_rm_invalid_1.size(),
                                fp_args2_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_RTI,
                                fp_args2_rm_invalid_2.size(),
                                fp_args2_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_invalid.size(),
                                fp_args2_invalid.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_mis.size(),
                                fp_args2_mis.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_rm_invalid_1.size(),
                                fp_args2_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SQRT,
                                fp_args2_rm_invalid_2.size(),
                                fp_args2_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_invalid_2.size(),
                                fp_args3_rm_invalid_2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_invalid_1.size(),
                                fp_args3_rm_invalid_1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FP_SUB,
                                fp_args3_rm_mis.size(),
                                fp_args3_rm_mis.data()),
               error_mis_sort);
  // others
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_APPLY,
                                apply_args3_invalid_1.size(),
                                apply_args3_invalid_1.data()),
               "invalid number of arguments");
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_APPLY,
                                apply_args3_invalid_2.size(),
                                apply_args3_invalid_2.data()),
               "does not match sort in function domain");
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_select_args2_invalid_1.size(),
                                array_select_args2_invalid_1.data()),
               d_error_exp_arr_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_SELECT,
                                array_select_args2_invalid_2.size(),
                                array_select_args2_invalid_2.data()),
               error_arr_index_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_invalid_1.size(),
                                array_store_args3_invalid_1.data()),
               d_error_exp_arr_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_invalid_2.size(),
                                array_store_args3_invalid_2.data()),
               error_arr_index_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ARRAY_STORE,
                                array_store_args3_invalid_3.size(),
                                array_store_args3_invalid_3.data()),
               error_arr_element_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_DISTINCT,
                                bv_args2_mis.size(),
                                bv_args2_mis.data()),
               error_mis_sort);
  ASSERT_DEATH(
      bitwuzla_mk_term(
          d_tm, BITWUZLA_KIND_EQUAL, bv_args2_mis.size(), bv_args2_mis.data()),
      error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_invalid_1.size(),
                                quant_args2_invalid_1.data()),
               d_error_exp_var_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_invalid_2.size(),
                                quant_args2_invalid_2.data()),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_EXISTS,
                                quant_args2_invalid_3.size(),
                                quant_args2_invalid_3.data()),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_EXISTS,
                                quant_args3_invalid.size(),
                                quant_args3_invalid.data()),
               error_dvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_invalid_1.size(),
                                quant_args2_invalid_1.data()),
               d_error_exp_var_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_invalid_2.size(),
                                quant_args2_invalid_2.data()),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FORALL,
                                quant_args2_invalid_3.size(),
                                quant_args2_invalid_3.data()),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_FORALL,
                                quant_args3_invalid.size(),
                                quant_args3_invalid.data()),
               error_dvar_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ITE,
                                ite_args3_invalid_2.size(),
                                ite_args3_invalid_2.data()),
               d_error_exp_bool_term);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_ITE,
                                ite_death_args3_1.size(),
                                ite_death_args3_1.data()),
               error_mis_sort);
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args2_invalid_1.size(),
                                lambda_args2_invalid_1.data()),
               d_error_exp_var_term);
  bitwuzla_mk_term(
      d_tm, BITWUZLA_KIND_LAMBDA, lambda_args2.size(), lambda_args2.data());
  ASSERT_DEATH(bitwuzla_mk_term(d_tm,
                                BITWUZLA_KIND_LAMBDA,
                                lambda_args3_invalid_1.size(),
                                lambda_args3_invalid_1.data()),
               error_dvar_term);
  bitwuzla_mk_term(
      d_tm, BITWUZLA_KIND_LAMBDA, lambda_args3.size(), lambda_args3.data());
  // indexed
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs2.size(),
                                        bv_idxs2.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_EXTRACT,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extract_death_idxs2_1.size(),
                                        bv_extract_death_idxs2_1.data()),
               "upper index must be greater or equal to lower index");
  ASSERT_DEATH(
      bitwuzla_mk_term_indexed(d_tm,
                               BITWUZLA_KIND_BV_EXTRACT,
                               bv_args1.size(),
                               bv_args1.data(),
                               bv_extract_death_idxs2_2.size(),
                               bv_extract_death_idxs2_2.data()),
      "upper index must be less than the bit-vector size of given term");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_REPEAT,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_REPEAT,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_repeat_idxs_invalid_1.size(),
                                        bv_repeat_idxs_invalid_1.data()),
               "resulting bit-vector size exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_ROLI,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_RORI,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_SIGN_EXTEND,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extend_idxs_invalid_1.size(),
                                        bv_extend_idxs_invalid_1.data()),
               "exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_BV_ZERO_EXTEND,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        bv_extend_idxs_invalid_1.size(),
                                        bv_extend_idxs_invalid_1.data()),
               "exceeds maximum bit-vector size");
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args1_invalid.size(),
                                        bv_args1_invalid.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                                        bv_args1.size(),
                                        bv_args1.data(),
                                        fp_idxs3.size(),
                                        fp_idxs3.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm_invalid_1.size(),
                                        fp_args2_rm_invalid_1.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm_invalid_2.size(),
                                        fp_args2_rm_invalid_2.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm.size(),
                                        fp_args2_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                                        fp_args2_rm.size(),
                                        fp_args2_rm.data(),
                                        fp_idxs3.size(),
                                        fp_idxs3.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                                        bv_args2_rm_invalid_1.size(),
                                        bv_args2_rm_invalid_1.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                                        bv_args2_rm_invalid_2.size(),
                                        bv_args2_rm_invalid_2.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                                        bv_args2_rm.size(),
                                        bv_args2_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_SBV,
                                        bv_args2_rm.size(),
                                        bv_args2_rm.data(),
                                        fp_idxs3.size(),
                                        fp_idxs3.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                        bv_args2_rm_invalid_1.size(),
                                        bv_args2_rm_invalid_1.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                        bv_args2_rm_invalid_2.size(),
                                        bv_args2_rm_invalid_2.data(),
                                        fp_idxs1.size(),
                                        fp_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                        bv_args2_rm.size(),
                                        bv_args2_rm.data(),
                                        fp_idxs2.size(),
                                        fp_idxs2.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_FP_FROM_UBV,
                                        bv_args2_rm.size(),
                                        bv_args2_rm.data(),
                                        fp_idxs3.size(),
                                        fp_idxs3.data()),
               error_fp_size);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args2_rm_invalid_1.size(),
                                        fp_args2_rm_invalid_1.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_SBV,
                                        fp_args2_rm_invalid_2.size(),
                                        fp_args2_rm_invalid_2.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args2_rm_invalid_1.size(),
                                        fp_args2_rm_invalid_1.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               d_error_exp_rm_term);
  ASSERT_DEATH(bitwuzla_mk_term_indexed(d_tm,
                                        BITWUZLA_KIND_FP_TO_UBV,
                                        fp_args2_rm_invalid_2.size(),
                                        fp_args2_rm_invalid_2.data(),
                                        bv_idxs1.size(),
                                        bv_idxs1.data()),
               error_invalid_sort);
}

TEST_F(TestCApi, mk_const)
{
  ASSERT_DEATH(bitwuzla_mk_const(d_tm, 0, "asdf"), d_error_inv_sort);
  bitwuzla_mk_const(d_tm, d_bv_sort8, 0);
  bitwuzla_mk_const(d_tm, d_bv_sort8, "");
}

TEST_F(TestCApi, mk_const_array)
{
  ASSERT_DEATH(bitwuzla_mk_const_array(d_tm, 0, d_bv_one1), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_tm, d_arr_sort_bv, 0),
               d_error_inv_term);
  ASSERT_DEATH(bitwuzla_mk_const_array(d_tm, d_bv_sort8, d_bv_one1),
               "sort of constant array is not an array sort");
  ASSERT_DEATH(
      bitwuzla_mk_const_array(d_tm, d_arr_sort_bv, d_array),
      "sort of constant array element does not match given array sort");
  ASSERT_DEATH(
      bitwuzla_mk_const_array(d_tm, d_arr_sort_bvfp, d_fp_pzero32),
      "sort of constant array element does not match given array sort");
  bitwuzla_mk_const_array(d_tm, d_arr_sort_bvfp, d_fp_const16);
}

TEST_F(TestCApi, mk_var)
{
  ASSERT_DEATH(bitwuzla_mk_var(d_tm, 0, "asdf"), d_error_inv_sort);
  bitwuzla_mk_var(d_tm, d_bv_sort8, 0);
  bitwuzla_mk_var(d_tm, d_bv_sort8, "");
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, get_term_mgr)
{
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_EQ(d_tm, bitwuzla_get_term_mgr(bitwuzla));
    bitwuzla_delete(bitwuzla);
  }
}

TEST_F(TestCApi, push)
{
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_DEATH(bitwuzla_push(nullptr, 2), d_error_not_null);

    bitwuzla_push(bitwuzla, 0);
    bitwuzla_delete(bitwuzla);
  }
}

TEST_F(TestCApi, pop)
{
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_DEATH(bitwuzla_pop(nullptr, 2), d_error_not_null);

    bitwuzla_pop(bitwuzla, 0);
    bitwuzla_delete(bitwuzla);
  }
}

TEST_F(TestCApi, assert)
{
  Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
  ASSERT_DEATH(bitwuzla_assert(nullptr, d_true), d_error_not_null);
  ASSERT_DEATH(bitwuzla_assert(bitwuzla, 0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_assert(bitwuzla, d_bv_const8), d_error_exp_bool_term);

  // TODO: this should throw, not implemented yet
  // ASSERT_DEATH(bitwuzla_assert(bitwuzla, d_bool_var),
  // d_error_unexp_param_term); ASSERT_DEATH(bitwuzla_assert(bitwuzla,
  // d_bool_lambda), d_error_exp_bool_term);
  // ASSERT_DEATH(bitwuzla_assert(bitwuzla, d_bool_lambda_body),
  //             d_error_unexp_param_term);

  bitwuzla_assert(bitwuzla, d_bool_apply);

  bitwuzla_assert(bitwuzla, d_bool_const);
  bitwuzla_delete(bitwuzla);
}

TEST_F(TestCApi, is_unsat_assumption)
{
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 0);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);
    ASSERT_DEATH(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const1),
                 "unsat assumptions production not enabled");
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 1);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);

    ASSERT_DEATH(bitwuzla_is_unsat_assumption(nullptr, d_true),
                 d_error_not_null);
    ASSERT_DEATH(bitwuzla_is_unsat_assumption(bitwuzla, 0), d_error_inv_term);

    bitwuzla_assert(bitwuzla, d_true);
    std::vector<BitwuzlaTerm> assumptions = {d_bool_const};
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());
    ASSERT_DEATH(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const1_true),
                 d_error_unsat);

    assumptions = {d_bool_const,
                   bitwuzla_mk_term1(d_tm, BITWUZLA_KIND_NOT, d_bool_const)};
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());

    ASSERT_DEATH(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const8),
                 d_error_exp_bool_term);
    ASSERT_DEATH(bitwuzla_is_unsat_assumption(bitwuzla, d_bool_lambda),
                 d_error_exp_bool_term);
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_true));
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_bool_var));
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_bool_lambda_body));
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(bitwuzla, d_bool_const));
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(
        bitwuzla, bitwuzla_mk_term1(d_tm, BITWUZLA_KIND_NOT, d_bool_const)));
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
}

TEST_F(TestCApi, get_unsat_assumptions)
{
  size_t size;
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 0);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);
    ASSERT_DEATH(bitwuzla_get_unsat_assumptions(bitwuzla, &size),
                 "unsat assumptions production not enabled");
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 1);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);

    ASSERT_DEATH(bitwuzla_get_unsat_assumptions(nullptr, &size),
                 d_error_not_null);
    ASSERT_DEATH(bitwuzla_get_unsat_assumptions(bitwuzla, 0), d_error_not_null);

    bitwuzla_assert(bitwuzla, d_true);
    std::vector<BitwuzlaTerm> assumptions{d_bool_const};
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());
    ASSERT_DEATH(bitwuzla_get_unsat_assumptions(bitwuzla, &size),
                 d_error_unsat);

    assumptions = {
        d_bv_const1_true, d_bv_const1_false, d_and_bv_const1, d_eq_bv_const8};
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const1_true));
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const1_false));
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_and_bv_const1));
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_eq_bv_const8));
    const BitwuzlaTerm *unsat_ass =
        bitwuzla_get_unsat_assumptions(bitwuzla, &size);
    size_t i                = 0;
    for (; i < size; ++i)
    {
      ASSERT_TRUE(bitwuzla_is_unsat_assumption(bitwuzla, unsat_ass[i]));
    }
    ASSERT_EQ(i, 2);
    for (i = 0; i < size; ++i)
    {
      bitwuzla_assert(bitwuzla, unsat_ass[i]);
    }
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
}

TEST_F(TestCApi, get_unsat_core)
{
  size_t size;
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_DEATH(bitwuzla_get_unsat_core(bitwuzla, &size), d_error_unsat_cores);
    bitwuzla_delete(bitwuzla);
  }
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_DEATH(bitwuzla_get_unsat_core(bitwuzla, &size), d_error_unsat_cores);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_CORES, 1);
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, 1);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);

    ASSERT_DEATH(bitwuzla_get_unsat_core(nullptr, &size), d_error_not_null);
    ASSERT_DEATH(bitwuzla_get_unsat_core(bitwuzla, nullptr), d_error_not_null);

    bitwuzla_assert(bitwuzla, d_true);
    std::vector<BitwuzlaTerm> assumptions{d_bv_const1_true};
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());
    ASSERT_DEATH(bitwuzla_get_unsat_core(bitwuzla, &size), d_error_unsat);

    bitwuzla_assert(bitwuzla, d_bv_const1_true);
    bitwuzla_assert(bitwuzla, d_eq_bv_const8);
    assumptions[0] = d_bv_const1_false;
    assumptions.push_back(d_and_bv_const1);
    bitwuzla_check_sat_assuming(
        bitwuzla, assumptions.size(), assumptions.data());
    ASSERT_TRUE(bitwuzla_is_unsat_assumption(bitwuzla, d_bv_const1_false));
    ASSERT_FALSE(bitwuzla_is_unsat_assumption(bitwuzla, d_and_bv_const1));
    const BitwuzlaTerm *unsat_core = bitwuzla_get_unsat_core(bitwuzla, &size);
    ASSERT_TRUE(size == 2);
    ASSERT_TRUE(unsat_core[0] == d_bv_const1_false
                || unsat_core[0] == d_bv_const1_true);
    ASSERT_TRUE(unsat_core[1] == d_bv_const1_false
                || unsat_core[1] == d_bv_const1_true);

    const BitwuzlaTerm *unsat_ass =
        bitwuzla_get_unsat_assumptions(bitwuzla, &size);
    ASSERT_EQ(unsat_ass[0], d_bv_const1_false);
    ASSERT_TRUE(size == 1);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_SAT);
    bitwuzla_assert(bitwuzla, unsat_ass[0]);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
}

TEST_F(TestCApi, simplify)
{
  ASSERT_DEATH(bitwuzla_simplify(nullptr), d_error_not_null);
  BitwuzlaOptions *options = bitwuzla_options_new();
  Bitwuzla *bitwuzla       = bitwuzla_new(d_tm, options);
  bitwuzla_assert(bitwuzla, d_bv_const1_false);
  bitwuzla_assert(bitwuzla, d_and_bv_const1);
  bitwuzla_simplify(bitwuzla);
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, check_sat)
{
  ASSERT_DEATH(bitwuzla_check_sat(nullptr), d_error_not_null);
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    bitwuzla_check_sat(bitwuzla);
    bitwuzla_check_sat(bitwuzla);
    bitwuzla_delete(bitwuzla);
  }
}

TEST_F(TestCApi, get_value)
{
  {
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, nullptr);
    ASSERT_DEATH(bitwuzla_get_value(bitwuzla, d_bv_const8),
                 d_error_produce_models);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);
    ASSERT_DEATH(bitwuzla_get_value(nullptr, d_bv_const8), d_error_not_null);
    ASSERT_DEATH(bitwuzla_get_value(bitwuzla, 0), d_error_inv_term);
    bitwuzla_assert(bitwuzla, d_bv_const1_true);
    std::vector<BitwuzlaTerm> assumptions{d_bv_const1_false};
    ASSERT_EQ(bitwuzla_check_sat_assuming(
                  bitwuzla, assumptions.size(), assumptions.data()),
              BITWUZLA_UNSAT);
    ASSERT_DEATH(bitwuzla_get_value(bitwuzla, d_bv_const1), d_error_sat);
    bitwuzla_check_sat(bitwuzla);
    ASSERT_EQ(d_bv_one1, bitwuzla_get_value(bitwuzla, d_bv_const1));
    ASSERT_EQ(bitwuzla_mk_false(d_tm),
              bitwuzla_get_value(bitwuzla, d_bv_const1_false));
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
  {
    BitwuzlaOptions *options = bitwuzla_options_new();
    bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, 1);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, options);
    bitwuzla_assert(bitwuzla, d_exists);
    ASSERT_DEATH(bitwuzla_get_value(bitwuzla, d_bv_const8), d_error_sat);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_SAT);
    bitwuzla_assert(
        bitwuzla,
        bitwuzla_mk_term2(d_tm,
                          BITWUZLA_KIND_EQUAL,
                          d_bv_const8,
                          bitwuzla_get_value(bitwuzla, d_bv_const8)));
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_SAT);
    bitwuzla_delete(bitwuzla);
    bitwuzla_options_delete(options);
  }
}

TEST_F(TestCApi, value_get_bool)
{
  ASSERT_EQ(true, bitwuzla_term_value_get_bool(d_true));
  ASSERT_EQ(false, bitwuzla_term_value_get_bool(bitwuzla_mk_false(d_tm)));
  ASSERT_EQ("true", std::string(bitwuzla_term_value_get_str(d_true)));
  ASSERT_EQ(
      "false",
      std::string(bitwuzla_term_value_get_str_fmt(bitwuzla_mk_false(d_tm), 2)));
}

TEST_F(TestCApi, value_get_bv)
{
  ASSERT_DEATH(bitwuzla_term_value_get_str(0), d_error_inv_term);
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str(d_bv_one1)),
            std::string("1"));
  BitwuzlaTerm bv_maxs32 = bitwuzla_mk_bv_max_signed(d_tm, d_bv_sort32);
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str(bv_maxs32)),
            std::string("01111111111111111111111111111111"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(bv_maxs32, 10)),
            std::string("2147483647"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(bv_maxs32, 16)),
            std::string("7fffffff"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-1", 10), 2)),
            std::string("11111111"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-1", 10), 10)),
            std::string("255"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-1", 10), 16)),
            std::string("ff"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-123", 10))),
            std::string("10000101"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-123", 10), 10)),
            std::string("133"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-123", 10), 16)),
            std::string("85"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-128", 10), 2)),
            std::string("10000000"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-128", 10), 10)),
            std::string("128"));
  ASSERT_EQ(std::string(bitwuzla_term_value_get_str_fmt(
                bitwuzla_mk_bv_value(d_tm, d_bv_sort8, "-128", 10), 16)),
            std::string("80"));
}

TEST_F(TestCApi, value_get_fp)
{
  ASSERT_EQ("01111111110000000000000000000000",
            std::string(bitwuzla_term_value_get_str(d_fp_nan32)));
  ASSERT_EQ("10000000000000000000000000000000",
            std::string(bitwuzla_term_value_get_str(d_fp_nzero32)));
}

TEST_F(TestCApi, value_fp_ieee)
{
  const char *sign, *exp, *sig;
  bitwuzla_term_value_get_fp_ieee(d_fp_nan32, &sign, &exp, &sig, 2);
  ASSERT_EQ("0", std::string(sign));
  ASSERT_EQ("11111111", std::string(exp));
  ASSERT_EQ("10000000000000000000000", std::string(sig));
  bitwuzla_term_value_get_fp_ieee(d_fp_nzero32, &sign, &exp, &sig, 2);
  ASSERT_EQ("1", std::string(sign));
  ASSERT_EQ("00000000", std::string(exp));
  ASSERT_EQ("00000000000000000000000", std::string(sig));
}

TEST_F(TestCApi, get_rm_value)
{
  ASSERT_DEATH(bitwuzla_term_value_get_rm(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_value_get_rm(d_fp_nan32),
               "expected rounding-mode value");
  ASSERT_EQ(BITWUZLA_RM_RNA, bitwuzla_term_value_get_rm(d_rm_rna));
  ASSERT_EQ(BITWUZLA_RM_RNE, bitwuzla_term_value_get_rm(d_rm_rne));
  ASSERT_EQ(BITWUZLA_RM_RTN, bitwuzla_term_value_get_rm(d_rm_rtn));
  ASSERT_EQ(BITWUZLA_RM_RTP, bitwuzla_term_value_get_rm(d_rm_rtp));
  ASSERT_EQ(BITWUZLA_RM_RTZ, bitwuzla_term_value_get_rm(d_rm_rtz));
  ASSERT_EQ("RNA", std::string(bitwuzla_term_value_get_str(d_rm_rna)));
  ASSERT_EQ("RNE", std::string(bitwuzla_term_value_get_str(d_rm_rne)));
  ASSERT_EQ("RTN", std::string(bitwuzla_term_value_get_str(d_rm_rtn)));
  ASSERT_EQ("RTP", std::string(bitwuzla_term_value_get_str_fmt(d_rm_rtp, 2)));
  ASSERT_EQ("RTZ", std::string(bitwuzla_term_value_get_str_fmt(d_rm_rtz, 10)));
}

/* -------------------------------------------------------------------------- */
/* Printing                                                                   */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, print_formula)
{
  ASSERT_DEATH(bitwuzla_print_formula(nullptr, "smt2", stdout, 2),
               d_error_not_null);

  BitwuzlaOptions *options = bitwuzla_options_new();
  Bitwuzla *bitwuzla       = bitwuzla_new(d_tm, options);

  ASSERT_DEATH(bitwuzla_print_formula(bitwuzla, nullptr, stdout, 2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_print_formula(bitwuzla, "smt2", nullptr, 2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_print_formula(bitwuzla, "asdf", stdout, 2),
               "invalid format, expected 'smt2'");
  ASSERT_DEATH(bitwuzla_print_formula(bitwuzla, "smt2", stdout, 23),
               "invalid bit-vector output number format");

  std::string filename = "print_formula.out";

  bitwuzla_assert(bitwuzla, d_bool_const);
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_EQUAL,
          bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_APPLY, d_lambda, d_bv_const8),
          d_bv_zero8));

  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 2);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic QF_BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#b00000000))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 10);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic QF_BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "(_ bv0 8)))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 16);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic QF_BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#x00))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }

  bitwuzla_assert(bitwuzla, d_exists);
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 2);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#b00000000))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 10);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "(_ bv0 8)))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 16);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic BV)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#x00))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }

  std::vector<BitwuzlaTerm> apply_args = {
      d_fun_fp,
      d_bv_const8,
      d_fp_const16,
      bitwuzla_mk_term1_indexed1(
          d_tm, BITWUZLA_KIND_BV_ZERO_EXTEND, d_bv_ones23, 9)};
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_FP_LEQ,
          bitwuzla_mk_term(
              d_tm, BITWUZLA_KIND_APPLY, apply_args.size(), apply_args.data()),
          d_fp_const16));
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 2);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(declare-const fp16 (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#b00000000))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))"
        << std::endl
        << "(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) "
           "#b11111111111111111111111)) fp16))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 10);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(declare-const fp16 (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "(_ bv0 8)))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))"
        << std::endl
        << "(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) "
           "(_ bv8388607 23))) fp16))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }
  {
    FILE *tmpfile = fopen(filename.c_str(), "w");
    bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 16);
    fclose(tmpfile);
    std::ifstream ifs(filename);
    std::string res((std::istreambuf_iterator<char>(ifs)),
                    (std::istreambuf_iterator<char>()));
    unlink(filename.c_str());
    std::stringstream expected_smt2;
    expected_smt2
        << "(set-logic UFBVFP)" << std::endl
        << "(declare-const b Bool)" << std::endl
        << "(declare-const bv8 (_ BitVec 8))" << std::endl
        << "(declare-const fp16 (_ FloatingPoint 5 11))" << std::endl
        << "(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) (_ BitVec "
           "32)) (_ FloatingPoint 5 11))"
        << std::endl
        << "(assert b)" << std::endl
        << "(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) "
           "#x00))"
        << std::endl
        << "(assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))"
        << std::endl
        << "(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) "
           "#b11111111111111111111111)) fp16))"
        << std::endl
        << "(check-sat)" << std::endl
        << "(exit)" << std::endl;
    ASSERT_EQ(res, expected_smt2.str());
  }

  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, print_formula2)
{
  std::string filename = "print_formula.out";
  FILE *tmpfile        = fopen(filename.c_str(), "w");

  BitwuzlaOptions *options = bitwuzla_options_new();
  Bitwuzla *bitwuzla       = bitwuzla_new(d_tm, options);
  BitwuzlaSort bv1         = bitwuzla_mk_bv_sort(d_tm, 1);
  BitwuzlaSort ar1_1       = bitwuzla_mk_array_sort(d_tm, bv1, bv1);
  BitwuzlaTerm a           = bitwuzla_mk_const(d_tm, ar1_1, "a");
  BitwuzlaTerm b           = bitwuzla_mk_const(d_tm, ar1_1, "b");
  BitwuzlaTerm z           = bitwuzla_mk_bv_one(d_tm, bv1);
  BitwuzlaTerm e = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_ARRAY_SELECT, a, z);
  BitwuzlaTerm c = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_EQUAL, a, b);
  bitwuzla_assert(bitwuzla, bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_EQUAL, e, z));
  bitwuzla_assert(bitwuzla, c);
  bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 2);
  fclose(tmpfile);

  std::ifstream ifs(filename);
  std::string res((std::istreambuf_iterator<char>(ifs)),
                  (std::istreambuf_iterator<char>()));
  unlink(filename.c_str());

  std::stringstream expected_smt2;
  expected_smt2 << "(set-logic QF_ABV)" << std::endl
                << "(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))"
                << std::endl
                << "(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))"
                << std::endl
                << "(assert (= (select a #b1) #b1))" << std::endl
                << "(assert (= a b))" << std::endl
                << "(check-sat)" << std::endl
                << "(exit)" << std::endl;
  ASSERT_EQ(res, expected_smt2.str());
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, print_formula3)
{
  std::string filename = "print_formula.out";
  FILE *tmpfile        = fopen(filename.c_str(), "w");

  BitwuzlaOptions *options = bitwuzla_options_new();
  Bitwuzla *bitwuzla       = bitwuzla_new(d_tm, options);
  BitwuzlaSort bv32        = bitwuzla_mk_bv_sort(d_tm, 32);
  BitwuzlaTerm n           = bitwuzla_mk_const(d_tm, bv32, "n");
  BitwuzlaTerm sim         = bitwuzla_mk_const(d_tm, bv32, "~");
  BitwuzlaTerm zero        = bitwuzla_mk_bv_zero(d_tm, bv32);
  BitwuzlaTerm two         = bitwuzla_mk_bv_value_uint64(d_tm, bv32, 2);
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_DISTINCT,
                        zero,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, n, sim)));
  bitwuzla_push(bitwuzla, 1);
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_EQUAL,
          bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, n, two),
          bitwuzla_mk_term1(
              d_tm,
              BITWUZLA_KIND_BV_NEG,
              bitwuzla_mk_term2(
                  d_tm,
                  BITWUZLA_KIND_BV_ADD,
                  sim,
                  bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_MUL, n, two)))));
  bitwuzla_push(bitwuzla, 1);
  bitwuzla_assert(
      bitwuzla,
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_EQUAL,
          zero,
          bitwuzla_mk_term2(
              d_tm, BITWUZLA_KIND_BV_ADD, n, bitwuzla_mk_bv_one(d_tm, bv32))));

  bitwuzla_print_formula(bitwuzla, "smt2", tmpfile, 2);
  fclose(tmpfile);

  std::ifstream ifs(filename);
  std::string res((std::istreambuf_iterator<char>(ifs)),
                  (std::istreambuf_iterator<char>()));
  unlink(filename.c_str());

  std::stringstream expected_smt2;
  expected_smt2
      << "(set-logic QF_BV)" << std::endl
      << "(declare-const n (_ BitVec 32))" << std::endl
      << "(declare-const ~ (_ BitVec 32))" << std::endl
      << "(assert (distinct #b00000000000000000000000000000000 (bvadd n ~)))"
      << std::endl
      << "(push 1)" << std::endl
      << "(assert (= (bvadd n #b00000000000000000000000000000010) (bvneg "
         "(bvadd ~ (bvmul n "
         "#b00000000000000000000000000000010)))))"
      << std::endl
      << "(push 1)" << std::endl
      << "(assert (= #b00000000000000000000000000000000 (bvadd n "
         "#b00000000000000000000000000000001)))"
      << std::endl
      << "(check-sat)" << std::endl
      << "(exit)" << std::endl;

  ASSERT_EQ(res, expected_smt2.str());
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
}

/* -------------------------------------------------------------------------- */
/* Statistics                                                                 */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, statistics)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  Bitwuzla *bitwuzla       = bitwuzla_new(d_tm, options);
  bitwuzla_assert(bitwuzla, d_bool_const);
  const char **keys, **values;
  size_t size;
  bitwuzla_get_statistics(bitwuzla, &keys, &values, &size);
  for (size_t i = 0; i < size; ++i)
  {
    std::cout << keys[i] << ": " << values[i] << std::endl;
  }
  bitwuzla_delete(bitwuzla);
  bitwuzla_options_delete(options);
}

/* -------------------------------------------------------------------------- */
/* Parsing                                                                    */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, parser_smt2)
{
  const char *filename = "parse.smt2";
  std::ofstream smt2(filename);
  smt2 << "(set-logic QF_BV)\n";
  smt2 << "(check-sat)\n";
  smt2 << "(exit)\n" << std::flush;
  smt2.close();

  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  ASSERT_DEATH(bitwuzla_parser_new(d_tm, nullptr, "smt2", 2, "<stdout>"),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_new(d_tm, options, nullptr, 2, "<stdout>"),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_new(d_tm, options, "smt2", 12, "<stdout>"),
               "invalid bit-vector output number format");
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
  ASSERT_DEATH(bitwuzla_parser_get_bitwuzla(parser), "not yet initialized");
  ASSERT_DEATH(bitwuzla_parser_parse(nullptr, filename, true, true, &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse(parser, nullptr, true, true, &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse(parser, filename, true, true, nullptr),
               d_error_not_null);
  bitwuzla_parser_parse(parser, filename, true, true, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_funs, nullptr);
  bitwuzla_options_delete(options);
  bitwuzla_parser_delete(parser);
  std::remove(filename);
  ASSERT_DEATH(bitwuzla_parser_get_bitwuzla(nullptr), d_error_not_null);
}

TEST_F(TestCApi, parser2_smt2)
{
  const char *filename = "parse.smt2";
  std::ofstream smt2(filename);
  smt2 << "(assert x)" << std::flush;
  smt2.close();

  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
  bitwuzla_parser_parse(parser, filename, true, true, &error_msg);
  ASSERT_NE(error_msg, nullptr);
  ASSERT_EQ(std::string(error_msg),
  std::string(bitwuzla_parser_get_error_msg(parser)));
  ASSERT_NE(std::string(error_msg).find("undefined symbol 'x'"),
            std::string::npos);
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_funs, nullptr);
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
  std::remove(filename);
}

TEST_F(TestCApi, parser_string1_smt2)
{
  std::stringstream smt2;
  smt2 << "(set-logic QF_BV)\n";
  smt2 << "(check-sat)\n";
  smt2 << "(exit)\n";
  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, smt2.str().c_str(), true, true, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    ASSERT_NE(std::string(error_msg).find("failed to open"), std::string::npos);
    size_t size;
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_funs, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, smt2.str().c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    size_t size;
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_funs, nullptr);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_string2_smt2)
{
  std::string str_decl     = "(declare-const a Bool)";
  std::string str_true     = "(assert (= a true))";
  std::string str_false    = "(assert (= a false))";
  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
  bitwuzla_parser_parse(parser, str_decl.c_str(), true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(parser, str_true.c_str(), true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(parser, str_false.c_str(), true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  Bitwuzla *bitwuzla = bitwuzla_parser_get_bitwuzla(parser);
  ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
  ASSERT_EQ(bitwuzla_get_term_mgr(bitwuzla), d_tm);
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 1);
  ASSERT_EQ(std::string(bitwuzla_term_get_symbol(decl_funs[0])), "a");
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_smt2_string_term)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
  const char *error_msg;

  ASSERT_DEATH(bitwuzla_parser_parse_term(nullptr, "true", &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse_term(parser, nullptr, &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse_term(parser, "true", nullptr),
               d_error_not_null);

  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "true", &error_msg),
            bitwuzla_mk_true(d_tm));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "false", &error_msg),
            bitwuzla_mk_false(d_tm));
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(
      parser, "(declare-const a Bool)", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_a = bitwuzla_parser_parse_term(parser, "a", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(
      parser, "(declare-const b (_ BitVec 16))", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_b = bitwuzla_parser_parse_term(parser, "b", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(
      parser, "(declare-const c Bool)", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_c = bitwuzla_parser_parse_term(parser, "c", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "(xor a c)", &error_msg),
            bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_XOR, t_a, t_c));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(
      bitwuzla_parser_parse_term(
          parser, "(bvadd b #b1011111010001010)", &error_msg),
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_BV_ADD,
          t_b,
          bitwuzla_mk_bv_value(
              d_tm, bitwuzla_mk_bv_sort(d_tm, 16), "1011111010001010", 2)));
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 3);
  std::unordered_set<std::string> decl_funs_strs;
  for (size_t i = 0; i < size; ++i)
  {
    decl_funs_strs.insert(bitwuzla_term_get_symbol(decl_funs[i]));
  }
  ASSERT_NE(decl_funs_strs.find("a"), decl_funs_strs.end());
  ASSERT_NE(decl_funs_strs.find("b"), decl_funs_strs.end());
  ASSERT_NE(decl_funs_strs.find("c"), decl_funs_strs.end());
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_smt2_string_sort)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "smt2", 10, "<stdout>");
  const char *error_msg;

  ASSERT_DEATH(bitwuzla_parser_parse_sort(nullptr, "Bool", &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse_sort(parser, nullptr, &error_msg),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_parser_parse_sort(parser, "Bool", nullptr),
               d_error_not_null);

  ASSERT_EQ(bitwuzla_parser_parse_sort(parser, "Bool", &error_msg),
            bitwuzla_mk_bool_sort(d_tm));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_sort(parser, "(_ BitVec 32)", &error_msg),
            bitwuzla_mk_bv_sort(d_tm, 32));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_sort(parser, "RoundingMode", &error_msg),
            bitwuzla_mk_rm_sort(d_tm));
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(parser, "(declare-sort m 0)", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse_sort(parser, "m", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(parser,
                        "(define-sort FPN () (_ FloatingPoint 11 53))",
                        true,
                        false,
                        &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaSort fpn = bitwuzla_parser_parse_sort(parser, "FPN", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(fpn,
            bitwuzla_parser_parse_sort(
                parser, "(_ FloatingPoint 11 53)", &error_msg));
  ASSERT_EQ(error_msg, nullptr);
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 1);
  ASSERT_EQ(std::string(bitwuzla_sort_get_uninterpreted_symbol(decl_sorts[0])),
            "m");
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_funs, nullptr);
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_smt2_print_model_sat)
{
  const char *filename = "parse.smt2";
  std::ofstream smt2(filename);
  smt2 << "(declare-fun a () (_ BitVec 1))\n";
  smt2 << "(declare-fun b () (_ BitVec 1))\n";
  smt2 << "(declare-fun c () (_ BitVec 1))\n";
  smt2 << "(declare-fun d () (_ BitVec 1))\n";
  smt2 << "(assert (= b (ite (= (_ bv1 1) (bvand c b d a)) (_ bv0 1) (_ bv1 "
          "1))))\n";
  smt2 << "(set-info :status sat)\n";
  smt2 << "(check-sat)\n";
  smt2.close();

  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();

  {
    // error, produce models not enabled
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    ASSERT_EQ(std::string(error_msg),
              std::string(bitwuzla_parser_get_error_msg(parser)));
    std::cout << error_msg << std::endl;
    ASSERT_NE(std::string(error_msg).find("model generation is not enabled"),
              std::string::npos);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, true);
  {
    // parse only
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, true, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
  std::remove(filename);
}

TEST_F(TestCApi, parser_smt2_print_model_unsat)
{
  const char *filename = "parse.smt2";
  std::ofstream smt2(filename);
  smt2 << "(set-info :status unsat)\n";
  smt2 << "(set-logic QF_AUFBV)\n";
  smt2 << "(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))\n";
  smt2 << "(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))\n";
  smt2 << "(declare-fun i () (_ BitVec 32))\n";
  smt2 << "(declare-fun c () Bool)\n";
  smt2 << "(assert (not (= (ite c (select a i) (select b i)) (select (ite c a "
          "b) i))))\n";
  smt2 << "(check-sat)\n";
  smt2.close();

  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  {
    // error, produce models not enabled
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    ASSERT_EQ(std::string(error_msg),
              std::string(bitwuzla_parser_get_error_msg(parser)));
    ASSERT_NE(std::string(error_msg).find("model generation is not enabled"),
              std::string::npos);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, true);
  {
    // parse only
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, true, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "smt2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
  std::remove(filename);
}

TEST_F(TestCApi, parser_btor2)
{
  const char *input = "parse.btor2";
  std::ofstream btor2(input);
  btor2 << "1 sort bitvec 8" << std::endl;
  btor2 << "2 input 1 @inp2" << std::endl;
  btor2 << "3 sort bitvec 3" << std::endl;
  btor2 << "4 one 3" << std::endl;
  btor2 << "5 uext 1 4 5" << std::endl;
  btor2 << "6 srl 1 2 5" << std::endl;
  btor2 << "7 sort bitvec 1" << std::endl;
  btor2 << "8 slice 7 6 7 7" << std::endl;
  btor2 << "9 constraint 8" << std::endl << std::flush;
  const char *error_msg;
  size_t size;

  BitwuzlaOptions *options = bitwuzla_options_new();

  ASSERT_DEATH(bitwuzla_parser_new(d_tm, options, "btor2", 10, nullptr),
               d_error_not_null);
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_get_bitwuzla(parser);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_funs, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, "parsex.btor2", true, true, &error_msg);
    ASSERT_NE(std::string(error_msg).find("failed to open 'parsex.btor2'"),
              std::string::npos);
    bitwuzla_parser_parse(parser, "parse.btor2", true, true, &error_msg);
    ASSERT_NE(
        std::string(error_msg).find("parser in unsafe state after parse error"),
        std::string::npos);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_funs, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, input, true, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla_parser_get_bitwuzla(parser)),
              BITWUZLA_UNSAT);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 1);
    ASSERT_EQ(std::string(bitwuzla_term_get_symbol(decl_funs[0])), "@inp2");
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
  std::remove(input);
}

TEST_F(TestCApi, parser_btor2_string1)
{
  std::stringstream btor2;
  btor2 << "1 sort bitvec 8" << std::endl;
  btor2 << "2 input 1 @inp2" << std::endl;
  btor2 << "3 sort bitvec 3" << std::endl;
  btor2 << "4 one 3 @one" << std::endl;
  btor2 << "5 uext 1 4 5" << std::endl;
  btor2 << "6 srl 1 2 5 @srl" << std::endl;
  btor2 << "7 sort bitvec 1" << std::endl;
  btor2 << "8 slice 7 6 7 7" << std::endl;
  btor2 << "9 constraint 8" << std::endl;

  const char *error_msg;
  size_t size;
  BitwuzlaOptions *options = bitwuzla_options_new();
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, btor2.str().c_str(), true, true, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    ASSERT_NE(std::string(error_msg).find("failed to open"), std::string::npos);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_funs, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, btor2.str().c_str(), true, false, &error_msg);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 1);
    ASSERT_EQ(std::string(bitwuzla_term_get_symbol(decl_funs[0])), "@inp2");
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_btor2_string2)
{
  std::string decl_sorts;
  {
    std::stringstream ss;
    ss << "1 sort bitvec 8" << std::endl << "2 sort array 1 1" << std::endl;
    decl_sorts = ss.str();
  }
  std::string decl_inputs;
  {
    std::stringstream ss;
    ss << "3 input 2 @arr3" << std::endl
       << "4 input 2 @arr4" << std::endl
       << "5 input 2 @arr5" << std::endl;
    decl_inputs = ss.str();
  }
  std::string decl_more_inputs;
  {
    std::stringstream ss;
    ss << "6 sort bitvec 1" << std::endl
       << "7 input 6 @inp7" << std::endl
       << "8 input 1 @inp8" << std::endl;
    decl_more_inputs = ss.str();
  }
  std::string ite9;
  {
    std::stringstream ss;
    ss << "9 ite 2 -7 4 5" << std::endl;
    ite9 = ss.str();
  }
  std::string reads;
  {
    std::stringstream ss;
    ss << "10 read 1 4 8" << std::endl
       << "11 read 1 9 8" << std::endl
       << "12 neq 6 10 11" << std::endl;
    reads = ss.str();
  }
  std::string and13;
  {
    std::stringstream ss;
    ss << "13 and 6 -7 12";
    and13 = ss.str();
  }
  std::string root;
  {
    std::stringstream ss;
    ss << "14 constraint 13" << std::endl;
    root = ss.str();
  }

  size_t size;
  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, decl_sorts.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, decl_inputs.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(
        parser, decl_more_inputs.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, ite9.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, reads.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, and13.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, root.c_str(), true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    Bitwuzla *bitwuzla = bitwuzla_parser_get_bitwuzla(parser);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 5);
    std::unordered_set<std::string> decl_funs_strs;
    for (size_t i = 0; i < size; ++i)
    {
      decl_funs_strs.insert(bitwuzla_term_get_symbol(decl_funs[i]));
    }
    ASSERT_NE(decl_funs_strs.find("@arr3"), decl_funs_strs.end());
    ASSERT_NE(decl_funs_strs.find("@arr4"), decl_funs_strs.end());
    ASSERT_NE(decl_funs_strs.find("@arr5"), decl_funs_strs.end());
    ASSERT_NE(decl_funs_strs.find("@inp7"), decl_funs_strs.end());
    ASSERT_NE(decl_funs_strs.find("@inp8"), decl_funs_strs.end());
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
    bitwuzla_parser_parse(parser, decl_sorts.c_str(), true, false, &error_msg);
    bitwuzla_parser_parse(parser, "3 input 2 @arr3", true, false, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_parse(parser, "3 input 2 @arr3", true, false, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
    ASSERT_EQ(size, 0);
    ASSERT_EQ(decl_sorts, nullptr);
    auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
    ASSERT_EQ(size, 1);
    ASSERT_EQ(std::string(bitwuzla_term_get_symbol(decl_funs[0])), "@arr3");
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_btor2_string_term)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");

  const char *error_msg;
  bitwuzla_parser_parse(parser, "1 sort bitvec 1", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "2 constd 1 1", &error_msg),
            bitwuzla_mk_bv_value_uint64(d_tm, bitwuzla_mk_bv_sort(d_tm, 1), 1));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "3 constd 1 0", &error_msg),
            bitwuzla_mk_bv_value_uint64(d_tm, bitwuzla_mk_bv_sort(d_tm, 1), 0));
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_a =
      bitwuzla_parser_parse_term(parser, "4 input 1 a", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  bitwuzla_parser_parse(parser, "5 sort bitvec 16", true, false, &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_b =
      bitwuzla_parser_parse_term(parser, "6 input 5 b", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  BitwuzlaTerm t_c =
      bitwuzla_parser_parse_term(parser, "7 input 1 c", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_term(parser, "8 xor 1 4 7", &error_msg),
            bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_XOR, t_a, t_c));
  bitwuzla_parser_parse_term(parser, "9 const 5 1011111010001010", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(
      bitwuzla_parser_parse_term(parser, "10 add 5 6 9", &error_msg),
      bitwuzla_mk_term2(
          d_tm,
          BITWUZLA_KIND_BV_ADD,
          t_b,
          bitwuzla_mk_bv_value(
              d_tm, bitwuzla_mk_bv_sort(d_tm, 16), "1011111010001010", 2)));
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 3);
  std::unordered_set<std::string> decl_funs_strs;
  for (size_t i = 0; i < size; ++i)
  {
    decl_funs_strs.insert(bitwuzla_term_get_symbol(decl_funs[i]));
  }
  ASSERT_NE(decl_funs_strs.find("a"), decl_funs_strs.end());
  ASSERT_NE(decl_funs_strs.find("b"), decl_funs_strs.end());
  ASSERT_NE(decl_funs_strs.find("c"), decl_funs_strs.end());
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_btor2_string_sort)
{
  BitwuzlaOptions *options = bitwuzla_options_new();
  BitwuzlaParser *parser =
      bitwuzla_parser_new(d_tm, options, "btor2", 10, "<stdout>");
  const char *error_msg;
  BitwuzlaSort bv1 =
      bitwuzla_parser_parse_sort(parser, "1 sort bitvec 1", &error_msg);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bv1, bitwuzla_mk_bv_sort(d_tm, 1));
  ASSERT_EQ(bitwuzla_parser_parse_sort(parser, "2 sort bitvec 32", &error_msg),
            bitwuzla_mk_bv_sort(d_tm, 32));
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(bitwuzla_parser_parse_sort(parser, "3 sort array 1 1", &error_msg),
            bitwuzla_mk_array_sort(d_tm, bv1, bv1));
  ASSERT_EQ(error_msg, nullptr);
  size_t size;
  auto decl_sorts = bitwuzla_parser_get_declared_sorts(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_sorts, nullptr);
  auto decl_funs = bitwuzla_parser_get_declared_funs(parser, &size);
  ASSERT_EQ(size, 0);
  ASSERT_EQ(decl_funs, nullptr);
  bitwuzla_parser_delete(parser);
  bitwuzla_options_delete(options);
}

TEST_F(TestCApi, parser_btor2_print_model_sat)
{
  const char *filename = "parse.btor2";
  std::ofstream btor2(filename);
  btor2 << "1 sort bitvec 32\n";
  btor2 << "2 input 1 x\n";
  btor2 << "3 input 1 y\n";
  btor2 << "4 add 1 -2 -3\n";
  btor2 << "5 add 1 2 4\n";
  btor2 << "6 add 1 3 5\n";
  btor2 << "7 const 1 11111111111111111111111111111110\n";
  btor2 << "8 sort bitvec 1\n";
  btor2 << "9 eq 8 6 7\n";
  btor2 << "10 constraint 9\n";
  btor2.close();

  const char *error_msg;
  BitwuzlaOptions *options = bitwuzla_options_new();
  {
    // error, produce models not enabled
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_NE(error_msg, nullptr);
    ASSERT_EQ(std::string(error_msg),
              std::string(bitwuzla_parser_get_error_msg(parser)));
    ASSERT_NE(std::string(error_msg).find("model generation is not enabled"),
              std::string::npos);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_set_option(options, BITWUZLA_OPT_PRODUCE_MODELS, true);
  {
    // parse only
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, true, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  {
    BitwuzlaParser *parser =
        bitwuzla_parser_new(d_tm, options, "btor2", 2, "<stdout>");
    bitwuzla_parser_configure_auto_print_model(parser, true);
    bitwuzla_parser_parse(parser, filename, false, true, &error_msg);
    ASSERT_EQ(error_msg, nullptr);
    bitwuzla_parser_delete(parser);
  }
  bitwuzla_options_delete(options);
  std::remove(filename);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, sort_hash)
{
  ASSERT_DEATH(bitwuzla_sort_hash(0), d_error_inv_sort);
}

TEST_F(TestCApi, sort_bv_get_size)
{
  ASSERT_DEATH(bitwuzla_sort_bv_get_size(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_bv_get_size(d_fp_sort16), d_error_exp_bv_sort);
  ASSERT_EQ(bitwuzla_sort_bv_get_size(d_bv_sort8), 8);
}

TEST_F(TestCApi, sort_fp_get_exp_size)
{
  ASSERT_DEATH(bitwuzla_sort_fp_get_exp_size(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_fp_get_exp_size(d_bv_sort8), d_error_exp_fp_sort);
  ASSERT_EQ(bitwuzla_sort_fp_get_exp_size(d_fp_sort16), 5);
}

TEST_F(TestCApi, sort_fp_get_sig_size)
{
  ASSERT_DEATH(bitwuzla_sort_fp_get_sig_size(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_fp_get_sig_size(d_bv_sort8), d_error_exp_fp_sort);
  ASSERT_EQ(bitwuzla_sort_fp_get_sig_size(d_fp_sort16), 11);
}

TEST_F(TestCApi, sort_array_get_index)
{
  ASSERT_DEATH(bitwuzla_sort_array_get_index(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_array_get_index(d_bv_sort23),
               d_error_exp_arr_sort);
  ASSERT_TRUE(
      bitwuzla_sort_is_bv(bitwuzla_sort_array_get_index(d_arr_sort_bvfp)));
}

TEST_F(TestCApi, sort_array_get_element)
{
  ASSERT_DEATH(bitwuzla_sort_array_get_element(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_array_get_element(d_bv_sort23),
               d_error_exp_arr_sort);
  ASSERT_TRUE(
      bitwuzla_sort_is_fp(bitwuzla_sort_array_get_element(d_arr_sort_bvfp)));
}

TEST_F(TestCApi, sort_fun_get_domain_sorts)
{
  size_t size;
  ASSERT_DEATH(bitwuzla_sort_fun_get_domain_sorts(0, &size), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_fun_get_domain_sorts(d_fun_sort, nullptr),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_sort_fun_get_domain_sorts(d_bv_sort32, &size),
               d_error_exp_fun_sort);

  BitwuzlaSort *domain_sorts =
      bitwuzla_sort_fun_get_domain_sorts(d_fun_sort, &size);
  ASSERT_EQ(size, 3);
  ASSERT_EQ(d_bv_sort8, domain_sorts[0]);
  ASSERT_EQ(d_fp_sort16, domain_sorts[1]);
  ASSERT_EQ(d_bv_sort32, domain_sorts[2]);
}

TEST_F(TestCApi, sort_fun_get_codomain)
{
  ASSERT_DEATH(bitwuzla_sort_fun_get_codomain(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_fun_get_codomain(d_bv_sort32),
               d_error_exp_fun_sort);
  ASSERT_EQ(bitwuzla_sort_fun_get_codomain(d_fun_sort), d_bv_sort8);
}

TEST_F(TestCApi, sort_fun_get_arity)
{
  ASSERT_DEATH(bitwuzla_sort_fun_get_arity(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_fun_get_arity(d_bv_sort32), d_error_exp_fun_sort);
  ASSERT_EQ(bitwuzla_sort_fun_get_arity(d_fun_sort), 3);
}

TEST_F(TestCApi, sort_get_uninterpreted_symbol)
{
  ASSERT_DEATH(bitwuzla_sort_get_uninterpreted_symbol(0), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_get_uninterpreted_symbol(d_bv_sort8),
               "expected uninterpreted sort");
  BitwuzlaSort s1 = bitwuzla_mk_uninterpreted_sort(d_tm, nullptr);
  BitwuzlaSort s2 = bitwuzla_mk_uninterpreted_sort(d_tm, "foo");
  BitwuzlaSort s3 = bitwuzla_mk_uninterpreted_sort(d_tm, "foo");
  BitwuzlaSort s4 = bitwuzla_mk_uninterpreted_sort(d_tm, "bar");
  ASSERT_EQ(bitwuzla_sort_get_uninterpreted_symbol(s1), nullptr);
  ASSERT_EQ(std::string(bitwuzla_sort_get_uninterpreted_symbol(s2)),
            std::string("foo"));
  ASSERT_EQ(std::string(bitwuzla_sort_get_uninterpreted_symbol(s3)),
            std::string("foo"));
  ASSERT_EQ(std::string(bitwuzla_sort_get_uninterpreted_symbol(s4)),
            std::string("bar"));
}

TEST_F(TestCApi, sort_is_array)
{
  ASSERT_DEATH(bitwuzla_sort_is_array(0), d_error_inv_sort);
  ASSERT_TRUE(bitwuzla_sort_is_array(d_arr_sort_bv));
  ASSERT_TRUE(bitwuzla_sort_is_array(d_arr_sort_bvfp));
  ASSERT_TRUE(bitwuzla_sort_is_array(d_arr_sort_fpbv));
  ASSERT_FALSE(bitwuzla_sort_is_array(d_fun_sort));
  ASSERT_FALSE(bitwuzla_sort_is_array(d_fun_sort_fp));
  ASSERT_FALSE(bitwuzla_sort_is_array(d_bv_sort8));
  ASSERT_FALSE(bitwuzla_sort_is_array(d_fp_sort16));
  ASSERT_FALSE(bitwuzla_sort_is_array(d_un_sort));
}

TEST_F(TestCApi, sort_is_bv)
{
  ASSERT_DEATH(bitwuzla_sort_is_bv(0), d_error_inv_sort);
  ASSERT_TRUE(bitwuzla_sort_is_bv(d_bv_sort1));
  ASSERT_TRUE(bitwuzla_sort_is_bv(d_bv_sort8));
  ASSERT_TRUE(bitwuzla_sort_is_bv(d_bv_sort23));
  ASSERT_TRUE(bitwuzla_sort_is_bv(d_bv_sort32));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_fp_sort16));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_arr_sort_bv));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_arr_sort_bvfp));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_arr_sort_fpbv));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_fun_sort));
  ASSERT_FALSE(bitwuzla_sort_is_bv(d_un_sort));
}

TEST_F(TestCApi, sort_is_fp)
{
  ASSERT_DEATH(bitwuzla_sort_is_fp(0), d_error_inv_sort);
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_fp_sort16));
  ASSERT_TRUE(bitwuzla_sort_is_fp(d_fp_sort32));
  ASSERT_FALSE(bitwuzla_sort_is_fp(d_bv_sort8));
  ASSERT_FALSE(bitwuzla_sort_is_fp(d_arr_sort_bv));
  ASSERT_FALSE(bitwuzla_sort_is_fp(d_arr_sort_bvfp));
  ASSERT_FALSE(bitwuzla_sort_is_fp(d_fun_sort_fp));
  ASSERT_FALSE(bitwuzla_sort_is_fp(d_un_sort));
}

TEST_F(TestCApi, sort_is_fun)
{
  ASSERT_DEATH(bitwuzla_sort_is_fun(0), d_error_inv_sort);
  ASSERT_TRUE(bitwuzla_sort_is_fun(d_fun_sort));
  ASSERT_TRUE(bitwuzla_sort_is_fun(d_fun_sort_fp));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_arr_sort_bv));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_arr_sort_bvfp));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_arr_sort_fpbv));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_bv_sort8));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_fp_sort16));
  ASSERT_FALSE(bitwuzla_sort_is_fun(d_un_sort));
}

TEST_F(TestCApi, sort_is_rm)
{
  ASSERT_DEATH(bitwuzla_sort_is_rm(0), d_error_inv_sort);
  ASSERT_TRUE(bitwuzla_sort_is_rm(d_rm_sort));
  ASSERT_FALSE(bitwuzla_sort_is_rm(d_bv_sort8));
  ASSERT_FALSE(bitwuzla_sort_is_rm(d_fp_sort16));
  ASSERT_FALSE(bitwuzla_sort_is_rm(d_arr_sort_bv));
  ASSERT_FALSE(bitwuzla_sort_is_rm(d_un_sort));
}

TEST_F(TestCApi, sort_is_uninterpreted)
{
  ASSERT_DEATH(bitwuzla_sort_is_uninterpreted(0), d_error_inv_sort);
  ASSERT_FALSE(bitwuzla_sort_is_uninterpreted(d_rm_sort));
  ASSERT_FALSE(bitwuzla_sort_is_uninterpreted(d_bv_sort8));
  ASSERT_FALSE(bitwuzla_sort_is_uninterpreted(d_fp_sort16));
  ASSERT_FALSE(bitwuzla_sort_is_uninterpreted(d_arr_sort_bv));
  ASSERT_TRUE(bitwuzla_sort_is_uninterpreted(d_un_sort));
}

TEST_F(TestCApi, sort_print)
{
  ASSERT_DEATH(bitwuzla_sort_print(0, stdout), d_error_inv_sort);
  ASSERT_DEATH(bitwuzla_sort_print(d_bv_sort1, nullptr), d_error_not_null);

  testing::internal::CaptureStdout();

  bitwuzla_sort_print(d_bv_sort1, stdout);
  bitwuzla_sort_print(d_bv_sort8, stdout);
  bitwuzla_sort_print(d_rm_sort, stdout);
  bitwuzla_sort_print(d_fp_sort32, stdout);

  std::string output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output,
            "(_ BitVec 1)(_ BitVec 8)RoundingMode(_ FloatingPoint 8 24)");
}

TEST_F(TestCApi, regr1)
{
  std::vector<BitwuzlaSort> domain({d_bv_sort8});
  BitwuzlaSort fun_sort =
      bitwuzla_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bv_sort8);
  bitwuzla_mk_array_sort(d_tm, d_bv_sort8, d_bv_sort8);
  std::vector<BitwuzlaTerm> args({bitwuzla_mk_const(d_tm, d_bv_sort8, "x"),
                                  bitwuzla_mk_const(d_tm, fun_sort, "f")});
  ASSERT_DEATH(
      bitwuzla_mk_term(d_tm, BITWUZLA_KIND_APPLY, args.size(), args.data()),
      d_error_unexp_fun_term);
}

TEST_F(TestCApi, regr2)
{
  std::vector<BitwuzlaSort> domain({d_bv_sort8});
  BitwuzlaSort fun_sort =
      bitwuzla_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bv_sort8);
  BitwuzlaSort array_sort =
      bitwuzla_mk_array_sort(d_tm, d_bv_sort8, d_bv_sort8);
  ASSERT_NE(fun_sort, array_sort);
  BitwuzlaTerm fun   = bitwuzla_mk_const(d_tm, fun_sort, 0);
  BitwuzlaTerm array = bitwuzla_mk_const(d_tm, array_sort, 0);
  ASSERT_EQ(array_sort, bitwuzla_term_get_sort(array));
  ASSERT_EQ(fun_sort, bitwuzla_term_get_sort(fun));
  ASSERT_NE(bitwuzla_term_get_sort(fun), bitwuzla_term_get_sort(array));
  ASSERT_TRUE(bitwuzla_term_is_fun(fun));
  ASSERT_TRUE(bitwuzla_term_is_array(array));
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestCApi, term_hash)
{
  ASSERT_DEATH(bitwuzla_term_hash(0), d_error_inv_term);
}

TEST_F(TestCApi, term_get_sort)
{
  ASSERT_DEATH(bitwuzla_term_get_sort(0), d_error_inv_term);
  ASSERT_EQ(bitwuzla_term_get_sort(d_bv_const8), d_bv_sort8);
}

TEST_F(TestCApi, term_array_get_index_sort)
{
  ASSERT_DEATH(bitwuzla_term_array_get_index_sort(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_array_get_index_sort(d_bv_zero8),
               d_error_exp_arr_sort);
  ASSERT_TRUE(
      bitwuzla_sort_is_fp(bitwuzla_term_array_get_index_sort(d_array_fpbv)));
  ASSERT_EQ(bitwuzla_term_array_get_index_sort(d_array_fpbv), d_fp_sort16);
}

TEST_F(TestCApi, term_array_get_element_sort)
{
  ASSERT_DEATH(bitwuzla_term_array_get_element_sort(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_array_get_element_sort(d_bv_zero8),
               d_error_exp_arr_sort);
  ASSERT_TRUE(
      bitwuzla_sort_is_bv(bitwuzla_term_array_get_element_sort(d_array_fpbv)));
  ASSERT_EQ(bitwuzla_term_array_get_element_sort(d_array_fpbv), d_bv_sort8);
}

TEST_F(TestCApi, term_fun_get_domain_sorts)
{
  size_t size;
  BitwuzlaTerm bv_term = bitwuzla_mk_const(d_tm, d_bv_sort32, "bv");

  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(0, &size), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(bv_term, nullptr),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_term_fun_get_domain_sorts(bv_term, &size),
               d_error_exp_fun_sort);

  BitwuzlaSort *domain_sorts = bitwuzla_term_fun_get_domain_sorts(d_fun, &size);
  ASSERT_EQ(size, 3);
  ASSERT_EQ(d_bv_sort8, domain_sorts[0]);
  ASSERT_EQ(d_fp_sort16, domain_sorts[1]);
  ASSERT_EQ(d_bv_sort32, domain_sorts[2]);
}

TEST_F(TestCApi, term_fun_get_codomain_sort)
{
  ASSERT_DEATH(bitwuzla_term_fun_get_codomain_sort(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_fun_get_codomain_sort(d_bv_zero8),
               d_error_exp_fun_sort);
  ASSERT_EQ(bitwuzla_term_fun_get_codomain_sort(d_fun_fp), d_fp_sort16);
}

TEST_F(TestCApi, term_bv_get_size)
{
  ASSERT_DEATH(bitwuzla_term_bv_get_size(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_bv_get_size(d_fp_const16), d_error_exp_bv_sort);
  ASSERT_EQ(bitwuzla_term_bv_get_size(d_bv_zero8), 8);
}

TEST_F(TestCApi, term_fp_get_exp_size)
{
  ASSERT_DEATH(bitwuzla_term_fp_get_exp_size(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_fp_get_exp_size(d_bv_const8), d_error_exp_fp_sort);
  ASSERT_EQ(bitwuzla_term_fp_get_exp_size(d_fp_const16), 5);
}

TEST_F(TestCApi, term_fp_get_sig_size)
{
  ASSERT_DEATH(bitwuzla_term_fp_get_sig_size(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_fp_get_sig_size(d_bv_const8), d_error_exp_fp_sort);
  ASSERT_EQ(bitwuzla_term_fp_get_sig_size(d_fp_const16), 11);
}

TEST_F(TestCApi, term_fun_get_arity)
{
  ASSERT_DEATH(bitwuzla_term_fun_get_arity(0), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_fun_get_arity(d_bv_const8), d_error_exp_fun_sort);
  ASSERT_EQ(bitwuzla_term_fun_get_arity(d_fun), 3);
}

TEST_F(TestCApi, term_get_symbol)
{
  ASSERT_DEATH(bitwuzla_term_get_symbol(0), d_error_inv_term);
  ASSERT_EQ(std::string(bitwuzla_term_get_symbol(d_fun)), std::string("fun"));
}

TEST_F(TestCApi, term_is_equal_sort)
{
  ASSERT_DEATH(bitwuzla_term_is_equal_sort(0, d_bv_const1), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_is_equal_sort(d_bv_const1, 0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_equal_sort(d_bv_const8, d_bv_zero8));
  ASSERT_FALSE(bitwuzla_term_is_equal_sort(d_bv_const1, d_bv_zero8));
}

TEST_F(TestCApi, term_is_const)
{
  ASSERT_DEATH(bitwuzla_term_is_const(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_const(d_array));
  ASSERT_TRUE(bitwuzla_term_is_const(d_fun));
  ASSERT_TRUE(bitwuzla_term_is_const(d_bv_const1));
  ASSERT_TRUE(bitwuzla_term_is_const(d_fp_const16));
  ASSERT_TRUE(bitwuzla_term_is_const(d_rm_const));
  ASSERT_FALSE(bitwuzla_term_is_const(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_const(d_store));
}

TEST_F(TestCApi, term_is_var)
{
  ASSERT_DEATH(bitwuzla_term_is_var(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_var(d_var1));
  ASSERT_TRUE(bitwuzla_term_is_var(d_bound_var));
  ASSERT_FALSE(bitwuzla_term_is_var(d_fp_pzero32));
}

#if 0
TEST_F(TestCApi, term_is_bound_var)
{
  ASSERT_DEATH(bitwuzla_term_is_bound_var(0), d_error_inv_term);
  ASSERT_FALSE(bitwuzla_term_is_bound_var(d_var1));
  ASSERT_TRUE(bitwuzla_term_is_bound_var(d_bound_var));
  ASSERT_DEATH(bitwuzla_term_is_bound_var(d_fp_pzero32), d_error_exp_var_term);
}
#endif

TEST_F(TestCApi, term_is_array)
{
  ASSERT_DEATH(bitwuzla_term_is_array(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_array(d_array));
  ASSERT_TRUE(bitwuzla_term_is_array(d_store));
  ASSERT_FALSE(bitwuzla_term_is_array(d_fun));
  ASSERT_FALSE(bitwuzla_term_is_array(d_fp_pzero32));
}

TEST_F(TestCApi, term_is_bv)
{
  ASSERT_DEATH(bitwuzla_term_is_bv(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv(d_bv_zero8));
  ASSERT_FALSE(bitwuzla_term_is_bv(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_bv(d_array));
  ASSERT_FALSE(bitwuzla_term_is_bv(d_array_fpbv));
  ASSERT_FALSE(bitwuzla_term_is_bv(d_fun));
}

TEST_F(TestCApi, term_is_fp)
{
  ASSERT_DEATH(bitwuzla_term_is_fp(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp(d_bv_zero8));
  ASSERT_FALSE(bitwuzla_term_is_fp(d_array));
  ASSERT_FALSE(bitwuzla_term_is_fp(d_array_fpbv));
  ASSERT_FALSE(bitwuzla_term_is_fp(d_fun));
}

TEST_F(TestCApi, term_is_fun)
{
  ASSERT_DEATH(bitwuzla_term_is_fun(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fun(d_fun));
  ASSERT_FALSE(bitwuzla_term_is_fun(d_array));
  ASSERT_FALSE(bitwuzla_term_is_fun(d_array_fpbv));
  ASSERT_FALSE(bitwuzla_term_is_fun(d_fp_pzero32));
}

TEST_F(TestCApi, term_is_rm)
{
  ASSERT_DEATH(bitwuzla_term_is_rm(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm(d_rm_const));
  ASSERT_FALSE(bitwuzla_term_is_rm(d_bv_zero8));
}

TEST_F(TestCApi, term_is_uninterpreted)
{
  ASSERT_DEATH(bitwuzla_term_is_uninterpreted(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_uninterpreted(d_un_const));
  ASSERT_FALSE(bitwuzla_term_is_uninterpreted(d_bv_zero8));
}

TEST_F(TestCApi, term_is_true)
{
  ASSERT_TRUE(bitwuzla_term_is_true(bitwuzla_mk_true(d_tm)));
  ASSERT_FALSE(bitwuzla_term_is_true(bitwuzla_mk_false(d_tm)));
  ASSERT_FALSE(bitwuzla_term_is_true(bitwuzla_mk_bv_one(d_tm, d_bv_sort1)));
}

TEST_F(TestCApi, term_is_false)
{
  ASSERT_TRUE(bitwuzla_term_is_false(bitwuzla_mk_false(d_tm)));
  ASSERT_FALSE(bitwuzla_term_is_false(bitwuzla_mk_true(d_tm)));
  ASSERT_FALSE(bitwuzla_term_is_false(bitwuzla_mk_bv_zero(d_tm, d_bv_sort1)));
}

TEST_F(TestCApi, term_is_bv_value)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value(d_bv_zero8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value(d_bv_const1));
}

TEST_F(TestCApi, term_is_fp_value)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value(d_fp_const16));
}

TEST_F(TestCApi, term_is_rm_value)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value(d_rm_rna));
  ASSERT_TRUE(bitwuzla_term_is_rm_value(d_rm_rne));
  ASSERT_TRUE(bitwuzla_term_is_rm_value(d_rm_rtn));
  ASSERT_TRUE(bitwuzla_term_is_rm_value(d_rm_rtp));
  ASSERT_TRUE(bitwuzla_term_is_rm_value(d_rm_rtz));
  ASSERT_FALSE(bitwuzla_term_is_rm_value(d_rm_const));
}

TEST_F(TestCApi, term_is_bv_value_zero)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value_zero(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value_zero(d_bv_zero8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_zero(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_zero(d_bv_ones23));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_zero(d_bv_mins8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_zero(d_bv_maxs8));
}

TEST_F(TestCApi, term_is_bv_value_one)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value_one(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value_one(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_one(d_bv_ones23));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_one(d_bv_mins8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_one(d_bv_maxs8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_one(d_bv_zero8));
}

TEST_F(TestCApi, term_is_bv_value_ones)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value_ones(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value_ones(d_bv_ones23));
  ASSERT_TRUE(bitwuzla_term_is_bv_value_ones(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_ones(d_bv_mins8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_ones(d_bv_maxs8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_ones(d_bv_zero8));
}

TEST_F(TestCApi, term_is_bv_value_min_signed)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value_min_signed(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value_min_signed(d_bv_mins8));
  ASSERT_TRUE(bitwuzla_term_is_bv_value_min_signed(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_min_signed(d_bv_ones23));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_min_signed(d_bv_maxs8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_min_signed(d_bv_zero8));
}

TEST_F(TestCApi, term_is_bv_value_max_signed)
{
  ASSERT_DEATH(bitwuzla_term_is_bv_value_max_signed(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_bv_value_max_signed(d_bv_maxs8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_max_signed(d_bv_mins8));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_max_signed(d_bv_one1));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_max_signed(d_bv_ones23));
  ASSERT_FALSE(bitwuzla_term_is_bv_value_max_signed(d_bv_zero8));
}

TEST_F(TestCApi, term_is_fp_value_pos_zero)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value_pos_zero(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value_pos_zero(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_zero(d_fp_nzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_zero(d_fp_pinf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_zero(d_fp_ninf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_zero(d_fp_nan32));
}

TEST_F(TestCApi, term_is_fp_value_neg_zero)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value_neg_zero(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value_neg_zero(d_fp_nzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_zero(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_zero(d_fp_pinf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_zero(d_fp_ninf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_zero(d_fp_nan32));
}

TEST_F(TestCApi, term_is_fp_value_pos_inf)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value_pos_inf(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value_pos_inf(d_fp_pinf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_inf(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_inf(d_fp_nzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_inf(d_fp_ninf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_pos_inf(d_fp_nan32));
}

TEST_F(TestCApi, term_is_fp_value_neg_inf)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value_neg_inf(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value_neg_inf(d_fp_ninf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_inf(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_inf(d_fp_nzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_inf(d_fp_pinf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_neg_inf(d_fp_nan32));
}

TEST_F(TestCApi, term_is_fp_value_nan)
{
  ASSERT_DEATH(bitwuzla_term_is_fp_value_nan(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_fp_value_nan(d_fp_nan32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_nan(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_nan(d_fp_nzero32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_nan(d_fp_pinf32));
  ASSERT_FALSE(bitwuzla_term_is_fp_value_nan(d_fp_ninf32));
}

TEST_F(TestCApi, term_is_rm_value_rna)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value_rna(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value_rna(d_rm_rna));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rna(d_fp_pzero32));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rna(d_rm_rne));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rna(d_rm_rtn));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rna(d_rm_rtp));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rna(d_rm_rtz));
}

TEST_F(TestCApi, term_is_rm_value_rne)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value_rne(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value_rne(d_rm_rne));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rne(d_fun));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rne(d_rm_rna));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rne(d_rm_rtn));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rne(d_rm_rtp));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rne(d_rm_rtz));
}

TEST_F(TestCApi, term_is_rm_value_rtn)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value_rtn(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value_rtn(d_rm_rtn));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtn(d_true));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtn(d_rm_rna));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtn(d_rm_rne));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtn(d_rm_rtp));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtn(d_rm_rtz));
}

TEST_F(TestCApi, term_is_rm_value_rtp)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value_rtp(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value_rtp(d_rm_rtp));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtp(d_var2));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtp(d_rm_rna));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtp(d_rm_rne));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtp(d_rm_rtn));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtp(d_rm_rtz));
}

TEST_F(TestCApi, term_is_rm_value_rtz)
{
  ASSERT_DEATH(bitwuzla_term_is_rm_value_rtz(0), d_error_inv_term);
  ASSERT_TRUE(bitwuzla_term_is_rm_value_rtz(d_rm_rtz));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtz(d_lambda));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtz(d_rm_rna));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtz(d_rm_rne));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtz(d_rm_rtn));
  ASSERT_FALSE(bitwuzla_term_is_rm_value_rtz(d_rm_rtp));
}

TEST_F(TestCApi, term_print)
{
  ASSERT_DEATH(bitwuzla_term_print(0, stdout), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_print(d_and_bv_const1, nullptr), d_error_not_null);
  {
    testing::internal::CaptureStdout();

    bitwuzla_term_print(d_and_bv_const1, stdout);
    bitwuzla_term_print(d_exists, stdout);

    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output,
              "(= #b1 (bvand #b1 bv1))"
              "(exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q)))");
  }

  BitwuzlaSort bv1  = bitwuzla_mk_bv_sort(d_tm, 1);
  BitwuzlaSort bv5  = bitwuzla_mk_bv_sort(d_tm, 5);
  BitwuzlaSort bv10 = bitwuzla_mk_bv_sort(d_tm, 10);
  BitwuzlaSort bv4  = bitwuzla_mk_bv_sort(d_tm, 4);
  BitwuzlaSort bv8  = bitwuzla_mk_bv_sort(d_tm, 8);

  {
    BitwuzlaTerm t =
        bitwuzla_mk_fp_value(d_tm,
                             bitwuzla_mk_bv_one(d_tm, bv1),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv5, 3),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv10, 23));

    testing::internal::CaptureStdout();
    bitwuzla_term_print(t, stdout);
    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output, "(fp #b1 #b00011 #b0000010111)");
  }
  {
    BitwuzlaTerm t =
        bitwuzla_mk_fp_value(d_tm,
                             bitwuzla_mk_bv_one(d_tm, bv1),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv4, 3),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv8, 23));
    testing::internal::CaptureStdout();
    bitwuzla_term_print(t, stdout);
    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output, "(fp #b1 #b0011 #b00010111)");
  }
}

TEST_F(TestCApi, term_print_fmt)
{
  ASSERT_DEATH(bitwuzla_term_print_fmt(0, stdout, 2), d_error_inv_term);
  ASSERT_DEATH(bitwuzla_term_print_fmt(d_and_bv_const1, nullptr, 2),
               d_error_not_null);
  ASSERT_DEATH(bitwuzla_term_print_fmt(d_and_bv_const1, stdout, 23),
               "invalid bit-vector output number format");

  {
    testing::internal::CaptureStdout();

    bitwuzla_term_print_fmt(d_and_bv_const1, stdout, 2);
    bitwuzla_term_print_fmt(d_exists, stdout, 2);
    bitwuzla_term_print_fmt(d_and_bv_const1, stdout, 10);
    bitwuzla_term_print_fmt(d_exists, stdout, 10);
    bitwuzla_term_print_fmt(d_and_bv_const1, stdout, 16);
    bitwuzla_term_print_fmt(d_exists, stdout, 16);

    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output,
              "(= #b1 (bvand #b1 bv1))"
              "(exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q)))"
              "(= (_ bv1 1) (bvand (_ bv1 1) bv1))"
              "(exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q)))"
              "(= #b1 (bvand #b1 bv1))"
              "(exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q)))");
  }

  BitwuzlaSort bv1  = bitwuzla_mk_bv_sort(d_tm, 1);
  BitwuzlaSort bv5  = bitwuzla_mk_bv_sort(d_tm, 5);
  BitwuzlaSort bv10 = bitwuzla_mk_bv_sort(d_tm, 10);
  BitwuzlaSort bv4  = bitwuzla_mk_bv_sort(d_tm, 4);
  BitwuzlaSort bv8  = bitwuzla_mk_bv_sort(d_tm, 8);

  {
    BitwuzlaTerm t =
        bitwuzla_mk_fp_value(d_tm,
                             bitwuzla_mk_bv_one(d_tm, bv1),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv5, 3),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv10, 23));

    testing::internal::CaptureStdout();
    bitwuzla_term_print_fmt(t, stdout, 2);
    bitwuzla_term_print_fmt(t, stdout, 10);
    bitwuzla_term_print_fmt(t, stdout, 16);
    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output,
              "(fp #b1 #b00011 #b0000010111)"
              "(fp (_ bv1 1) (_ bv3 5) (_ bv23 10))"
              "(fp #b1 #b00011 #b0000010111)");
  }
  {
    BitwuzlaTerm t =
        bitwuzla_mk_fp_value(d_tm,
                             bitwuzla_mk_bv_one(d_tm, bv1),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv4, 3),
                             bitwuzla_mk_bv_value_uint64(d_tm, bv8, 23));
    testing::internal::CaptureStdout();
    bitwuzla_term_print_fmt(t, stdout, 2);
    bitwuzla_term_print_fmt(t, stdout, 10);
    bitwuzla_term_print_fmt(t, stdout, 16);
    std::string output = testing::internal::GetCapturedStdout();
    ASSERT_EQ(output,
              "(fp #b1 #b0011 #b00010111)"
              "(fp (_ bv1 1) (_ bv3 4) (_ bv23 8))"
              "(fp #b1 #b0011 #b00010111)");
  }
}

TEST_F(TestCApi, term_print_regr0)
{
  testing::internal::CaptureStdout();

  bitwuzla_term_print(d_rm_rne, stdout);
  printf("\n");
  bitwuzla_term_print(d_rm_rna, stdout);
  printf("\n");
  bitwuzla_term_print(d_rm_rtn, stdout);
  printf("\n");
  bitwuzla_term_print(d_rm_rtp, stdout);
  printf("\n");
  bitwuzla_term_print(d_rm_rtz, stdout);

  std::string output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output, "RNE\nRNA\nRTN\nRTP\nRTZ");
}

TEST_F(TestCApi, term_print_regr1)
{
  BitwuzlaSort bv_sort5  = bitwuzla_mk_bv_sort(d_tm, 5);
  BitwuzlaSort bv_sort10 = bitwuzla_mk_bv_sort(d_tm, 10);

  BitwuzlaTerm fp_val;
  std::string output;

  fp_val = bitwuzla_mk_fp_value(d_tm,
                                bitwuzla_mk_bv_zero(d_tm, d_bv_sort1),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort5),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort10));

  testing::internal::CaptureStdout();
  bitwuzla_term_print(fp_val, stdout);
  output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output, "(fp #b0 #b00000 #b0000000000)");

  fp_val = bitwuzla_mk_fp_value(d_tm,
                                bitwuzla_mk_bv_one(d_tm, d_bv_sort1),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort5),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort10));

  testing::internal::CaptureStdout();
  bitwuzla_term_print(fp_val, stdout);
  output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output, "(fp #b1 #b00000 #b0000000000)");

  fp_val = bitwuzla_mk_fp_value(d_tm,
                                bitwuzla_mk_bv_zero(d_tm, d_bv_sort1),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort5),
                                bitwuzla_mk_bv_one(d_tm, bv_sort10));

  testing::internal::CaptureStdout();
  bitwuzla_term_print(fp_val, stdout);
  output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output, "(fp #b0 #b00000 #b0000000001)");

  fp_val = bitwuzla_mk_fp_value(d_tm,
                                bitwuzla_mk_bv_one(d_tm, d_bv_sort1),
                                bitwuzla_mk_bv_zero(d_tm, bv_sort5),
                                bitwuzla_mk_bv_one(d_tm, bv_sort10));

  testing::internal::CaptureStdout();
  bitwuzla_term_print(fp_val, stdout);
  output = testing::internal::GetCapturedStdout();
  ASSERT_EQ(output, "(fp #b1 #b00000 #b0000000001)");
}

TEST_F(TestCApi, indexed)
{
  BitwuzlaSort fp_sort = bitwuzla_mk_fp_sort(d_tm, 5, 11);
  BitwuzlaSort bv_sort = bitwuzla_mk_bv_sort(d_tm, 8);
  BitwuzlaTerm fp_term = bitwuzla_mk_const(d_tm, fp_sort, 0);
  BitwuzlaTerm bv_term = bitwuzla_mk_const(d_tm, bv_sort, 0);
  BitwuzlaTerm rm      = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RNE);

  size_t size;
  uint64_t *indices;
  BitwuzlaTerm idx =
      bitwuzla_mk_term2_indexed1(d_tm, BITWUZLA_KIND_FP_TO_SBV, rm, fp_term, 8);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 1);
  ASSERT_EQ(indices[0], 8);

  idx =
      bitwuzla_mk_term2_indexed1(d_tm, BITWUZLA_KIND_FP_TO_UBV, rm, fp_term, 9);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 1);
  ASSERT_EQ(indices[0], 9);

  idx = bitwuzla_mk_term1_indexed2(
      d_tm, BITWUZLA_KIND_FP_TO_FP_FROM_BV, bv_term, 3, 5);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 2);
  ASSERT_EQ(indices[0], 3);
  ASSERT_EQ(indices[1], 5);

  idx = bitwuzla_mk_term2_indexed2(
      d_tm, BITWUZLA_KIND_FP_TO_FP_FROM_FP, rm, fp_term, 7, 18);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 2);
  ASSERT_EQ(indices[0], 7);
  ASSERT_EQ(indices[1], 18);

  idx = bitwuzla_mk_term2_indexed2(
      d_tm, BITWUZLA_KIND_FP_TO_FP_FROM_SBV, rm, bv_term, 8, 24);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 2);
  ASSERT_EQ(indices[0], 8);
  ASSERT_EQ(indices[1], 24);

  idx = bitwuzla_mk_term2_indexed2(
      d_tm, BITWUZLA_KIND_FP_TO_FP_FROM_UBV, rm, bv_term, 5, 11);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 2);
  ASSERT_EQ(indices[0], 5);
  ASSERT_EQ(indices[1], 11);

  idx =
      bitwuzla_mk_term1_indexed2(d_tm, BITWUZLA_KIND_BV_EXTRACT, bv_term, 6, 0);
  ASSERT_TRUE(bitwuzla_term_is_indexed(idx));
  indices = bitwuzla_term_get_indices(idx, &size);
  ASSERT_EQ(size, 2);
  ASSERT_EQ(indices[0], 6);
  ASSERT_EQ(indices[1], 0);
}

TEST_F(TestCApi, terms)
{
  BitwuzlaSort array_sort =
      bitwuzla_mk_array_sort(d_tm, d_bv_sort16, d_bv_sort16);
  std::vector<BitwuzlaSort> domain = {d_bv_sort16, d_bv_sort16, d_bv_sort16};
  BitwuzlaSort fun_sort =
      bitwuzla_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bv_sort16);

  std::vector<BitwuzlaTerm> fp_args = {
      d_rm_rna,
      bitwuzla_mk_const(d_tm, d_fp_sort16, nullptr),
      bitwuzla_mk_const(d_tm, d_fp_sort16, nullptr),
      bitwuzla_mk_const(d_tm, d_fp_sort16, nullptr)};

  std::vector<BitwuzlaTerm> bv_args = {
      bitwuzla_mk_const(d_tm, d_bv_sort16, nullptr),
      bitwuzla_mk_const(d_tm, d_bv_sort16, nullptr),
      bitwuzla_mk_const(d_tm, d_bv_sort16, nullptr),
      bitwuzla_mk_const(d_tm, d_bv_sort16, nullptr)};

  std::vector<BitwuzlaTerm> bool_args = {
      bitwuzla_mk_const(d_tm, d_bool_sort, nullptr),
      bitwuzla_mk_const(d_tm, d_bool_sort, nullptr)};

  for (size_t i = 0; i < BITWUZLA_KIND_NUM_KINDS; ++i)
  {
    BitwuzlaKind kind = static_cast<BitwuzlaKind>(i);
    BitwuzlaTerm term = nullptr;

    switch (kind)
    {
      case BITWUZLA_KIND_CONSTANT:
      case BITWUZLA_KIND_CONST_ARRAY:
      case BITWUZLA_KIND_VALUE:
      case BITWUZLA_KIND_VARIABLE: continue;

      // Boolean
      case BITWUZLA_KIND_NOT:
        term = bitwuzla_mk_term1(d_tm, kind, bool_args[0]);
        break;

      case BITWUZLA_KIND_AND:
      case BITWUZLA_KIND_IFF:
      case BITWUZLA_KIND_IMPLIES:
      case BITWUZLA_KIND_OR:
      case BITWUZLA_KIND_XOR:
        term = bitwuzla_mk_term(d_tm, kind, bool_args.size(), bool_args.data());
        break;

      // BV Unary
      case BITWUZLA_KIND_BV_DEC:
      case BITWUZLA_KIND_BV_INC:
      case BITWUZLA_KIND_BV_NEG:
      case BITWUZLA_KIND_BV_NEG_OVERFLOW:
      case BITWUZLA_KIND_BV_NOT:
      case BITWUZLA_KIND_BV_REDAND:
      case BITWUZLA_KIND_BV_REDOR:
      case BITWUZLA_KIND_BV_REDXOR:
        term = bitwuzla_mk_term(d_tm, kind, 1, bv_args.data());
        break;

      // BV Binary
      case BITWUZLA_KIND_BV_ASHR:
      case BITWUZLA_KIND_BV_COMP:
      case BITWUZLA_KIND_BV_NAND:
      case BITWUZLA_KIND_BV_NOR:
      case BITWUZLA_KIND_BV_ROL:
      case BITWUZLA_KIND_BV_ROR:
      case BITWUZLA_KIND_BV_SADD_OVERFLOW:
      case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
      case BITWUZLA_KIND_BV_SDIV:
      case BITWUZLA_KIND_BV_SGE:
      case BITWUZLA_KIND_BV_SGT:
      case BITWUZLA_KIND_BV_SHL:
      case BITWUZLA_KIND_BV_SHR:
      case BITWUZLA_KIND_BV_SLE:
      case BITWUZLA_KIND_BV_SLT:
      case BITWUZLA_KIND_BV_SMOD:
      case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
      case BITWUZLA_KIND_BV_SREM:
      case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
      case BITWUZLA_KIND_BV_SUB:
      case BITWUZLA_KIND_BV_UADD_OVERFLOW:
      case BITWUZLA_KIND_BV_UDIV:
      case BITWUZLA_KIND_BV_UGE:
      case BITWUZLA_KIND_BV_UGT:
      case BITWUZLA_KIND_BV_ULE:
      case BITWUZLA_KIND_BV_ULT:
      case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
      case BITWUZLA_KIND_BV_UREM:
      case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      case BITWUZLA_KIND_BV_XNOR:
        term = bitwuzla_mk_term(d_tm, kind, 2, bv_args.data());
        break;

      // BV Binary+
      case BITWUZLA_KIND_BV_ADD:
      case BITWUZLA_KIND_BV_AND:
      case BITWUZLA_KIND_BV_CONCAT:
      case BITWUZLA_KIND_BV_MUL:
      case BITWUZLA_KIND_BV_OR:
      case BITWUZLA_KIND_BV_XOR:
        term = bitwuzla_mk_term(d_tm, kind, bv_args.size(), bv_args.data());
        break;

      case BITWUZLA_KIND_DISTINCT:
      case BITWUZLA_KIND_EQUAL:
        term = bitwuzla_mk_term(d_tm, kind, 2, bv_args.data());
        break;

      // BV indexed
      case BITWUZLA_KIND_BV_EXTRACT:
        term = bitwuzla_mk_term1_indexed2(d_tm, kind, bv_args[0], 3, 2);
        break;

      case BITWUZLA_KIND_BV_REPEAT:
      case BITWUZLA_KIND_BV_ROLI:
      case BITWUZLA_KIND_BV_RORI:
      case BITWUZLA_KIND_BV_SIGN_EXTEND:
      case BITWUZLA_KIND_BV_ZERO_EXTEND:
        term = bitwuzla_mk_term1_indexed1(d_tm, kind, bv_args[0], 5);
        break;

      // Arrays
      case BITWUZLA_KIND_ARRAY_SELECT: {
        std::vector<BitwuzlaTerm> args = {
            bitwuzla_mk_const(d_tm, array_sort, nullptr), bv_args[0]};
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      case BITWUZLA_KIND_ARRAY_STORE: {
        std::vector<BitwuzlaTerm> args = {
            bitwuzla_mk_const(d_tm, array_sort, nullptr),
            bv_args[0],
            bv_args[1]};
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      case BITWUZLA_KIND_APPLY: {
        std::vector<BitwuzlaTerm> args = {
            bitwuzla_mk_const(d_tm, fun_sort, nullptr),
            bv_args[0],
            bv_args[1],
            bv_args[2]};
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      // Binder
      case BITWUZLA_KIND_EXISTS:
      case BITWUZLA_KIND_FORALL:
      case BITWUZLA_KIND_LAMBDA: {
        std::vector<BitwuzlaTerm> args = {
            bitwuzla_mk_var(d_tm, d_bv_sort16, nullptr),
            bitwuzla_mk_var(d_tm, d_bv_sort16, nullptr)};
        // body
        args.push_back(bitwuzla_mk_term(
            d_tm, BITWUZLA_KIND_BV_SLT, args.size(), args.data()));
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      // FP Unary
      case BITWUZLA_KIND_FP_ABS:
      case BITWUZLA_KIND_FP_IS_INF:
      case BITWUZLA_KIND_FP_IS_NAN:
      case BITWUZLA_KIND_FP_IS_NEG:
      case BITWUZLA_KIND_FP_IS_NORMAL:
      case BITWUZLA_KIND_FP_IS_POS:
      case BITWUZLA_KIND_FP_IS_SUBNORMAL:
      case BITWUZLA_KIND_FP_IS_ZERO:
      case BITWUZLA_KIND_FP_NEG:
        term = bitwuzla_mk_term1(d_tm, kind, fp_args[1]);
        break;

      // FP Binary
      case BITWUZLA_KIND_FP_EQUAL:
      case BITWUZLA_KIND_FP_GEQ:
      case BITWUZLA_KIND_FP_GT:
      case BITWUZLA_KIND_FP_LEQ:
      case BITWUZLA_KIND_FP_LT:
      case BITWUZLA_KIND_FP_MAX:
      case BITWUZLA_KIND_FP_MIN:
      case BITWUZLA_KIND_FP_REM:
        term = bitwuzla_mk_term(d_tm, kind, 2, fp_args.data() + 1);
        break;

      case BITWUZLA_KIND_FP_SQRT:
      case BITWUZLA_KIND_FP_RTI:
        term = bitwuzla_mk_term(d_tm, kind, 2, fp_args.data());
        break;

      // FP Ternary
      case BITWUZLA_KIND_FP_ADD:
      case BITWUZLA_KIND_FP_DIV:
      case BITWUZLA_KIND_FP_MUL:
      case BITWUZLA_KIND_FP_SUB:
        term = bitwuzla_mk_term(d_tm, kind, 3, fp_args.data());
        break;

      case BITWUZLA_KIND_FP_FP: {
        std::vector<BitwuzlaTerm> args = {d_bv_const1, bv_args[0], bv_args[1]};
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      // FP Quaternery
      case BITWUZLA_KIND_FP_FMA:
        term = bitwuzla_mk_term(d_tm, kind, fp_args.size(), fp_args.data());
        break;

      // FP indexed
      case BITWUZLA_KIND_FP_TO_FP_FROM_BV:
        term = bitwuzla_mk_term1_indexed2(d_tm, kind, bv_args[0], 5, 11);
        break;

      case BITWUZLA_KIND_FP_TO_FP_FROM_SBV:
      case BITWUZLA_KIND_FP_TO_FP_FROM_UBV:
        term = bitwuzla_mk_term2_indexed2(
            d_tm, kind, fp_args[0], bv_args[0], 5, 11);
        break;

      case BITWUZLA_KIND_FP_TO_FP_FROM_FP:
        term = bitwuzla_mk_term2_indexed2(
            d_tm, kind, fp_args[0], fp_args[1], 5, 11);
        break;

      case BITWUZLA_KIND_FP_TO_SBV:
      case BITWUZLA_KIND_FP_TO_UBV:
        term =
            bitwuzla_mk_term2_indexed1(d_tm, kind, fp_args[0], fp_args[1], 16);
        break;

      // Others
      case BITWUZLA_KIND_ITE: {
        std::vector<BitwuzlaTerm> args = {bool_args[0], bv_args[0], bv_args[1]};
        term = bitwuzla_mk_term(d_tm, kind, args.size(), args.data());
        break;
      }

      default: break;
    }
    // No unhandled BitwuzlaKind
    ASSERT_NE(term, nullptr);

    size_t size;
    BitwuzlaTerm *children = bitwuzla_term_get_children(term, &size);

    if (bitwuzla_term_is_const(term) || bitwuzla_term_is_var(term)
        || bitwuzla_term_is_value(term))
    {
      ASSERT_EQ(size, 0);
      ASSERT_EQ(children, nullptr);
      continue;
    }

    ASSERT_GT(size, 0);
    ASSERT_NE(children, nullptr);
    for (size_t i = 0; i < size; ++i)
    {
      assert(children[i] != nullptr);
      ASSERT_NE(children[i], nullptr);
    }

    BitwuzlaTerm tterm;
    if (bitwuzla_term_get_kind(term) == BITWUZLA_KIND_CONST_ARRAY)
    {
      ASSERT_EQ(size, 1);
      tterm = bitwuzla_mk_const_array(
          d_tm, bitwuzla_term_get_sort(term), children[0]);
    }
    else
    {
      kind = bitwuzla_term_get_kind(term);
      if (bitwuzla_term_is_indexed(term))
      {
        size_t num_indices;
        uint64_t *indices = bitwuzla_term_get_indices(term, &num_indices);
        tterm             = bitwuzla_mk_term_indexed(
            d_tm, kind, size, children, num_indices, indices);
      }
      else if (kind == BITWUZLA_KIND_LAMBDA || kind == BITWUZLA_KIND_FORALL
               || kind == BITWUZLA_KIND_EXISTS)
      {
        // TODO: variables are already bound and can't be passed to mk_term
        // create new vars and substitute
        tterm = term;
      }
      else
      {
        assert(kind != BITWUZLA_KIND_BV_NOT || size == 1);
        tterm = bitwuzla_mk_term(d_tm, kind, size, children);
      }
    }
    ASSERT_EQ(tterm, term);
  }

  size_t size;

  ASSERT_EQ(bitwuzla_term_get_kind(d_bv_const8), BITWUZLA_KIND_CONSTANT);
  ASSERT_EQ(bitwuzla_term_get_children(d_bv_const8, &size), nullptr);
  ASSERT_EQ(size, 0);

  ASSERT_EQ(bitwuzla_term_get_kind(d_rm_const), BITWUZLA_KIND_CONSTANT);
  ASSERT_EQ(bitwuzla_term_get_children(d_rm_const, &size), nullptr);
  ASSERT_EQ(size, 0);

  ASSERT_EQ(bitwuzla_term_get_kind(d_un_const), BITWUZLA_KIND_CONSTANT);
  ASSERT_EQ(bitwuzla_term_get_children(d_un_const, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm bv_var = bitwuzla_mk_var(d_tm, d_bv_sort16, nullptr);
  ASSERT_EQ(bitwuzla_term_get_kind(bv_var), BITWUZLA_KIND_VARIABLE);
  ASSERT_EQ(bitwuzla_term_get_children(bv_var, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm rm_val = bitwuzla_mk_rm_value(d_tm, BITWUZLA_RM_RNA);
  ASSERT_EQ(bitwuzla_term_get_kind(rm_val), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(rm_val, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm fp_from_real_val =
      bitwuzla_mk_fp_from_real(d_tm, d_fp_sort16, rm_val, "1.1");
  ASSERT_EQ(bitwuzla_term_get_kind(fp_from_real_val), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(fp_from_real_val, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm fp_from_real =
      bitwuzla_mk_fp_from_real(d_tm, d_fp_sort16, d_rm_const, "1.1");
  ASSERT_EQ(bitwuzla_term_get_kind(fp_from_real), BITWUZLA_KIND_ITE);
  ASSERT_NE(bitwuzla_term_get_children(fp_from_real, &size), nullptr);
  ASSERT_EQ(size, 3);

  BitwuzlaTerm fp_from_rational_val =
      bitwuzla_mk_fp_from_rational(d_tm, d_fp_sort16, rm_val, "1", "2");
  ASSERT_EQ(bitwuzla_term_get_kind(fp_from_rational_val), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(fp_from_rational_val, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm fp_from_rational =
      bitwuzla_mk_fp_from_rational(d_tm, d_fp_sort16, d_rm_const, "1", "2");
  ASSERT_EQ(bitwuzla_term_get_kind(fp_from_rational), BITWUZLA_KIND_ITE);
  ASSERT_NE(bitwuzla_term_get_children(fp_from_rational, &size), nullptr);
  ASSERT_EQ(size, 3);

  BitwuzlaTerm fp_nan = bitwuzla_mk_fp_nan(d_tm, d_fp_sort16);
  ASSERT_EQ(bitwuzla_term_get_kind(fp_nan), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(fp_nan, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm bv_one = bitwuzla_mk_bv_one(d_tm, d_bv_sort16);
  ASSERT_EQ(bitwuzla_term_get_kind(bv_one), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(bv_one, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm bv_val = bitwuzla_mk_bv_value(d_tm, d_bv_sort16, "43", 10);
  ASSERT_EQ(bitwuzla_term_get_kind(bv_val), BITWUZLA_KIND_VALUE);
  ASSERT_EQ(bitwuzla_term_get_children(bv_val, &size), nullptr);
  ASSERT_EQ(size, 0);

  BitwuzlaTerm const_array = bitwuzla_mk_const_array(d_tm, array_sort, bv_val);
  ASSERT_EQ(bitwuzla_term_get_kind(const_array), BITWUZLA_KIND_CONST_ARRAY);
  ASSERT_NE(bitwuzla_term_get_children(const_array, &size), nullptr);
  ASSERT_EQ(size, 1);
}

TEST_F(TestCApi, substitute)
{
  std::vector<BitwuzlaSort> domain = {d_bv_sort16, d_bv_sort16, d_bv_sort16};
  BitwuzlaSort fun_sort =
      bitwuzla_mk_fun_sort(d_tm, domain.size(), domain.data(), d_bool_sort);
  BitwuzlaSort array_sort =
      bitwuzla_mk_array_sort(d_tm, d_bv_sort16, d_bv_sort16);

  BitwuzlaTerm bv_const = bitwuzla_mk_const(d_tm, d_bv_sort16, 0);
  BitwuzlaTerm bv_value = bitwuzla_mk_bv_value(d_tm, d_bv_sort16, "143", 10);

  // simple substitution const -> value
  {
    std::vector<BitwuzlaTerm> keys   = {bv_const};
    std::vector<BitwuzlaTerm> values = {bv_value};
    BitwuzlaTerm result              = bitwuzla_substitute_term(
        bv_const, keys.size(), keys.data(), values.data());
    ASSERT_EQ(result, bv_value);
  }

  // (sdiv x y) -> (sdiv value y)
  {
    BitwuzlaTerm x = bitwuzla_mk_const(d_tm, d_bv_sort16, 0);
    BitwuzlaTerm y = bitwuzla_mk_const(d_tm, d_bv_sort16, 0);

    std::vector<BitwuzlaTerm> keys   = {x};
    std::vector<BitwuzlaTerm> values = {bv_value};

    BitwuzlaTerm result = bitwuzla_substitute_term(
        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_SDIV, x, y),
        keys.size(),
        keys.data(),
        values.data());
    ASSERT_EQ(result,
              bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_SDIV, bv_value, y));
  }

  // partial substitution of variables in quantified formula
  {
    std::vector<BitwuzlaTerm> args = {bitwuzla_mk_const(d_tm, fun_sort, 0),
                                      bitwuzla_mk_var(d_tm, d_bv_sort16, "x"),
                                      bitwuzla_mk_var(d_tm, d_bv_sort16, "y"),
                                      bitwuzla_mk_var(d_tm, d_bv_sort16, "z")};
    args.push_back(
        bitwuzla_mk_term(d_tm, BITWUZLA_KIND_APPLY, args.size(), args.data()));
    BitwuzlaTerm q = bitwuzla_mk_term(
        d_tm, BITWUZLA_KIND_FORALL, args.size() - 1, args.data() + 1);

    std::vector<BitwuzlaTerm> keys   = {args[1], args[2]};
    std::vector<BitwuzlaTerm> values = {
        bitwuzla_mk_const(d_tm, d_bv_sort16, 0),
        bitwuzla_mk_const(d_tm, d_bv_sort16, 0)};

    std::vector<BitwuzlaTerm> args_apply = {
        args[0], values[0], values[1], args[3]};
    BitwuzlaTerm apply = bitwuzla_mk_term(
        d_tm, BITWUZLA_KIND_APPLY, args_apply.size(), args_apply.data());
    std::vector<BitwuzlaTerm> args_expected = {args[3], apply};
    BitwuzlaTerm expected =
        bitwuzla_mk_term(d_tm, BITWUZLA_KIND_FORALL, 2, args_expected.data());

    BitwuzlaTerm result =
        bitwuzla_substitute_term(q, keys.size(), keys.data(), values.data());
    ASSERT_EQ(result, expected);
  }

  // substitute term in constant array
  {
    BitwuzlaTerm term        = bitwuzla_mk_const(d_tm, d_bv_sort16, 0);
    BitwuzlaTerm const_array = bitwuzla_mk_const_array(d_tm, array_sort, term);

    std::vector<BitwuzlaTerm> keys   = {term};
    std::vector<BitwuzlaTerm> values = {bv_value};

    BitwuzlaTerm result = bitwuzla_substitute_term(
        const_array, keys.size(), keys.data(), values.data());

    BitwuzlaTerm expected = bitwuzla_mk_const_array(d_tm, array_sort, bv_value);
    ASSERT_EQ(result, expected);
    ASSERT_EQ(bitwuzla_term_get_kind(result), BITWUZLA_KIND_CONST_ARRAY);
  }
}

TEST_F(TestCApi, substitute2)
{
  BitwuzlaSort bv8   = bitwuzla_mk_bv_sort(d_tm, 8);
  BitwuzlaTerm x     = bitwuzla_mk_const(d_tm, bv8, "x");
  BitwuzlaTerm one   = bitwuzla_mk_bv_one(d_tm, bv8);
  BitwuzlaTerm btrue = bitwuzla_mk_true(d_tm);
  BitwuzlaTerm addxx = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, x, x);
  BitwuzlaTerm addoo = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, one, one);

  std::vector<BitwuzlaTerm> keys;
  std::vector<BitwuzlaTerm> values;

  keys = {x}, values = {one};
  ASSERT_DEATH(
      bitwuzla_substitute_term(0, keys.size(), keys.data(), values.data()),
      d_error_inv_term);
  keys = {0};
  ASSERT_DEATH(
      bitwuzla_substitute_term(addxx, keys.size(), keys.data(), values.data()),
      d_error_inv_term);
  keys = {x}, values = {0};
  ASSERT_DEATH(
      bitwuzla_substitute_term(addxx, keys.size(), keys.data(), values.data()),
      d_error_inv_term);
  keys = {one}, values = {btrue};
  ASSERT_DEATH(
      bitwuzla_substitute_term(addxx, keys.size(), keys.data(), values.data()),
      "invalid term substitution");

  keys = {x}, values = {one};
  ASSERT_EQ(
      bitwuzla_substitute_term(addxx, keys.size(), keys.data(), values.data()),
      addoo);
  keys = {one}, values = {x};
  ASSERT_EQ(
      bitwuzla_substitute_term(addxx, keys.size(), keys.data(), values.data()),
      addxx);

  // simultaneous substitution
  BitwuzlaTerm y     = bitwuzla_mk_const(d_tm, bv8, "y");
  BitwuzlaTerm addxy = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, x, y);
  BitwuzlaTerm addyo = bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, y, one);
  keys = {x, y}, values = {y, btrue};
  ASSERT_DEATH(
      bitwuzla_substitute_term(addxy, keys.size(), keys.data(), values.data()),
      "invalid term substitution");
  values = {y, one};
  ASSERT_EQ(
      bitwuzla_substitute_term(addxy, keys.size(), keys.data(), values.data()),
      addyo);

  std::vector<BitwuzlaTerm> terms    = {addxx, addxy};
  std::vector<BitwuzlaTerm> expected = {
      bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, y, y),
      bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, y, x)};
  keys = {x, y}, values = {y, x};
  bitwuzla_substitute_terms(
      terms.size(), terms.data(), keys.size(), keys.data(), values.data());
  for (size_t i = 0; i < expected.size(); ++i)
  {
    ASSERT_EQ(terms[i], expected[i]);
  }
}

TEST_F(TestCApi, term_copy_release)
{
  BitwuzlaTermManager *tm = bitwuzla_term_manager_new();

  ASSERT_TRUE(tm->d_alloc_terms.empty());

  auto t1 = bitwuzla_mk_true(tm);
  ASSERT_EQ(t1->d_refs, 1);
  ASSERT_EQ(tm->d_alloc_terms.size(), 1);

  auto t1c = bitwuzla_term_copy(t1);
  ASSERT_EQ(t1->d_refs, 2);
  ASSERT_EQ(tm->d_alloc_terms.size(), 1);
  ASSERT_EQ(t1, t1c);

  auto t2 = bitwuzla_mk_true(tm);
  ASSERT_EQ(tm->d_alloc_terms.size(), 1);
  ASSERT_EQ(t1, t2);
  ASSERT_EQ(t1->d_refs, 3);

  auto t3 = bitwuzla_mk_false(tm);
  ASSERT_EQ(tm->d_alloc_terms.size(), 2);
  ASSERT_EQ(t3->d_refs, 1);

  bitwuzla_term_release(t3);
  ASSERT_EQ(tm->d_alloc_terms.size(), 1);

  bitwuzla_term_release(t2);
  ASSERT_EQ(t1->d_refs, 2);
  bitwuzla_term_release(t1c);
  ASSERT_EQ(t1->d_refs, 1);
  bitwuzla_term_release(t1);
  ASSERT_TRUE(tm->d_alloc_terms.empty());

  bitwuzla_term_manager_delete(tm);
}

TEST_F(TestCApi, sort_copy_release)
{
  BitwuzlaTermManager *tm = bitwuzla_term_manager_new();

  ASSERT_TRUE(tm->d_alloc_sorts.empty());

  auto s1 = bitwuzla_mk_bool_sort(tm);
  ASSERT_EQ(s1->d_refs, 1);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);

  auto s1c = bitwuzla_sort_copy(s1);
  ASSERT_EQ(s1->d_refs, 2);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);
  ASSERT_EQ(s1, s1c);

  auto s2 = bitwuzla_mk_bool_sort(tm);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);
  ASSERT_EQ(s1, s2);
  ASSERT_EQ(s1->d_refs, 3);

  auto s3 = bitwuzla_mk_bv_sort(tm, 1);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 2);
  ASSERT_EQ(s3->d_refs, 1);

  bitwuzla_sort_release(s3);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);

  bitwuzla_sort_release(s2);
  ASSERT_EQ(s1->d_refs, 2);
  bitwuzla_sort_release(s1c);
  ASSERT_EQ(s1->d_refs, 1);
  bitwuzla_sort_release(s1);
  ASSERT_TRUE(tm->d_alloc_sorts.empty());

  bitwuzla_term_manager_delete(tm);
}

TEST_F(TestCApi, term_mgr_release)
{
  BitwuzlaTermManager *tm = bitwuzla_term_manager_new();

  auto t1 = bitwuzla_mk_true(tm);
  ASSERT_EQ(t1->d_refs, 1);
  ASSERT_EQ(tm->d_alloc_terms.size(), 1);
  ASSERT_TRUE(tm->d_alloc_sorts.empty());

  auto s1 = bitwuzla_mk_bool_sort(tm);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);
  auto s2 = bitwuzla_sort_copy(s1);
  ASSERT_EQ(tm->d_alloc_sorts.size(), 1);
  ASSERT_EQ(s2->d_refs, 2);

  bitwuzla_term_manager_release(tm);
  ASSERT_TRUE(tm->d_alloc_terms.empty());
  ASSERT_TRUE(tm->d_alloc_sorts.empty());

  bitwuzla_term_manager_delete(tm);
}

TEST_F(TestCApi, term_print1)
{
  ASSERT_DEATH(bitwuzla_term_to_string(0), d_error_inv_term);
  BitwuzlaTerm a = bitwuzla_mk_const(d_tm, d_bv_sort1, "a");
  BitwuzlaTerm t = bitwuzla_mk_term1(d_tm, BITWUZLA_KIND_BV_NOT, a);
  ASSERT_EQ(std::string(bitwuzla_term_to_string(t)), "(bvnot a)");
}

TEST_F(TestCApi, term_print2)
{
  BitwuzlaSort fn1_1 = bitwuzla_mk_fun_sort(d_tm, 1, &d_bv_sort1, d_bv_sort1);
  BitwuzlaTerm t     = bitwuzla_mk_const(d_tm, fn1_1, "f");
  ASSERT_EQ(std::string(bitwuzla_term_to_string(t)), "f");
}

TEST_F(TestCApi, term_print3)
{
  BitwuzlaSort ar1_1 = bitwuzla_mk_array_sort(d_tm, d_bv_sort1, d_bv_sort1);
  BitwuzlaTerm t     = bitwuzla_mk_const(d_tm, ar1_1, "a");
  ASSERT_EQ(std::string(bitwuzla_term_to_string(t)), "a");
}

TEST_F(TestCApi, arrayfun)
{
  BitwuzlaSort bvsort = bitwuzla_mk_bv_sort(d_tm, 4);
  std::vector<BitwuzlaSort> domain({bvsort});
  BitwuzlaSort funsort =
      bitwuzla_mk_fun_sort(d_tm, domain.size(), domain.data(), bvsort);
  BitwuzlaSort arrsort = bitwuzla_mk_array_sort(d_tm, bvsort, bvsort);
  BitwuzlaTerm f       = bitwuzla_mk_const(d_tm, funsort, "f");
  BitwuzlaTerm a       = bitwuzla_mk_const(d_tm, arrsort, "a");
  ASSERT_TRUE(bitwuzla_term_get_sort(f) != bitwuzla_term_get_sort(a));
  ASSERT_TRUE(bitwuzla_term_is_fun(f));
  ASSERT_TRUE(!bitwuzla_term_is_fun(a));
  ASSERT_TRUE(!bitwuzla_term_is_array(f));
  ASSERT_TRUE(bitwuzla_term_is_array(a));
}

/* -------------------------------------------------------------------------- */
/* Termination function                                                       */
/* -------------------------------------------------------------------------- */

namespace {
int32_t
test_terminate1(void *state)
{
  (void) state;
  return true;
}
struct terminator_state
{
  struct timeval start;
  int32_t time_limit_ms;
};

static int32_t
test_terminate2(void *state)
{
  struct terminator_state *tstate = (struct terminator_state *) state;
  struct timeval now;
  gettimeofday(&now, NULL);
  if (((now.tv_sec - tstate->start.tv_sec) * 1000
       + (now.tv_usec - tstate->start.tv_usec) / 1000)
      >= tstate->time_limit_ms)
  {
    return 1;
  }
  return 0;
}
}  // namespace

TEST_F(TestCApi, terminate)
{
  BitwuzlaSort bv_sort4 = bitwuzla_mk_bv_sort(d_tm, 4);
  BitwuzlaTerm x        = bitwuzla_mk_const(d_tm, bv_sort4, nullptr);
  BitwuzlaTerm s        = bitwuzla_mk_const(d_tm, bv_sort4, nullptr);
  BitwuzlaTerm t        = bitwuzla_mk_const(d_tm, bv_sort4, nullptr);
  BitwuzlaTerm a        = bitwuzla_mk_term2(
      d_tm,
      BITWUZLA_KIND_AND,
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_EQUAL,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_ADD, x, x),
                        bitwuzla_mk_bv_value_uint64(d_tm, bv_sort4, 3)),
      bitwuzla_mk_term1(
          d_tm,
          BITWUZLA_KIND_NOT,
          bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_UADD_OVERFLOW, x, x)));
  BitwuzlaTerm b = bitwuzla_mk_term2(
      d_tm,
      BITWUZLA_KIND_DISTINCT,
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_BV_MUL,
                        s,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_MUL, x, t)),
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_BV_MUL,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_MUL, s, x),
                        t));
  // solved by rewriting
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "bitblast");
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    bitwuzla_assert(bitwuzla, a);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "prop");
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    bitwuzla_assert(bitwuzla, a);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
  // not solved by rewriting, should be terminated when configured
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "bitblast");
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    bitwuzla_assert(bitwuzla, b);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNSAT);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option(opts, BITWUZLA_OPT_REWRITE_LEVEL, 0);
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "bitblast");
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    bitwuzla_set_termination_callback(bitwuzla, test_terminate1, nullptr);
    bitwuzla_assert(bitwuzla, b);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNKNOWN);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option(opts, BITWUZLA_OPT_REWRITE_LEVEL, 0);
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "prop");
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    bitwuzla_set_termination_callback(bitwuzla, test_terminate1, nullptr);
    bitwuzla_assert(bitwuzla, b);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNKNOWN);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
}

TEST_F(TestCApi, terminate_sat)
{
  BitwuzlaSort bv_sort32 = bitwuzla_mk_bv_sort(d_tm, 32);
  BitwuzlaTerm x         = bitwuzla_mk_const(d_tm, bv_sort32, nullptr);
  BitwuzlaTerm s         = bitwuzla_mk_const(d_tm, bv_sort32, nullptr);
  BitwuzlaTerm t         = bitwuzla_mk_const(d_tm, bv_sort32, nullptr);
  BitwuzlaTerm b         = bitwuzla_mk_term2(
      d_tm,
      BITWUZLA_KIND_DISTINCT,
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_BV_MUL,
                        s,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_MUL, x, t)),
      bitwuzla_mk_term2(d_tm,
                        BITWUZLA_KIND_BV_MUL,
                        bitwuzla_mk_term2(d_tm, BITWUZLA_KIND_BV_MUL, s, x),
                        t));
  // not solved by bit-blasting without preprocessing, should be terminated in
  // the SAT solver when configured
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "bitblast");
    bitwuzla_set_option(opts, BITWUZLA_OPT_PREPROCESS, 0);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    struct terminator_state state;
    gettimeofday(&state.start, NULL);
    state.time_limit_ms = 1000;
    bitwuzla_set_termination_callback(bitwuzla, test_terminate2, &state);
    bitwuzla_assert(bitwuzla, b);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNKNOWN);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
  {
    BitwuzlaOptions *opts = bitwuzla_options_new();
    bitwuzla_set_option_mode(opts, BITWUZLA_OPT_BV_SOLVER, "prop");
    bitwuzla_set_option(opts, BITWUZLA_OPT_PREPROCESS, 0);
    Bitwuzla *bitwuzla = bitwuzla_new(d_tm, opts);
    struct terminator_state state;
    gettimeofday(&state.start, NULL);
    state.time_limit_ms = 1000;
    bitwuzla_set_termination_callback(bitwuzla, test_terminate2, &state);
    bitwuzla_assert(bitwuzla, b);
    ASSERT_EQ(bitwuzla_check_sat(bitwuzla), BITWUZLA_UNKNOWN);
    bitwuzla_options_delete(opts);
    bitwuzla_delete(bitwuzla);
  }
}

/* -------------------------------------------------------------------------- */
/* Abort callback function                                                    */
/* -------------------------------------------------------------------------- */

namespace {
class TestException : public std::exception
{
  TestException(const std::string &msg) : d_msg(msg) {}
  std::string d_msg;
};

void
test_abort(const char *msg)
{
  std::rethrow_if_nested(TestException(std::string(msg)));
}
}  // namespace

TEST_F(TestCApi, abort_callback)
{
  bitwuzla_set_abort_callback(nullptr);
  bitwuzla_set_abort_callback(test_abort);
  try
  {
    bitwuzla_kind_to_string(BITWUZLA_KIND_NUM_KINDS);
  }
  catch (TestException &e)
  {
    ASSERT_NE(e.d_msg.find("invalid term kind"), std::string::npos);
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
