#include "api/checks.h"
#include "api/cpp/bitwuzla.h"
#include "test/unit/test.h"

namespace bzla::test {

class TestApi : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    //    d_bv_sort1  = bitwuzla_mk_bv_sort(d_bzla, 1);
    //    d_bv_sort8  = bitwuzla_mk_bv_sort(d_bzla, 8);
    //    d_bv_sort23 = bitwuzla_mk_bv_sort(d_bzla, 23);
    //    d_bv_sort32 = bitwuzla_mk_bv_sort(d_bzla, 32);
    //
    //    d_fp_sort16 = bitwuzla_mk_fp_sort(d_bzla, 5, 11);
    //    d_fp_sort32 = bitwuzla_mk_fp_sort(d_bzla, 8, 24);
    //    d_rm_sort   = bitwuzla_mk_rm_sort(d_bzla);
    //
    //    d_arr_sort_bvfp = bitwuzla_mk_array_sort(d_bzla, d_bv_sort8,
    //    d_fp_sort16); d_arr_sort_fpbv = bitwuzla_mk_array_sort(d_bzla,
    //    d_fp_sort16, d_bv_sort8); d_arr_sort_bv   =
    //    bitwuzla_mk_array_sort(d_bzla, d_bv_sort32, d_bv_sort8);
    //
    //    d_fun_domain_sort = {d_bv_sort8, d_fp_sort16, d_bv_sort32};
    //    d_fun_sort        = bitwuzla_mk_fun_sort(
    //        d_bzla, d_fun_domain_sort.size(), d_fun_domain_sort.data(),
    //        d_bv_sort8);
    //    d_fun_sort_fp = bitwuzla_mk_fun_sort(d_bzla,
    //                                         d_fun_domain_sort.size(),
    //                                         d_fun_domain_sort.data(),
    //                                         d_fp_sort16);
    //    d_true        = bitwuzla_mk_true(d_bzla);
    //    d_bv_one1     = bitwuzla_mk_bv_one(d_bzla, d_bv_sort1);
    //    d_bv_ones23   = bitwuzla_mk_bv_ones(d_bzla, d_bv_sort23);
    //    d_bv_mins8    = bitwuzla_mk_bv_min_signed(d_bzla, d_bv_sort8);
    //    d_bv_maxs8    = bitwuzla_mk_bv_max_signed(d_bzla, d_bv_sort8);
    //    d_bv_zero8    = bitwuzla_mk_bv_zero(d_bzla, d_bv_sort8);
    //    d_fp_pzero32  = bitwuzla_mk_fp_pos_zero(d_bzla, d_fp_sort32);
    //    d_fp_nzero32  = bitwuzla_mk_fp_neg_zero(d_bzla, d_fp_sort32);
    //    d_fp_pinf32   = bitwuzla_mk_fp_pos_inf(d_bzla, d_fp_sort32);
    //    d_fp_ninf32   = bitwuzla_mk_fp_neg_inf(d_bzla, d_fp_sort32);
    //    d_fp_nan32    = bitwuzla_mk_fp_nan(d_bzla, d_fp_sort32);
    //
    //    d_bv_const1  = bitwuzla_mk_const(d_bzla, d_bv_sort1, "bv_const1");
    //    d_bv_const8  = bitwuzla_mk_const(d_bzla, d_bv_sort8, "bv_const8");
    //    d_fp_const16 = bitwuzla_mk_const(d_bzla, d_fp_sort16, "fp_const16");
    //    d_rm_const   = bitwuzla_mk_const(d_bzla, d_rm_sort, "rm_const");
    //
    //    d_rm_rna = bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_RNA);
    //    d_rm_rne = bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_RNE);
    //    d_rm_rtn = bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_RTN);
    //    d_rm_rtp = bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_RTP);
    //    d_rm_rtz = bitwuzla_mk_rm_value(d_bzla, BITWUZLA_RM_RTZ);
    //
    //    d_fun        = bitwuzla_mk_const(d_bzla, d_fun_sort, "fun");
    //    d_fun_fp     = bitwuzla_mk_const(d_bzla, d_fun_sort_fp, "fun_fp");
    //    d_array_fpbv = bitwuzla_mk_const(d_bzla, d_arr_sort_fpbv,
    //    "array_fpbv"); d_array      = bitwuzla_mk_const(d_bzla, d_arr_sort_bv,
    //    "array"); d_store      = bitwuzla_mk_term3(d_bzla,
    //                                BITWUZLA_KIND_ARRAY_STORE,
    //                                d_array,
    //                                bitwuzla_mk_const(d_bzla, d_bv_sort32,
    //                                "store"), d_bv_zero8);
    //
    //    d_var1      = bitwuzla_mk_var(d_bzla, d_bv_sort8, "var1");
    //    d_var2      = bitwuzla_mk_var(d_bzla, d_bv_sort8, "var2");
    //    d_bound_var = bitwuzla_mk_var(d_bzla, d_bv_sort8, "bount_var");
    //    d_bool_var =
    //        bitwuzla_mk_var(d_bzla, bitwuzla_mk_bool_sort(d_bzla),
    //        "bool_var");
    //
    //    d_not_bv_const1 =
    //        bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, d_bv_const1);
    //    d_and_bv_const1 =
    //        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_AND, d_bv_one1,
    //        d_bv_const1);
    //    d_eq_bv_const8 =
    //        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, d_bv_const8,
    //        d_bv_zero8);
    //
    //    const BitwuzlaTerm *lambda_body = bitwuzla_mk_term2(
    //        d_bzla, BITWUZLA_KIND_BV_ADD, d_bound_var, d_bv_const8);
    //    d_lambda = bitwuzla_mk_term2(
    //        d_bzla, BITWUZLA_KIND_LAMBDA, d_bound_var, lambda_body);
    //    d_bool_lambda_body =
    //        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, d_bool_var,
    //        d_true);
    //    d_bool_lambda = bitwuzla_mk_term2(
    //        d_bzla, BITWUZLA_KIND_LAMBDA, d_bool_var, d_bool_lambda_body);
    //    d_bool_apply =
    //        bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_APPLY, d_bool_lambda,
    //        d_true);
    //
    //    /* associated with other Bitwuzla instance */
    //    d_other_bzla            = bitwuzla_new();
    //    d_other_bv_sort1        = bitwuzla_mk_bv_sort(d_other_bzla, 1);
    //    d_other_bv_sort8        = bitwuzla_mk_bv_sort(d_other_bzla, 8);
    //    d_other_fp_sort16       = bitwuzla_mk_fp_sort(d_other_bzla, 5, 11);
    //    d_other_fun_domain_sort = {d_other_bv_sort8, d_other_bv_sort8};
    //    d_other_arr_sort_bv     = bitwuzla_mk_array_sort(
    //        d_other_bzla, d_other_bv_sort8, d_other_bv_sort8);
    //
    //    d_other_true     = bitwuzla_mk_true(d_other_bzla);
    //    d_other_bv_one1  = bitwuzla_mk_bv_one(d_other_bzla, d_other_bv_sort1);
    //    d_other_bv_zero8 = bitwuzla_mk_bv_zero(d_other_bzla,
    //    d_other_bv_sort8);
    //
    //    d_other_bv_const8 =
    //        bitwuzla_mk_const(d_other_bzla, d_other_bv_sort8, "bv_const8");
    //
    //    d_other_exists_var =
    //        bitwuzla_mk_var(d_other_bzla, d_other_bv_sort8, "exists_var");
    //    d_other_exists = bitwuzla_mk_term2(
    //        d_other_bzla,
    //        BITWUZLA_KIND_EXISTS,
    //        d_other_exists_var,
    //        bitwuzla_mk_term2(d_other_bzla,
    //                          BITWUZLA_KIND_EQUAL,
    //                          d_other_bv_zero8,
    //                          bitwuzla_mk_term2(d_other_bzla,
    //                                            BITWUZLA_KIND_BV_MUL,
    //                                            d_other_bv_const8,
    //                                            d_other_exists_var)));
  }

  bitwuzla::Options d_options;

  // sorts
  bitwuzla::Sort d_arr_sort_bv;
  bitwuzla::Sort d_arr_sort_bvfp;
  bitwuzla::Sort d_arr_sort_fpbv;
  bitwuzla::Sort d_bv_sort1;
  bitwuzla::Sort d_bv_sort23;
  bitwuzla::Sort d_bv_sort32;
  bitwuzla::Sort d_bv_sort8;
  bitwuzla::Sort d_fp_sort16;
  bitwuzla::Sort d_fp_sort32;
  bitwuzla::Sort d_fun_sort;
  bitwuzla::Sort d_fun_sort_fp;
  std::vector<bitwuzla::Sort> d_fun_domain_sorts;
  bitwuzla::Sort d_rm_sort;
  // terms
  bitwuzla::Term d_true;
  bitwuzla::Term d_bv_one1;
  bitwuzla::Term d_bv_ones23;
  bitwuzla::Term d_bv_zero8;
  bitwuzla::Term d_bv_mins8;
  bitwuzla::Term d_bv_maxs8;
  bitwuzla::Term d_fp_pzero32;
  bitwuzla::Term d_fp_nzero32;
  bitwuzla::Term d_fp_pinf32;
  bitwuzla::Term d_fp_ninf32;
  bitwuzla::Term d_fp_nan32;

  bitwuzla::Term d_bv_const1;
  bitwuzla::Term d_bv_const8;
  bitwuzla::Term d_fp_const16;
  bitwuzla::Term d_rm_const;

  bitwuzla::Term d_rm_rna;
  bitwuzla::Term d_rm_rne;
  bitwuzla::Term d_rm_rtn;
  bitwuzla::Term d_rm_rtp;
  bitwuzla::Term d_rm_rtz;

  bitwuzla::Term d_fun;
  bitwuzla::Term d_fun_fp;
  bitwuzla::Term d_array_fpbv;
  bitwuzla::Term d_array;
  bitwuzla::Term d_store;

  bitwuzla::Term d_var1;
  bitwuzla::Term d_var2;
  bitwuzla::Term d_bound_var;
  bitwuzla::Term d_bool_var;

  bitwuzla::Term d_not_bv_const1;
  bitwuzla::Term d_and_bv_const1;
  bitwuzla::Term d_eq_bv_const8;
  bitwuzla::Term d_lambda;
  bitwuzla::Term d_bool_lambda;
  bitwuzla::Term d_bool_lambda_body;
  bitwuzla::Term d_bool_apply;

  ///* not associated with d_bzla */
  // Bitwuzla *d_other_bzla;
  // const BitwuzlaSort *d_other_arr_sort_bv;
  // const BitwuzlaSort *d_other_bv_sort1;
  // const BitwuzlaSort *d_other_bv_sort8;
  // const BitwuzlaSort *d_other_fp_sort16;
  // std::vector<const BitwuzlaSort *> d_other_fun_domain_sort;
  // const BitwuzlaTerm *d_other_bv_one1;
  // const BitwuzlaTerm *d_other_bv_zero8;
  // const BitwuzlaTerm *d_other_exists_var;
  // const BitwuzlaTerm *d_other_bv_const8;
  // const BitwuzlaTerm *d_other_true;
  // const BitwuzlaTerm *d_other_exists;
};

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

TEST_F(TestApi, kind_to_string)
{
  ASSERT_EQ(std::to_string(bitwuzla::Kind::CONSTANT), std::string("CONSTANT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::CONST_ARRAY),
            std::string("CONST_ARRAY"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::VARIABLE), std::string("VARIABLE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::VALUE), std::string("VALUE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::AND), std::string("AND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::APPLY), std::string("APPLY"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::ARRAY_SELECT),
            std::string("SELECT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::ARRAY_STORE), std::string("STORE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ADD), std::string("BV_ADD"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_AND), std::string("BV_AND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ASHR), std::string("BV_ASHR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_COMP), std::string("BV_COMP"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_CONCAT),
            std::string("BV_CONCAT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_DEC), std::string("BV_DEC"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_INC), std::string("BV_INC"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_MUL), std::string("BV_MUL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_NAND), std::string("BV_NAND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_NEG), std::string("BV_NEG"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_NOR), std::string("BV_NOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_NOT), std::string("BV_NOT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_OR), std::string("BV_OR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_REDAND),
            std::string("BV_REDAND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_REDOR), std::string("BV_REDOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_REDXOR),
            std::string("BV_REDXOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ROL), std::string("BV_ROL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ROR), std::string("BV_ROR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SADD_OVERFLOW),
            std::string("BV_SADDO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SDIV_OVERFLOW),
            std::string("BV_SDIVO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SDIV), std::string("BV_SDIV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SGE), std::string("BV_SGE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SGT), std::string("BV_SGT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SHL), std::string("BV_SHL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SHR), std::string("BV_SHR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SLE), std::string("BV_SLE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SLT), std::string("BV_SLT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SMOD), std::string("BV_SMOD"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SMUL_OVERFLOW),
            std::string("BV_SMULO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SREM), std::string("BV_SREM"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SSUB_OVERFLOW),
            std::string("BV_SSUBO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SUB), std::string("BV_SUB"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UADD_OVERFLOW),
            std::string("BV_UADDO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UDIV), std::string("BV_UDIV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UGE), std::string("BV_UGE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UGT), std::string("BV_UGT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ULE), std::string("BV_ULE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ULT), std::string("BV_ULT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UMUL_OVERFLOW),
            std::string("BV_UMULO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_UREM), std::string("BV_UREM"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_USUB_OVERFLOW),
            std::string("BV_USUBO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_XNOR), std::string("BV_XNOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_XOR), std::string("BV_XOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::DISTINCT), std::string("DISTINCT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::EQUAL), std::string("EQUAL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::EXISTS), std::string("EXISTS"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FORALL), std::string("FORALL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_ABS), std::string("FP_ABS"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_ADD), std::string("FP_ADD"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_DIV), std::string("FP_DIV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_EQUAL), std::string("FP_EQUAL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_FMA), std::string("FP_FMA"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_FP), std::string("FP_FP"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_GEQ), std::string("FP_GEQ"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_GT), std::string("FP_GT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_INF),
            std::string("FP_IS_INF"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_NAN),
            std::string("FP_IS_NAN"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_NEG),
            std::string("FP_IS_NEG"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_NORMAL),
            std::string("FP_IS_NORMAL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_POS),
            std::string("FP_IS_POS"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_SUBNORMAL),
            std::string("FP_IS_SUBNORMAL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_IS_ZERO),
            std::string("FP_IS_ZERO"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_LEQ), std::string("FP_LEQ"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_LT), std::string("FP_LT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_MAX), std::string("FP_MAX"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_MIN), std::string("FP_MIN"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_MUL), std::string("FP_MUL"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_NEG), std::string("FP_NEG"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_REM), std::string("FP_REM"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_RTI), std::string("FP_RTI"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_SQRT), std::string("FP_SQRT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_SUB), std::string("FP_SUB"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::IFF), std::string("IFF"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::IMPLIES), std::string("IMPLIES"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::ITE), std::string("ITE"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::LAMBDA), std::string("LAMBDA"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::NOT), std::string("NOT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::OR), std::string("OR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::XOR), std::string("XOR"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_EXTRACT),
            std::string("BV_EXTRACT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_REPEAT),
            std::string("BV_REPEAT"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ROLI), std::string("BV_ROLI"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_RORI), std::string("BV_RORI"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_SIGN_EXTEND),
            std::string("BV_SIGN_EXTEND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::BV_ZERO_EXTEND),
            std::string("BV_ZERO_EXTEND"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_FP_FROM_BV),
            std::string("FP_TO_FP_FROM_BV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_FP_FROM_FP),
            std::string("FP_TO_FP_FROM_FP"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_FP_FROM_SBV),
            std::string("FP_TO_FP_FROM_SBV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_FP_FROM_UBV),
            std::string("FP_TO_FP_FROM_UBV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_SBV),
            std::string("FP_TO_SBV"));
  ASSERT_EQ(std::to_string(bitwuzla::Kind::FP_TO_UBV),
            std::string("FP_TO_UBV"));
}

/* -------------------------------------------------------------------------- */
/* RoundingMode                                                               */
/* -------------------------------------------------------------------------- */

TEST_F(TestApi, rm_to_string)
{
  ASSERT_EQ(std::to_string(bitwuzla::RoundingMode::RNA), std::string("RNA"));
  ASSERT_EQ(std::to_string(bitwuzla::RoundingMode::RNE), std::string("RNE"));
  ASSERT_EQ(std::to_string(bitwuzla::RoundingMode::RTN), std::string("RTN"));
  ASSERT_EQ(std::to_string(bitwuzla::RoundingMode::RTP), std::string("RTP"));
  ASSERT_EQ(std::to_string(bitwuzla::RoundingMode::RTZ), std::string("RTZ"));
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

TEST_F(TestApi, result_to_string)
{
  ASSERT_EQ(std::to_string(bitwuzla::Result::SAT), std::string("sat"));
  ASSERT_EQ(std::to_string(bitwuzla::Result::UNSAT), std::string("unsat"));
  ASSERT_EQ(std::to_string(bitwuzla::Result::UNKNOWN), std::string("unknown"));
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

TEST_F(TestApi, set_option)
{
  //{
  //  bitwuzla::Options opts;
  //  opts.set(bitwuzla::Option::INCREMENTAL, true);
  //  ASSERT_THROW(
  //      opts.set(bitwuzla::Option::PP_UNCONSTRAINED_OPTIMIZATION, true),
  //      BitwuzlaException);
  //}
  //{
  //  bitwuzla::Options opts;
  //  opts.set(bitwuzla::Option::FUN_DUAL_PROP, true);
  //  ASSERT_THROW(opts.set(bitwuzla::Option::FUN_JUST, true),
  //               "enabling multiple optimization techniques is not allowed");
  //  ASSERT_THROW(opts.set(bitwuzla::Option::PP_NONDESTR_SUBST, true),
  //  BitwuzlaException);
  //}
  //{
  //  bitwuzla::Options opts;
  //  opts.set(bitwuzla::Option::FUN_JUST, true);
  //  ASSERT_THROW(opts.set(bitwuzla::Option::FUN_DUAL_PROP, true),
  //  BitwuzlaException);
  //}
  {
    bitwuzla::Options opts;
    opts.set(bitwuzla::Option::PRODUCE_MODELS, true);
    // ASSERT_THROW(
    //     opts.set(bitwuzla::Option::PP_UNCONSTRAINED_OPTIMIZATION, true),
    //     BitwuzlaException);
  }
  //{
  //  bitwuzla::Options opts;
  //  opts.set(bitwuzla::Option::PP_NONDESTR_SUBST, true);
  //  ASSERT_THROW(
  //      opts.set(bitwuzla::Option::FUN_DUAL_PROP, true),
  //    BitwuzlaException);
  //}
  //{
  //  bitwuzla::Options opts;
  //  opts.set(bitwuzla::Option::PP_UNCONSTRAINED_OPTIMIZATION, true);
  //  ASSERT_THROW(opts.set(bitwuzla::Option::INCREMENTAL, true),
  //  BitwuzlaException);
  //  ASSERT_THROW(opts.set(bitwuzla::Option::PRODUCE_MODELS, true),
  //  BitwuzlaException);
  //}
  {
    bitwuzla::Options opts;
    ASSERT_EQ(opts.get(bitwuzla::Option::PRODUCE_UNSAT_CORES), 0);
    opts.set(bitwuzla::Option::PRODUCE_UNSAT_CORES, true);
    ASSERT_EQ(opts.get(bitwuzla::Option::PRODUCE_UNSAT_CORES), 1);
    ASSERT_EQ(opts.get(bitwuzla::Option::VERBOSITY), 0);
    opts.set(bitwuzla::Option::VERBOSITY, 2);
    ASSERT_EQ(opts.get(bitwuzla::Option::VERBOSITY), 2);
    ASSERT_EQ(opts.get_mode(bitwuzla::Option::BV_SOLVER), "bitblast");
    opts.set(bitwuzla::Option::BV_SOLVER, "prop");
    ASSERT_EQ(opts.get_mode(bitwuzla::Option::BV_SOLVER), "prop");
    opts.set(bitwuzla::Option::BV_SOLVER, std::string("prop"));
    ASSERT_EQ(opts.get_mode(bitwuzla::Option::BV_SOLVER), "prop");
    opts.set(bitwuzla::Option::SAT_SOLVER, std::string("cadical"));
    ASSERT_EQ(opts.get_mode(bitwuzla::Option::SAT_SOLVER), "cadical");
    ASSERT_THROW(opts.set(bitwuzla::Option::BV_SOLVER, "asdf"),
                 bitwuzla::BitwuzlaException);
    ASSERT_THROW(opts.set(bitwuzla::Option::INCREMENTAL, "true"),
                 bitwuzla::BitwuzlaException);
  }
}

TEST_F(TestApi, option_info)
{
  for (int32_t i = 0; i < static_cast<int32_t>(bitwuzla::Option::NUM_OPTS); ++i)
  {
    bitwuzla::Option opt = static_cast<bitwuzla::Option>(i);
    try  // TODO: temporary, until set of options is finalized
    {
      bitwuzla::OptionInfo info(d_options, opt);
      if (info.kind == bitwuzla::OptionInfo::Kind::BOOL)
      {
        ASSERT_EQ(d_options.get(opt),
                  std::get<bitwuzla::OptionInfo::Bool>(info.values).cur);
      }
      else if (info.kind == bitwuzla::OptionInfo::Kind::NUMERIC)
      {
        ASSERT_EQ(d_options.get(opt),
                  std::get<bitwuzla::OptionInfo::Numeric>(info.values).cur);
      }
      else
      {
        ASSERT_EQ(d_options.get_mode(opt),
                  std::get<bitwuzla::OptionInfo::Mode>(info.values).cur);
      }
    }
    catch (std::out_of_range &e)
    {
    }
  }
}

}  // namespace bzla::test
