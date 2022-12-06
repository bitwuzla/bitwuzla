#include "api/checks.h"
#include "api/cpp/bitwuzla.h"
#include "test/unit/test.h"

namespace bzla::test {

class TestApi : public ::testing::Test
{
 protected:
  /* associated with other Bitwuzla instance */
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

  bitwuzla::Options d_options;

  // sorts
  bitwuzla::Sort d_bv_sort1  = bitwuzla::mk_bv_sort(1);
  bitwuzla::Sort d_bv_sort23 = bitwuzla::mk_bv_sort(23);
  bitwuzla::Sort d_bv_sort32 = bitwuzla::mk_bv_sort(32);
  bitwuzla::Sort d_bv_sort8  = bitwuzla::mk_bv_sort(8);
  bitwuzla::Sort d_fp_sort16 = bitwuzla::mk_fp_sort(5, 11);
  bitwuzla::Sort d_fp_sort32 = bitwuzla::mk_fp_sort(8, 24);
  bitwuzla::Sort d_arr_sort_bv =
      bitwuzla::mk_array_sort(d_bv_sort32, d_bv_sort8);
  bitwuzla::Sort d_arr_sort_bvfp =
      bitwuzla::mk_array_sort(d_bv_sort8, d_fp_sort16);
  bitwuzla::Sort d_arr_sort_fpbv =
      bitwuzla::mk_array_sort(d_fp_sort16, d_bv_sort8);
  std::vector<bitwuzla::Sort> d_fun_domain_sorts{
      d_bv_sort8, d_fp_sort16, d_bv_sort32};
  bitwuzla::Sort d_fun_sort =
      bitwuzla::mk_fun_sort(d_fun_domain_sorts, d_bv_sort8);
  bitwuzla::Sort d_fun_sort_fp =
      bitwuzla::mk_fun_sort(d_fun_domain_sorts, d_fp_sort16);
  bitwuzla::Sort d_rm_sort = bitwuzla::mk_rm_sort();
  // terms
  bitwuzla::Term d_true       = bitwuzla::mk_true();
  bitwuzla::Term d_bv_one1    = bitwuzla::mk_bv_one(d_bv_sort1);
  bitwuzla::Term d_bv_ones23  = bitwuzla::mk_bv_ones(d_bv_sort23);
  bitwuzla::Term d_bv_zero8   = bitwuzla::mk_bv_zero(d_bv_sort8);
  bitwuzla::Term d_bv_mins8   = bitwuzla::mk_bv_min_signed(d_bv_sort8);
  bitwuzla::Term d_bv_maxs8   = bitwuzla::mk_bv_max_signed(d_bv_sort8);
  bitwuzla::Term d_fp_pzero32 = bitwuzla::mk_fp_pos_zero(d_fp_sort32);
  bitwuzla::Term d_fp_nzero32 = bitwuzla::mk_fp_neg_zero(d_fp_sort32);
  bitwuzla::Term d_fp_pinf32  = bitwuzla::mk_fp_pos_inf(d_fp_sort32);
  bitwuzla::Term d_fp_ninf32  = bitwuzla::mk_fp_neg_inf(d_fp_sort32);
  bitwuzla::Term d_fp_nan32   = bitwuzla::mk_fp_nan(d_fp_sort32);

  bitwuzla::Term d_bool_const = bitwuzla::mk_const(bitwuzla::mk_bool_sort());
  bitwuzla::Term d_bv_const1  = bitwuzla::mk_const(d_bv_sort1);
  bitwuzla::Term d_bv_const8  = bitwuzla::mk_const(d_bv_sort8);
  bitwuzla::Term d_fp_const16 = bitwuzla::mk_const(d_fp_sort16);
  bitwuzla::Term d_rm_const   = bitwuzla::mk_const(d_rm_sort);

  bitwuzla::Term d_rm_rna = bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNA);
  bitwuzla::Term d_rm_rne = bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RNE);
  bitwuzla::Term d_rm_rtn = bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTN);
  bitwuzla::Term d_rm_rtp = bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTP);
  bitwuzla::Term d_rm_rtz = bitwuzla::mk_rm_value(bitwuzla::RoundingMode::RTZ);

  bitwuzla::Term d_fun        = bitwuzla::mk_const(d_fun_sort);
  bitwuzla::Term d_fun_fp     = bitwuzla::mk_const(d_fun_sort_fp);
  bitwuzla::Term d_array_fpbv = bitwuzla::mk_const(d_arr_sort_fpbv);
  bitwuzla::Term d_array      = bitwuzla::mk_const(d_arr_sort_bv);
  bitwuzla::Term d_store =
      bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE,
                        {d_array, bitwuzla::mk_const(d_bv_sort32), d_bv_zero8});

  bitwuzla::Term d_var1      = bitwuzla::mk_var(d_bv_sort8);
  bitwuzla::Term d_var2      = bitwuzla::mk_var(d_bv_sort8);
  bitwuzla::Term d_bound_var = bitwuzla::mk_var(d_bv_sort8);
  bitwuzla::Term d_bool_var  = bitwuzla::mk_var(bitwuzla::mk_bool_sort());

  bitwuzla::Term d_not_bv_const1 =
      bitwuzla::mk_term(bitwuzla::Kind::BV_NOT, {d_bv_const1});
  bitwuzla::Term d_and_bv_const1 = bitwuzla::mk_term(
      bitwuzla::Kind::EQUAL,
      {d_bv_one1,
       bitwuzla::mk_term(bitwuzla::Kind::BV_AND, {d_bv_one1, d_bv_const1})});
  bitwuzla::Term d_eq_bv_const8 =
      bitwuzla::mk_term(bitwuzla::Kind::EQUAL, {d_bv_const8, d_bv_zero8});

  bitwuzla::Term d_lambda = bitwuzla::mk_term(
      bitwuzla::Kind::LAMBDA,
      {d_bound_var,
       bitwuzla::mk_term(bitwuzla::Kind::BV_ADD, {d_bound_var, d_bv_const8})});
  bitwuzla::Term d_bool_lambda_body =
      bitwuzla::mk_term(bitwuzla::Kind::EQUAL, {d_bool_var, d_true});
  bitwuzla::Term d_bool_lambda = bitwuzla::mk_term(
      bitwuzla::Kind::LAMBDA, {d_bool_var, d_bool_lambda_body});
  bitwuzla::Term d_bool_apply =
      bitwuzla::mk_term(bitwuzla::Kind::APPLY, {d_bool_lambda, d_true});

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

TEST_F(TestApi, mk_array_sort)
{
  ASSERT_THROW(bitwuzla::mk_array_sort(bitwuzla::Sort(), d_bv_sort8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_array_sort(d_bv_sort1, bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);

  ASSERT_NO_THROW(bitwuzla::mk_array_sort(d_arr_sort_bv, d_bv_sort8));
  ASSERT_NO_THROW(bitwuzla::mk_array_sort(d_bv_sort8, d_arr_sort_bv));
  ASSERT_NO_THROW(bitwuzla::mk_array_sort(d_fun_sort, d_bv_sort8));
  ASSERT_NO_THROW(bitwuzla::mk_array_sort(d_bv_sort8, d_fun_sort));
}

TEST_F(TestApi, mk_bv_sort)
{
  ASSERT_THROW(bitwuzla::mk_bv_sort(0), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_sort)
{
  ASSERT_THROW(bitwuzla::mk_fp_sort(0, 8), bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_sort(5, 0), bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_sort(1, 2), bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_sort(2, 1), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fun_sort)
{
  ASSERT_THROW(bitwuzla::mk_fun_sort({}, d_bv_sort8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fun_sort(d_fun_domain_sorts, bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_zero)
{
  ASSERT_THROW(bitwuzla::mk_bv_zero(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_zero(d_fp_sort16), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_one)
{
  ASSERT_THROW(bitwuzla::mk_bv_one(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_one(d_fp_sort16), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_ones)
{
  ASSERT_THROW(bitwuzla::mk_bv_ones(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_ones(d_fp_sort16), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_min_signed)
{
  ASSERT_THROW(bitwuzla::mk_bv_min_signed(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_min_signed(d_fp_sort16),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_max_signed)
{
  ASSERT_THROW(bitwuzla::mk_bv_max_signed(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_max_signed(d_fp_sort16),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_pos_zero)
{
  ASSERT_THROW(bitwuzla::mk_fp_pos_zero(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_pos_zero(d_bv_sort8),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_neg_zero)
{
  ASSERT_THROW(bitwuzla::mk_fp_neg_zero(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_neg_zero(d_bv_sort8),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_pos_inf)
{
  ASSERT_THROW(bitwuzla::mk_fp_pos_inf(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_pos_inf(d_bv_sort8),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_neg_inf)
{
  ASSERT_THROW(bitwuzla::mk_fp_neg_inf(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_neg_inf(d_bv_sort8),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_nan)
{
  ASSERT_THROW(bitwuzla::mk_fp_nan(bitwuzla::Sort()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_nan(d_bv_sort8), bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_bv_value)
{
  ASSERT_NO_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "127", 10));
  ASSERT_NO_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "-128", 10));
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "256", 10),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "-129", 10),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla::mk_bv_value(bitwuzla::Sort(), "010", 2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "", 2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "", 2),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla::mk_bv_value(d_fp_sort16, "010", 2),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "11111111010", 2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "1234567890", 10),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "1234567890aAbBcCdDeEfF", 16),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "1234567890", 2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "12z4567890", 10),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value(d_bv_sort8, "12z4567890", 16),
               bitwuzla::BitwuzlaException);

  // TODO enable
  // d_options.set(bitwuzla::Option::PRODUCE_MODELS, true);
  // bitwuzla::Bitwuzla bitwuzla(d_options);
  // bitwuzla.check_sat();
  // ASSERT_EQ(std::string(bitwuzla.get_bv_value(
  //              bitwuzla::mk_bv_value(
  //                   d_bv_sort8, "-1", 10))),
  //          "11111111");
  // ASSERT_EQ(std::string(bitwuzla.get_bv_value(
  //              bitwuzla::mk_bv_value(
  //                   d_bv_sort8, "-123", 10))),
  //          "10000101");
  // ASSERT_EQ(std::string(bitwuzla.get_bv_value(
  //              bitwuzla::mk_bv_value(
  //                   d_bv_sort8, "-128", 10))),
  //          "10000000");
}

TEST_F(TestApi, mk_bv_value_uint64)
{
  ASSERT_THROW(bitwuzla::mk_bv_value_uint64(bitwuzla::Sort(), 23),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_bv_value_uint64(d_fp_sort16, 23),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_fp_value)
{
  ASSERT_THROW(bitwuzla::mk_fp_value(bitwuzla::Term(), d_bv_zero8, d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, bitwuzla::Term(), d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, d_bv_zero8, bitwuzla::Term()),
               bitwuzla::BitwuzlaException);

  // TODO enable, currently fails in symfpu
  // ASSERT_THROW(
  //    bitwuzla::mk_fp_value( d_bv_zero8, d_bv_zero8, d_bv_zero8),
  //    bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_fp_const16, d_bv_zero8, d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, d_fp_const16, d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, d_bv_zero8, d_fp_const16),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_const1, d_bv_zero8, d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, d_bv_const8, d_bv_zero8),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_fp_value(d_bv_one1, d_bv_zero8, d_bv_const8),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_term_check_null)
{
  bitwuzla::Term null;
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOT, {null}),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_AND, {d_bv_zero8, null}),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ADD,
                                 {d_rm_const, null, d_fp_const16}),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_term_check_cnt)
{
  std::vector<bitwuzla::Term> apply_args1 = {d_bv_one1};
  std::vector<bitwuzla::Term> apply_args2 = {d_fun, d_bv_const8};
  std::vector<bitwuzla::Term> array_args1 = {d_array_fpbv};
  std::vector<bitwuzla::Term> bool_args1  = {d_true};
  std::vector<bitwuzla::Term> bool_args2  = {d_true, d_true};
  std::vector<bitwuzla::Term> bv_args1    = {d_bv_one1};
  std::vector<bitwuzla::Term> bv_args1_rm = {d_rm_const};
  std::vector<bitwuzla::Term> bv_args2    = {d_bv_zero8, d_bv_const8};
  std::vector<bitwuzla::Term> ite_args2   = {d_true, d_bv_const8};
  std::vector<bitwuzla::Term> fp_args1    = {d_fp_const16};
  std::vector<bitwuzla::Term> fp_args1_rm = {d_rm_const};
  std::vector<bitwuzla::Term> fp_args2    = {d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args2_rm = {d_rm_const, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args3_rm = {
      d_rm_const, d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> fun_args1 = {d_var1};

  std::vector<uint64_t> idxs1    = {1};
  std::vector<uint64_t> idxs2    = {2, 0};
  std::vector<uint64_t> fp_idxs1 = {5, 8};

  // bool
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::AND, bool_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IFF, bool_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IMPLIES, bool_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::NOT, bool_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::OR, bool_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::XOR, bool_args1),
               bitwuzla::BitwuzlaException);

  // bit-vectors
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::APPLY, apply_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::APPLY, apply_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT, array_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE, array_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ADD, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_AND, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ASHR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_CONCAT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_DEC, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_INC, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_MUL, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NAND, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NEG, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOT, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDAND, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDOR, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDXOR, bv_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROL, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SADD_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGE, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHL, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLE, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SMOD, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SMUL_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SREM, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SSUB_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SUB, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UADD_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UDIV, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGE, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULE, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UMUL_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UREM, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_USUB_OVERFLOW, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XNOR, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XOR, bv_args1),
               bitwuzla::BitwuzlaException);

  // floating-point
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ABS, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ADD, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_DIV, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_EQUAL, fp_args1_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FMA, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FP, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GEQ, fp_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GT, fp_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_INF, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NAN, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NEG, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NORMAL, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_POS, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_SUBNORMAL, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_ZERO, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LEQ, fp_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LT, fp_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MAX, fp_args3_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MIN, fp_args3_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_ZERO, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MUL, fp_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_REM, fp_args3_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_RTI, fp_args3_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SQRT, fp_args3_rm),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SUB, fp_args2),
               bitwuzla::BitwuzlaException);

  // others
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::DISTINCT, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EQUAL, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EXISTS, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FORALL, bv_args1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ITE, ite_args2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, fun_args1),
               bitwuzla::BitwuzlaException);

  // indexed
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_EXTRACT, bv_args2, idxs2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REPEAT, bv_args2, idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROLI, bv_args2, idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_RORI, bv_args2, idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SIGN_EXTEND, bv_args2, idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_ZERO_EXTEND, bv_args2, idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::FP_TO_FP_FROM_BV, bv_args2, fp_idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_FP_FROM_FP, fp_args3_rm, fp_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_FP_FROM_SBV, bv_args1_rm, fp_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_FP_FROM_UBV, bv_args1_rm, fp_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_TO_SBV, fp_args1, idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_TO_UBV, fp_args1, idxs1),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_term_check_args)
{
  std::vector<bitwuzla::Term> array_select_args2_invalid_1 = {d_fp_const16,
                                                              d_array_fpbv};
  std::vector<bitwuzla::Term> array_select_args2_invalid_2 = {d_array_fpbv,
                                                              d_bv_const8};

  std::vector<bitwuzla::Term> array_store_args3_invalid_1 = {
      d_fp_const16, d_array_fpbv, d_bv_const8};
  std::vector<bitwuzla::Term> array_store_args3_invalid_2 = {
      d_array_fpbv, d_bv_const8, d_bv_const8};
  std::vector<bitwuzla::Term> array_store_args3_invalid_3 = {
      d_array_fpbv, d_fp_const16, d_fp_const16};

  std::vector<bitwuzla::Term> apply_args3_invalid_1 = {
      d_fun, d_bv_const8, d_fun};
  std::vector<bitwuzla::Term> apply_args3_invalid_2 = {
      d_fun, d_bv_const8, d_bv_const8, d_fp_pzero32};

  std::vector<bitwuzla::Term> bool_args1_invalid = {d_bv_const8};
  std::vector<bitwuzla::Term> bool_args2_invalid = {d_fp_pzero32, d_fp_pzero32};
  std::vector<bitwuzla::Term> bool_args2_mis     = {d_true, d_bv_const8};

  std::vector<bitwuzla::Term> bv_args1         = {d_bv_const8};
  std::vector<bitwuzla::Term> bv_args1_invalid = {d_fp_const16};
  std::vector<bitwuzla::Term> bv_args2_invalid = {d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> bv_args2_mis     = {d_bv_one1, d_bv_const8};
  std::vector<bitwuzla::Term> bv_args2_rm      = {d_rm_const, d_bv_const8};
  std::vector<bitwuzla::Term> bv_args2_rm_invalid_1 = {d_bv_const8,
                                                       d_bv_const8};
  std::vector<bitwuzla::Term> bv_args2_rm_invalid_2 = {d_rm_const,
                                                       d_fp_const16};

  std::vector<bitwuzla::Term> ite_THROW_args3_1 = {
      d_true, d_bv_const8, d_bv_one1};
  std::vector<bitwuzla::Term> ite_args3_invalid_2 = {
      d_bv_const8, d_bv_const8, d_bv_const8};

  std::vector<bitwuzla::Term> lambda_args2_invalid_1 = {d_bv_const8,
                                                        d_bv_const8};
  std::vector<bitwuzla::Term> lambda_args2_invalid_2 = {d_bound_var,
                                                        d_bv_const8};
  std::vector<bitwuzla::Term> lambda_args3_invalid_1 = {
      d_var1, d_var1, d_bv_const8};

  std::vector<bitwuzla::Term> lambda_args3_invalid_2 = {
      d_var1,
      d_var2,
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_UBV,
          {d_rm_const,
           bitwuzla::mk_term(bitwuzla::Kind::BV_ADD, {d_var2, d_bv_const8})},
          {5, 8})};

  std::vector<bitwuzla::Term> fp_args2_rm = {d_rm_const, d_fp_const16};

  std::vector<bitwuzla::Term> fp_args1_invalid = {d_bv_one1};
  std::vector<bitwuzla::Term> fp_args2_invalid = {d_bv_zero8, d_bv_const8};
  std::vector<bitwuzla::Term> fp_args2_mis     = {d_fp_pzero32, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args2_rm_invalid_1 = {d_bv_const8,
                                                       d_fp_const16};
  std::vector<bitwuzla::Term> fp_args2_rm_invalid_2 = {d_rm_const, d_bv_const8};
  std::vector<bitwuzla::Term> fp_args3_rm_mis       = {
            d_rm_const, d_fp_pzero32, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args3_rm_invalid_1 = {
      d_fp_const16, d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args3_rm_invalid_2 = {
      d_rm_const, d_bv_zero8, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args4_mis = {
      d_rm_const, d_fp_pzero32, d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args4_rm_invalid_1 = {
      d_rm_const, d_bv_zero8, d_fp_const16, d_fp_const16};
  std::vector<bitwuzla::Term> fp_args4_rm_invalid_2 = {
      d_fp_const16, d_fp_const16, d_fp_const16, d_fp_const16};

  std::vector<bitwuzla::Term> fp_fp_args3_invalid_1 = {
      d_bv_const8, d_bv_zero8, d_bv_ones23};
  std::vector<bitwuzla::Term> fp_fp_args3_invalid_2 = {
      d_bv_one1, d_fp_pzero32, d_bv_ones23};
  std::vector<bitwuzla::Term> fp_fp_args3_invalid_3 = {
      d_bv_one1, d_bv_zero8, d_fp_pzero32};
  std::vector<bitwuzla::Term> fp_fp_args3_invalid_4 = {
      d_fp_pzero32, d_bv_zero8, d_bv_ones23};

  std::vector<bitwuzla::Term> quant_args2_invalid_1 = {d_true, d_true};
  std::vector<bitwuzla::Term> quant_args2_invalid_2 = {d_var1, d_bv_const8};
  std::vector<bitwuzla::Term> quant_args2_invalid_3 = {d_bound_var,
                                                       d_bv_const8};
  std::vector<bitwuzla::Term> quant_args3_invalid   = {
        d_var1, d_var1, d_bv_const8};

  std::vector<uint64_t> bv_idxs1                   = {3};
  std::vector<uint64_t> bv_idxs2                   = {2, 0};
  std::vector<uint64_t> bv_extract_idxs2_invalid_1 = {0, 2};
  std::vector<uint64_t> bv_extract_idxs2_invalid_2 = {9, 0};
  std::vector<uint64_t> bv_repeat_idxs_invalid_1   = {2305843009213693953};
  std::vector<uint64_t> bv_extend_idxs_invalid_1   = {UINT64_MAX};
  std::vector<uint64_t> fp_idxs2                   = {5, 8};
  std::vector<uint64_t> fp_idxs2_invalid_1         = {1, 8};
  std::vector<uint64_t> fp_idxs2_invalid_2         = {5, 1};

  // bool
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::AND, bool_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::AND, bool_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IFF, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IFF, bool_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IMPLIES, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::IMPLIES, bool_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::NOT, bool_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::OR, bool_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::XOR, bool_args2_invalid),
               bitwuzla::BitwuzlaException);
  // bit-vectors
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ADD, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ADD, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_AND, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_AND, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ASHR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ASHR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_DEC, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_INC, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_MUL, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_MUL, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NAND, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NAND, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NEG, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_NOT, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDAND, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDOR, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_REDXOR, bv_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_OR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROL, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROL, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ROR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SADD_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SADD_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SDIV, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGE, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGE, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGT, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SGT, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHL, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHL, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SHR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLE, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLE, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLT, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SLT, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SMOD, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SMOD, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SMUL_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SMUL_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SREM, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SREM, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SSUB_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_SSUB_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SUB, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_SUB, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_UADD_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_UADD_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UDIV, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UDIV, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGE, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGE, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGT, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UGT, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULE, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULE, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULT, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_ULT, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_UMUL_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_UMUL_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UREM, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_UREM, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_USUB_OVERFLOW, bv_args2_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_USUB_OVERFLOW, bv_args2_mis),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XNOR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XNOR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XOR, bv_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::BV_XOR, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  // floating-point
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ABS, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ADD, fp_args3_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ADD, fp_args3_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_ADD, fp_args3_rm_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_DIV, fp_args3_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_DIV, fp_args3_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_DIV, fp_args3_rm_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_EQUAL, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_EQUAL, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FMA, fp_args4_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FMA, fp_args4_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FMA, fp_args4_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FP, fp_fp_args3_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FP, fp_fp_args3_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FP, fp_fp_args3_invalid_3),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_FP, fp_fp_args3_invalid_4),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GEQ, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GEQ, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GT, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_GT, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_INF, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NAN, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NEG, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::FP_IS_NORMAL, fp_args1_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_POS, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::FP_IS_SUBNORMAL, fp_args1_invalid),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_ZERO, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LEQ, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LEQ, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LT, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_LT, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MAX, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MAX, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MIN, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MIN, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_IS_ZERO, fp_args1_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MUL, fp_args3_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MUL, fp_args3_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_MUL, fp_args3_rm_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_REM, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_REM, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_RTI, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_RTI, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_RTI, fp_args2_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_RTI, fp_args2_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SQRT, fp_args2_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SQRT, fp_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::FP_SQRT, fp_args2_rm_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::FP_SQRT, fp_args2_rm_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SUB, fp_args3_rm_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SUB, fp_args3_rm_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FP_SUB, fp_args3_rm_mis),
               bitwuzla::BitwuzlaException);
  // others
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::APPLY, apply_args3_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::APPLY, apply_args3_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT,
                                 array_select_args2_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_SELECT,
                                 array_select_args2_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE,
                                 array_store_args3_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE,
                                 array_store_args3_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ARRAY_STORE,
                                 array_store_args3_invalid_3),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::DISTINCT, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EQUAL, bv_args2_mis),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EXISTS, quant_args2_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EXISTS, quant_args2_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EXISTS, quant_args2_invalid_3),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::EXISTS, quant_args3_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FORALL, quant_args2_invalid_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FORALL, quant_args2_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FORALL, quant_args2_invalid_3),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::FORALL, quant_args3_invalid),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ITE, ite_args3_invalid_2),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(bitwuzla::Kind::ITE, ite_THROW_args3_1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, lambda_args2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, lambda_args3_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, lambda_args3_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_NO_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::LAMBDA, lambda_args2_invalid_2));
  // indexed
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_EXTRACT, bv_args1_invalid, bv_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::BV_EXTRACT, bv_args1, bv_extract_idxs2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::BV_EXTRACT, bv_args1, bv_extract_idxs2_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_REPEAT, bv_args1_invalid, bv_idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::BV_REPEAT, bv_args1, bv_repeat_idxs_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_ROLI, bv_args1_invalid, bv_idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(bitwuzla::Kind::BV_RORI, bv_args1_invalid, bv_idxs1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::BV_SIGN_EXTEND, bv_args1_invalid, bv_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::BV_SIGN_EXTEND, bv_args1, bv_extend_idxs_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::BV_ZERO_EXTEND, bv_args1_invalid, bv_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::BV_ZERO_EXTEND, bv_args1, bv_extend_idxs_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_BV, bv_args1_invalid, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_BV, bv_args1, fp_idxs2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_BV, bv_args1, fp_idxs2_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_FP, fp_args2_rm_invalid_1, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_FP, fp_args2_rm_invalid_2, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_FP, fp_args2_rm, fp_idxs2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_FP, fp_args2_rm, fp_idxs2_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_SBV, bv_args2_rm_invalid_1, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_SBV, bv_args2_rm_invalid_2, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_SBV, bv_args2_rm, fp_idxs2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_SBV, bv_args2_rm, fp_idxs2_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_UBV, bv_args2_rm_invalid_1, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_UBV, bv_args2_rm_invalid_2, fp_idxs2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_UBV, bv_args2_rm, fp_idxs2_invalid_1),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(
      bitwuzla::mk_term(
          bitwuzla::Kind::FP_TO_FP_FROM_UBV, bv_args2_rm, fp_idxs2_invalid_2),
      bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_SBV, fp_args2_rm_invalid_1, bv_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_SBV, fp_args2_rm_invalid_2, bv_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_UBV, fp_args2_rm_invalid_1, bv_idxs1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_term(
                   bitwuzla::Kind::FP_TO_UBV, fp_args2_rm_invalid_2, bv_idxs1),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_const)
{
  ASSERT_NO_THROW(bitwuzla::mk_const(d_bv_sort8));
  ASSERT_NO_THROW(bitwuzla::mk_const(d_bv_sort8, ""));
  ASSERT_THROW(bitwuzla::mk_const(bitwuzla::Sort(), "asdf"),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, mk_const_array)
{
  GTEST_SKIP();  // TODO enable when implemented
  ASSERT_THROW(bitwuzla::mk_const_array(bitwuzla::Sort(), d_bv_one1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_const_array(d_arr_sort_bv, bitwuzla::Term()),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla::mk_const_array(d_bv_sort8, d_bv_one1),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_const_array(d_arr_sort_bv, d_array),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla::mk_const_array(d_arr_sort_bvfp, d_fp_pzero32),
               bitwuzla::BitwuzlaException);

  ASSERT_NO_THROW(bitwuzla::mk_const_array(d_arr_sort_bvfp, d_fp_const16));
}

TEST_F(TestApi, mk_var)
{
  ASSERT_NO_THROW(bitwuzla::mk_var(d_bv_sort8));
  ASSERT_NO_THROW(bitwuzla::mk_var(d_bv_sort8, ""));
  ASSERT_THROW(bitwuzla::mk_var(bitwuzla::Sort(), "asdf"),
               bitwuzla::BitwuzlaException);
}

TEST_F(TestApi, push)
{
  {
    d_options.set(bitwuzla::Option::INCREMENTAL, false);
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.push(2), bitwuzla::BitwuzlaException);
  }
  {
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_NO_THROW(bitwuzla.push(0));
    ASSERT_NO_THROW(bitwuzla.push(2));
  }
}

TEST_F(TestApi, pop)
{
  {
    d_options.set(bitwuzla::Option::INCREMENTAL, false);
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.pop(0), bitwuzla::BitwuzlaException);
  }
  {
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.pop(2), bitwuzla::BitwuzlaException);
    ASSERT_NO_THROW(bitwuzla.pop(0));
    bitwuzla.push(2);
    ASSERT_NO_THROW(bitwuzla.pop(2));
  }
}

TEST_F(TestApi, assert)
{
  bitwuzla::Bitwuzla bitwuzla(d_options);
  ASSERT_THROW(bitwuzla.assert_formula(bitwuzla::Term()),
               bitwuzla::BitwuzlaException);
  ASSERT_THROW(bitwuzla.assert_formula(d_bv_const8),
               bitwuzla::BitwuzlaException);

  ASSERT_THROW(bitwuzla.assert_formula(d_bv_one1), bitwuzla::BitwuzlaException);
  // TODO: this should throw, not implemented yet
  // ASSERT_THROW(bitwuzla.assert_formula(d_bool_var),
  // bitwuzla::BitwuzlaException);
  // ASSERT_THROW(bitwuzla.assert_formula(d_bool_lambda),
  // bitwuzla::BitwuzlaException);
  // ASSERT_THROW(bitwuzla.assert_formula(d_bool_lambda_body),
  // bitwuzla::BitwuzlaException);

  ASSERT_NO_THROW(bitwuzla.assert_formula(d_bool_apply));
  ASSERT_NO_THROW(bitwuzla.assert_formula(d_bool_const));
}

TEST_F(TestApi, is_unsat_assumption)
{
  {
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bv_const1),
                 bitwuzla::BitwuzlaException);
  }
  {
    GTEST_SKIP();  // TODO enable when implemented
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);

    ASSERT_THROW(bitwuzla.is_unsat_assumption(bitwuzla::Term()),
                 bitwuzla::BitwuzlaException);

    bitwuzla.assert_formula(d_true);
    bitwuzla.check_sat({d_bv_const1});
    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bv_const1),
                 bitwuzla::BitwuzlaException);

    bitwuzla.check_sat(
        {d_bv_const1,
         bitwuzla::mk_term(bitwuzla::Kind::BV_NOT, {d_bv_const1})});

    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bv_const8),
                 bitwuzla::BitwuzlaException);
    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_true),
                 bitwuzla::BitwuzlaException);

    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bool_var),
                 bitwuzla::BitwuzlaException);
    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bool_lambda),
                 bitwuzla::BitwuzlaException);
    ASSERT_THROW(bitwuzla.is_unsat_assumption(d_bool_lambda_body),
                 bitwuzla::BitwuzlaException);

    ASSERT_NO_THROW(bitwuzla.is_unsat_assumption(d_bv_const1));
  }
}

TEST_F(TestApi, get_unsat_assumptions)
{
  {
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.get_unsat_assumptions(), bitwuzla::BitwuzlaException);
  }
  {
    GTEST_SKIP();  // TODO enable when implemented
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);

    bitwuzla.assert_formula(d_true);
    bitwuzla.check_sat({d_bv_const1});
    ASSERT_THROW(bitwuzla.get_unsat_assumptions(), bitwuzla::BitwuzlaException);

    bitwuzla.check_sat(
        {d_bv_const1, d_not_bv_const1, d_and_bv_const1, d_eq_bv_const8});
    ASSERT_TRUE(bitwuzla.is_unsat_assumption(d_bv_const1));
    ASSERT_TRUE(bitwuzla.is_unsat_assumption(d_not_bv_const1));
    ASSERT_TRUE(bitwuzla.is_unsat_assumption(d_and_bv_const1));
    ASSERT_FALSE(bitwuzla.is_unsat_assumption(d_eq_bv_const8));
    auto unsat_ass = bitwuzla.get_unsat_assumptions();
    ASSERT_EQ(unsat_ass.size(), 3);
    for (const auto& a : unsat_ass)
    {
      ASSERT_TRUE(bitwuzla.is_unsat_assumption(a));
      bitwuzla.assert_formula(a);
    }
    ASSERT_EQ(bitwuzla.check_sat(), bitwuzla::Result::UNSAT);
  }
}

TEST_F(TestApi, get_unsat_core)
{
  {
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.get_unsat_core(), bitwuzla::BitwuzlaException);
  }
  {
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);
    ASSERT_THROW(bitwuzla.get_unsat_core(), bitwuzla::BitwuzlaException);
  }
  {
    GTEST_SKIP();  // TODO enable when implemented
    d_options.set(bitwuzla::Option::INCREMENTAL, true);
    d_options.set(bitwuzla::Option::PRODUCE_UNSAT_CORES, true);
    bitwuzla::Bitwuzla bitwuzla(d_options);

    bitwuzla.assert_formula(d_true);
    bitwuzla.check_sat({d_bv_const1});
    ASSERT_THROW(bitwuzla.get_unsat_core(), bitwuzla::BitwuzlaException);

    bitwuzla.check_sat(
        {d_bv_const1, d_not_bv_const1, d_and_bv_const1, d_eq_bv_const8});

    ASSERT_TRUE(bitwuzla.is_unsat_assumption(d_bv_const1));
    ASSERT_TRUE(bitwuzla.is_unsat_assumption(d_and_bv_const1));
    auto unsat_core = bitwuzla.get_unsat_core();
    ASSERT_EQ(unsat_core.size(), 1);
    ASSERT_EQ(unsat_core[0], d_not_bv_const1);

    auto unsat_ass = bitwuzla.get_unsat_assumptions();
    ASSERT_EQ(unsat_ass.size(), 2);
    ASSERT_EQ(unsat_ass[0], d_bv_const1);
    ASSERT_EQ(unsat_ass[1], d_and_bv_const1);
    ASSERT_EQ(bitwuzla.check_sat(), bitwuzla::Result::SAT);
    bitwuzla.assert_formula(unsat_ass[0]);
    ASSERT_EQ(bitwuzla.check_sat(), bitwuzla::Result::UNSAT);
  }
}

TEST_F(TestApi, simplify)
{
  GTEST_SKIP();  // TODO enable when implemented
  bitwuzla::Bitwuzla bitwuzla(d_options);
  bitwuzla.assert_formula(d_bool_const);
  bitwuzla.assert_formula(d_and_bv_const1);
  ASSERT_EQ(bitwuzla.simplify(), bitwuzla::Result::SAT);
}

TEST_F(TestApi, check_sat)
{
  // TODO add checks in Bitwuzla::check_sat
  //{
  //  bitwuzla::Bitwuzla bitwuzla(d_options);
  //  ASSERT_NO_THROW(bitwuzla.check_sat());
  //  ASSERT_THROW(bitwuzla.check_sat(), bitwuzla::BitwuzlaException);
  //}
  //{
  //  d_options.set(bitwuzla::Option::INCREMENTAL, true);
  //  bitwuzla::Bitwuzla bitwuzla(d_options);
  //  ASSERT_NO_THROW(bitwuzla.check_sat());
  //  ASSERT_NO_THROW(bitwuzla.check_sat());
  //}
}
}  // namespace bzla::test
