/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

extern "C" {
#include "bitwuzla.h"

#include "bzlabv.h"
#include "bzlaconfig.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaparse.h"
#include "bzlaprintmodel.h"
#include "bzlasubst.h"
#include "dumper/bzladumpaig.h"
#include "dumper/bzladumpbtor.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlaabort.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"
}

#include <unordered_map>

#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solving_context.h"

using namespace bzla;

struct BitwuzlaSort;
struct BitwuzlaTerm;

/* -------------------------------------------------------------------------- */

struct Bitwuzla
{
  Bitwuzla() : d_ctx(d_options) { d_bzla_dummy = bzla_new(); }

  ~Bitwuzla() { bzla_delete(d_bzla_dummy); }

  void reset()
  {
    // TODO: reset solving context and options?
  }

  /* Children stack for bitwuzla_term_get_children. */
  std::vector<const BitwuzlaTerm *> d_term_children;
  /* Indices populated by bitwuzla_term_get_indices. */
  std::vector<uint32_t> d_term_indices;
  /* Domain sorts populated by bitwuzla_term_fun_get_domain_sorts and
   * bitwuzla_sort_fun_get_domain_sorts query. */
  std::vector<const BitwuzlaSort *> d_sorts;

  /* String populated by bitwuzla_get_bv_value. */
  std::string d_bv_value;

  /** Strings populated by bitwuzla_get_fp_value. */
  std::string d_fp_value_sign;
  std::string d_fp_value_exponent;
  std::string d_fp_value_significand;

  /* Map internal sort id to external sort wrapper. */
  std::unordered_map<Type, std::unique_ptr<BitwuzlaSort>> d_sort_map;
  std::unordered_map<Node, std::unique_ptr<BitwuzlaTerm>> d_node_map;

  option::Options d_options;
  SolvingContext d_ctx;

  /** Used for BzlaMsg etc. for now. */
  Bzla *d_bzla_dummy;
};

struct BitwuzlaSort
{
  BitwuzlaSort(Bitwuzla *bitwuzla, const Type &type)
      : d_bzla(bitwuzla), d_type(type)
  {
  }

  Bitwuzla *d_bzla;
  Type d_type;
};

struct BitwuzlaTerm
{
  BitwuzlaTerm(Bitwuzla *bitwuzla, const Node &node)
      : d_bzla(bitwuzla), d_node(node)
  {
  }

  Bitwuzla *d_bzla;
  Node d_node;
};

static const char *bzla_kind_to_str[BITWUZLA_NUM_KINDS] = {
    "BITWUZLA_KIND_CONST",
    "BITWUZLA_KIND_CONST_ARRAY",
    "BITWUZLA_KIND_VAL",
    "BITWUZLA_KIND_VAR",
    "BITWUZLA_KIND_AND",
    "BITWUZLA_KIND_APPLY",
    "BITWUZLA_KIND_ARRAY_SELECT",
    "BITWUZLA_KIND_ARRAY_STORE",
    "BITWUZLA_KIND_BV_ADD",
    "BITWUZLA_KIND_BV_AND",
    "BITWUZLA_KIND_BV_ASHR",
    "BITWUZLA_KIND_BV_COMP",
    "BITWUZLA_KIND_BV_CONCAT",
    "BITWUZLA_KIND_BV_DEC",
    "BITWUZLA_KIND_BV_INC",
    "BITWUZLA_KIND_BV_MUL",
    "BITWUZLA_KIND_BV_NAND",
    "BITWUZLA_KIND_BV_NEG",
    "BITWUZLA_KIND_BV_NOR",
    "BITWUZLA_KIND_BV_NOT",
    "BITWUZLA_KIND_BV_OR",
    "BITWUZLA_KIND_BV_REDAND",
    "BITWUZLA_KIND_BV_REDOR",
    "BITWUZLA_KIND_BV_REDXOR",
    "BITWUZLA_KIND_BV_ROL",
    "BITWUZLA_KIND_BV_ROR",
    "BITWUZLA_KIND_BV_SADD_OVERFLOW",
    "BITWUZLA_KIND_BV_SDIV_OVERFLOW",
    "BITWUZLA_KIND_BV_SDIV",
    "BITWUZLA_KIND_BV_SGE",
    "BITWUZLA_KIND_BV_SGT",
    "BITWUZLA_KIND_BV_SHL",
    "BITWUZLA_KIND_BV_SHR",
    "BITWUZLA_KIND_BV_SLE",
    "BITWUZLA_KIND_BV_SLT",
    "BITWUZLA_KIND_BV_SMOD",
    "BITWUZLA_KIND_BV_SMUL_OVERFLOW",
    "BITWUZLA_KIND_BV_SREM",
    "BITWUZLA_KIND_BV_SSUB_OVERFLOW",
    "BITWUZLA_KIND_BV_SUB",
    "BITWUZLA_KIND_BV_UADD_OVERFLOW",
    "BITWUZLA_KIND_BV_UDIV",
    "BITWUZLA_KIND_BV_UGE",
    "BITWUZLA_KIND_BV_UGT",
    "BITWUZLA_KIND_BV_ULE",
    "BITWUZLA_KIND_BV_ULT",
    "BITWUZLA_KIND_BV_UMUL_OVERFLOW",
    "BITWUZLA_KIND_BV_UREM",
    "BITWUZLA_KIND_BV_USUB_OVERFLOW",
    "BITWUZLA_KIND_BV_XNOR",
    "BITWUZLA_KIND_BV_XOR",
    "BITWUZLA_KIND_DISTINCT",
    "BITWUZLA_KIND_EQUAL",
    "BITWUZLA_KIND_EXISTS",
    "BITWUZLA_KIND_FORALL",
    "BITWUZLA_KIND_FP_ABS",
    "BITWUZLA_KIND_FP_ADD",
    "BITWUZLA_KIND_FP_DIV",
    "BITWUZLA_KIND_FP_EQ",
    "BITWUZLA_KIND_FP_FMA",
    "BITWUZLA_KIND_FP_FP",
    "BITWUZLA_KIND_FP_GEQ",
    "BITWUZLA_KIND_FP_GT",
    "BITWUZLA_KIND_FP_IS_INF",
    "BITWUZLA_KIND_FP_IS_NAN",
    "BITWUZLA_KIND_FP_IS_NEG",
    "BITWUZLA_KIND_FP_IS_NORMAL",
    "BITWUZLA_KIND_FP_IS_POS",
    "BITWUZLA_KIND_FP_IS_SUBNORMAL",
    "BITWUZLA_KIND_FP_IS_ZERO",
    "BITWUZLA_KIND_FP_LEQ",
    "BITWUZLA_KIND_FP_LT",
    "BITWUZLA_KIND_FP_MAX",
    "BITWUZLA_KIND_FP_MIN",
    "BITWUZLA_KIND_FP_MUL",
    "BITWUZLA_KIND_FP_NEG",
    "BITWUZLA_KIND_FP_REM",
    "BITWUZLA_KIND_FP_RTI",
    "BITWUZLA_KIND_FP_SQRT",
    "BITWUZLA_KIND_FP_SUB",
    "BITWUZLA_KIND_IFF",
    "BITWUZLA_KIND_IMPLIES",
    "BITWUZLA_KIND_ITE",
    "BITWUZLA_KIND_LAMBDA",
    "BITWUZLA_KIND_NOT",
    "BITWUZLA_KIND_OR",
    "BITWUZLA_KIND_XOR",
    "BITWUZLA_KIND_BV_EXTRACT",
    "BITWUZLA_KIND_BV_REPEAT",
    "BITWUZLA_KIND_BV_ROLI",
    "BITWUZLA_KIND_BV_RORI",
    "BITWUZLA_KIND_BV_SIGN_EXTEND",
    "BITWUZLA_KIND_BV_ZERO_EXTEND",
    "BITWUZLA_KIND_FP_TO_FP_FROM_BV",
    "BITWUZLA_KIND_FP_TO_FP_FROM_FP",
    "BITWUZLA_KIND_FP_TO_FP_FROM_SBV",
    "BITWUZLA_KIND_FP_TO_FP_FROM_UBV",
    "BITWUZLA_KIND_FP_TO_SBV",
    "BITWUZLA_KIND_FP_TO_UBV",
};

static std::unordered_map<node::Kind, BitwuzlaKind>
    s_kind_internal_to_external = {
        {node::Kind::CONSTANT, BITWUZLA_KIND_CONST},
        {node::Kind::VALUE, BITWUZLA_KIND_VAL},
        {node::Kind::VARIABLE, BITWUZLA_KIND_VAR},
        {node::Kind::DISTINCT, BITWUZLA_KIND_DISTINCT},
        {node::Kind::EQUAL, BITWUZLA_KIND_EQUAL},
        {node::Kind::ITE, BITWUZLA_KIND_ITE},

        {node::Kind::AND, BITWUZLA_KIND_AND},
        {node::Kind::IMPLIES, BITWUZLA_KIND_IMPLIES},
        {node::Kind::NOT, BITWUZLA_KIND_NOT},
        {node::Kind::OR, BITWUZLA_KIND_OR},
        {node::Kind::XOR, BITWUZLA_KIND_XOR},

        {node::Kind::BV_ADD, BITWUZLA_KIND_BV_ADD},
        {node::Kind::BV_AND, BITWUZLA_KIND_AND},
        {node::Kind::BV_ASHR, BITWUZLA_KIND_BV_ASHR},
        {node::Kind::BV_COMP, BITWUZLA_KIND_BV_COMP},
        {node::Kind::BV_CONCAT, BITWUZLA_KIND_BV_CONCAT},
        {node::Kind::BV_EXTRACT, BITWUZLA_KIND_BV_EXTRACT},
        {node::Kind::BV_MUL, BITWUZLA_KIND_BV_MUL},
        {node::Kind::BV_NAND, BITWUZLA_KIND_BV_NAND},
        {node::Kind::BV_NEG, BITWUZLA_KIND_BV_NEG},
        {node::Kind::BV_NOR, BITWUZLA_KIND_BV_NOR},
        {node::Kind::BV_NOT, BITWUZLA_KIND_BV_NOT},
        {node::Kind::BV_OR, BITWUZLA_KIND_BV_OR},
        {node::Kind::BV_REDAND, BITWUZLA_KIND_BV_REDAND},
        {node::Kind::BV_REDOR, BITWUZLA_KIND_BV_REDOR},
        {node::Kind::BV_REDXOR, BITWUZLA_KIND_BV_REDXOR},
        {node::Kind::BV_REPEAT, BITWUZLA_KIND_BV_REPEAT},
        {node::Kind::BV_ROL, BITWUZLA_KIND_BV_ROL},
        {node::Kind::BV_ROLI, BITWUZLA_KIND_BV_ROLI},
        {node::Kind::BV_ROR, BITWUZLA_KIND_BV_ROR},
        {node::Kind::BV_RORI, BITWUZLA_KIND_BV_RORI},
        {node::Kind::BV_SADDO, BITWUZLA_KIND_BV_SADD_OVERFLOW},
        {node::Kind::BV_SDIV, BITWUZLA_KIND_BV_SDIV},
        {node::Kind::BV_SDIVO, BITWUZLA_KIND_BV_SDIV_OVERFLOW},
        {node::Kind::BV_SGE, BITWUZLA_KIND_BV_SGE},
        {node::Kind::BV_SGT, BITWUZLA_KIND_BV_SGT},
        {node::Kind::BV_SHL, BITWUZLA_KIND_BV_SHL},
        {node::Kind::BV_SHR, BITWUZLA_KIND_BV_SHR},
        {node::Kind::BV_SIGN_EXTEND, BITWUZLA_KIND_BV_SIGN_EXTEND},
        {node::Kind::BV_SLE, BITWUZLA_KIND_BV_SLE},
        {node::Kind::BV_SLT, BITWUZLA_KIND_BV_SLT},
        {node::Kind::BV_SMOD, BITWUZLA_KIND_BV_SMOD},
        {node::Kind::BV_SMULO, BITWUZLA_KIND_BV_SMUL_OVERFLOW},
        {node::Kind::BV_SREM, BITWUZLA_KIND_BV_SREM},
        {node::Kind::BV_SSUBO, BITWUZLA_KIND_BV_SSUB_OVERFLOW},
        {node::Kind::BV_SUB, BITWUZLA_KIND_BV_SUB},
        {node::Kind::BV_UADDO, BITWUZLA_KIND_BV_UADD_OVERFLOW},
        {node::Kind::BV_UDIV, BITWUZLA_KIND_BV_UDIV},
        {node::Kind::BV_UGE, BITWUZLA_KIND_BV_UGE},
        {node::Kind::BV_UGT, BITWUZLA_KIND_BV_UGT},
        {node::Kind::BV_ULE, BITWUZLA_KIND_BV_ULE},
        {node::Kind::BV_ULT, BITWUZLA_KIND_BV_ULT},
        {node::Kind::BV_UMULO, BITWUZLA_KIND_BV_UMUL_OVERFLOW},
        {node::Kind::BV_UREM, BITWUZLA_KIND_BV_UREM},
        {node::Kind::BV_USUBO, BITWUZLA_KIND_BV_USUB_OVERFLOW},
        {node::Kind::BV_XNOR, BITWUZLA_KIND_BV_XNOR},
        {node::Kind::BV_XOR, BITWUZLA_KIND_BV_XOR},
        {node::Kind::BV_ZERO_EXTEND, BITWUZLA_KIND_BV_ZERO_EXTEND},

        {node::Kind::FP_ADD, BITWUZLA_KIND_FP_ADD},
        {node::Kind::FP_DIV, BITWUZLA_KIND_FP_DIV},
        {node::Kind::FP_EQUAL, BITWUZLA_KIND_FP_EQ},
        {node::Kind::FP_FMA, BITWUZLA_KIND_FP_FMA},
        {node::Kind::FP_GE, BITWUZLA_KIND_FP_GEQ},
        {node::Kind::FP_GT, BITWUZLA_KIND_FP_GT},
        {node::Kind::FP_IS_INF, BITWUZLA_KIND_FP_IS_INF},
        {node::Kind::FP_IS_NAN, BITWUZLA_KIND_FP_IS_NAN},
        {node::Kind::FP_IS_NEG, BITWUZLA_KIND_FP_IS_NEG},
        {node::Kind::FP_IS_NORM, BITWUZLA_KIND_FP_IS_NORMAL},
        {node::Kind::FP_IS_POS, BITWUZLA_KIND_FP_IS_POS},
        {node::Kind::FP_IS_SUBNORM, BITWUZLA_KIND_FP_IS_SUBNORMAL},
        {node::Kind::FP_IS_ZERO, BITWUZLA_KIND_FP_IS_ZERO},
        {node::Kind::FP_LE, BITWUZLA_KIND_FP_LEQ},
        {node::Kind::FP_LT, BITWUZLA_KIND_FP_LT},
        {node::Kind::FP_MAX, BITWUZLA_KIND_FP_MAX},
        {node::Kind::FP_MIN, BITWUZLA_KIND_FP_MIN},
        {node::Kind::FP_MUL, BITWUZLA_KIND_FP_MUL},
        {node::Kind::FP_NEG, BITWUZLA_KIND_FP_NEG},
        {node::Kind::FP_REM, BITWUZLA_KIND_FP_REM},
        {node::Kind::FP_RTI, BITWUZLA_KIND_FP_RTI},
        {node::Kind::FP_SQRT, BITWUZLA_KIND_FP_SQRT},
        {node::Kind::FP_SUB, BITWUZLA_KIND_FP_SUB},
        {node::Kind::FP_TO_FP_FROM_BV, BITWUZLA_KIND_FP_TO_FP_FROM_BV},
        {node::Kind::FP_TO_FP_FROM_FP, BITWUZLA_KIND_FP_TO_FP_FROM_FP},
        {node::Kind::FP_TO_FP_FROM_SBV, BITWUZLA_KIND_FP_TO_FP_FROM_SBV},
        {node::Kind::FP_TO_FP_FROM_UBV, BITWUZLA_KIND_FP_TO_FP_FROM_UBV},
        {node::Kind::FP_TO_SBV, BITWUZLA_KIND_FP_TO_SBV},
        {node::Kind::FP_TO_UBV, BITWUZLA_KIND_FP_TO_UBV},

        {node::Kind::CONST_ARRAY, BITWUZLA_KIND_CONST_ARRAY},
        {node::Kind::SELECT, BITWUZLA_KIND_ARRAY_SELECT},
        {node::Kind::STORE, BITWUZLA_KIND_ARRAY_STORE},

        {node::Kind::EXISTS, BITWUZLA_KIND_EXISTS},
        {node::Kind::FORALL, BITWUZLA_KIND_FORALL},

        {node::Kind::APPLY, BITWUZLA_KIND_APPLY},
        {node::Kind::LAMBDA, BITWUZLA_KIND_LAMBDA}};

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options.at(option))
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (bitwuzla_options.at(option))

/* -------------------------------------------------------------------------- */

#define BZLA_CHECK_OPT_INCREMENTAL(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL), \
             "incremental usage not enabled");

#define BZLA_CHECK_OPT_PRODUCE_MODELS(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS), \
             "model production not enabled");

#define BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_UNSAT_CORES), \
             "unsat core production not enabled");

#define BZLA_CHECK_UNSAT(bzla, what)                     \
  BZLA_ABORT(bzla->last_sat_result != BZLA_RESULT_UNSAT, \
             "cannot %s if input formula is not unsat",  \
             what);

#define BZLA_CHECK_SAT(bzla, what)                                          \
  BZLA_ABORT(                                                               \
      bzla->last_sat_result != BZLA_RESULT_SAT || !bzla->valid_assignments, \
      "cannot %s if input formula is not sat",                              \
      what);

/* -------------------------------------------------------------------------- */

#define BZLA_CHECK_ARG_NOT_NULL(arg) \
  BZLA_ABORT((arg) == NULL, "argument '%s' must not be NULL", #arg)

#define BZLA_CHECK_ARG_NOT_NULL_AT_IDX(arg, idx)           \
  BZLA_ABORT((arg) == NULL,                                \
             "argument '%s' must not be NULL at index %u", \
             #arg,                                         \
             (idx))

#define BZLA_CHECK_ARG_NOT_ZERO(arg) \
  BZLA_ABORT(arg == 0, "argument '%s' must be > 0", #arg)

#define BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(arg) \
  BZLA_ABORT(arg == NULL || *arg == '\0', "expected non-empty string")

#define BZLA_CHECK_ARG_CNT(kind, nary, expected, argc)                         \
  BZLA_ABORT(                                                                  \
      (nary && (argc) < expected) || (!nary && (argc) != (expected)),          \
      "invalid number of arguments for kind '%s', expected '%u' and got '%u'", \
      bzla_kind_to_str[kind],                                                  \
      expected,                                                                \
      argc)

#define BZLA_CHECK_IDX_CNT(kind, expected, argc)                             \
  BZLA_ABORT(                                                                \
      (argc) != (expected),                                                  \
      "invalid number of indices for kind '%s', expected '%u' and got '%u'", \
      bzla_kind_to_str[kind],                                                \
      expected,                                                              \
      argc)

#define BZLA_CHECK_ARGS_SORT(bzla, arg, nextarg, idx, sort_check)    \
  do                                                                 \
  {                                                                  \
    BzlaSortId sorti = bzla_node_get_sort_id(arg);                   \
    BZLA_ABORT(!sort_check(bzla, sorti),                             \
               "node with unexpected sort at index %u",              \
               idx);                                                 \
    if (nextarg)                                                     \
    {                                                                \
      BZLA_ABORT(sorti != bzla_node_get_sort_id(nextarg),            \
                 "terms with mismatching sort at indices %u and %u", \
                 idx,                                                \
                 (idx) + 1);                                         \
    }                                                                \
  } while (0)

#define BZLA_CHECK_MK_TERM_ARGS(                                   \
    kind, nary, args, expected, argc, start, sort_check, match)    \
  do                                                               \
  {                                                                \
    BZLA_CHECK_ARG_CNT(kind, nary, expected, argc);                \
    for (int64_t i = 0, j = 1; i < argc; i++, j++)                 \
    {                                                              \
      BZLA_CHECK_ARG_NOT_NULL_AT_IDX(args[i], i);                  \
      assert(bzla_node_get_ext_refs(args[i]));                     \
      BZLA_CHECK_TERM_BZLA(bzla, args[i]);                         \
      if (i < (start)) continue;                                   \
      BZLA_CHECK_ARGS_SORT(bzla,                                   \
                           args[i],                                \
                           j < (argc) && (match) ? args[j] : NULL, \
                           i,                                      \
                           sort_check);                            \
    }                                                              \
  } while (0)

#define BZLA_CHECK_MK_TERM_ARGS_IDXED(                                         \
    kind, args, expected, argc, idxc_expected, idxc, start, sort_check, match) \
  do                                                                           \
  {                                                                            \
    BZLA_CHECK_MK_TERM_ARGS(                                                   \
        kind, false, args, expected, argc, start, sort_check, match);          \
    BZLA_CHECK_IDX_CNT(kind, idxc_expected, idxc);                             \
  } while (0)

#define BZLA_CHECK_OPTION(bzla, opt) \
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option")

#define BZLA_CHECK_OPTION_VALUE(bzla, opt, value)                              \
  BZLA_ABORT(                                                                  \
      value<bzla_opt_get_min(bzla, opt) || value> bzla_opt_get_max(bzla, opt), \
      "invalid value '%u' for option '%s'",                                    \
      value,                                                                   \
      bzla_opt_get_lng(bzla, opt))

#define BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort)                           \
  do                                                                       \
  {                                                                        \
    BZLA_ABORT(!sort || (sort)->d_bzla != (bitwuzla),                      \
               "sort '%s' is not associated with given solver instance",   \
               #sort);                                                     \
    assert(bzla_sort_is_valid((sort)->d_bzla->d_bzla, sort->d_bzla_sort)); \
  } while (0)

#define BZLA_CHECK_SORT_BITWUZLA_AT_IDX(bitwuzla, sort, idx)                \
  do                                                                        \
  {                                                                         \
    BZLA_ABORT(                                                             \
        !sort || (sort)->d_bzla != (bitwuzla),                              \
        "sort %s is not associated with given solver instance at index %u", \
        #sort,                                                              \
        (idx));                                                             \
    assert(bzla_sort_is_valid((sort)->d_bzla->d_bzla, sort->d_bzla_sort));  \
  } while (0)

#define BZLA_CHECK_SORT_IS_ARRAY(bzla, sort)                        \
  BZLA_ABORT(!bzla_sort_is_fun(bzla, sort)                          \
                 || bzla_sort_tuple_get_arity(                      \
                        bzla, bzla_sort_fun_get_domain(bzla, sort)) \
                        != 1,                                       \
             "expected array sort");

#define BZLA_CHECK_SORT_IS_BV(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_bv(bzla, sort), "expected bit-vector sort")

#define BZLA_CHECK_SORT_IS_FP(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_fp(bzla, sort), "expected floating-point sort")

#define BZLA_CHECK_SORT_IS_FP_AT_IDX(bzla, sort, idx)    \
  BZLA_ABORT(!bzla_sort_is_fp(bzla, sort),               \
             "expected floating-point sort at index %u", \
             (idx))

#define BZLA_CHECK_SORT_IS_FUN(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_fun(bzla, sort), "expected function sort")

#define BZLA_CHECK_SORT_NOT_IS_FUN(bzla, sort)                            \
  do                                                                      \
  {                                                                       \
    BZLA_ABORT(bzla_sort_is_array(bzla, sort), "unexpected array sort");  \
    BZLA_ABORT(bzla_sort_is_fun(bzla, sort), "unexpected function sort"); \
  } while (0)

#define BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, sort, idx) \
  do                                                       \
  {                                                        \
    BZLA_ABORT(bzla_sort_is_array(bzla, sort),             \
               "unexpected function sort at index %u",     \
               (idx));                                     \
    BZLA_ABORT(bzla_sort_is_fun(bzla, sort),               \
               "unexpected function sort at index %u",     \
               (idx));                                     \
  } while (0)

#define BZLA_CHECK_TERM_BZLA(bzla, term)                               \
  BZLA_ABORT(bzla_node_get_bzla(term) != bzla,                         \
             "term '%s' is not associated with given solver instance", \
             #term);

#define BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, term, idx)   \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term),              \
             "expected rounding-mode term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_BOOL(bzla, term)                         \
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_get_sort_id(term)), \
             "expected boolean term")

#define BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, term, idx)             \
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_get_sort_id(term)), \
             "expected boolean term at index %u",                   \
             (idx))

#define BZLA_CHECK_TERM_IS_BV(bzla, term) \
  BZLA_ABORT(!bzla_node_is_bv(bzla, term), "expected bit-vector term")

#define BZLA_CHECK_TERM_IS_BV_AT_IDX(bzla, term, idx) \
  BZLA_ABORT(!bzla_node_is_bv(bzla, term),            \
             "expected bit-vector term at index %u",  \
             (idx))

#define BZLA_CHECK_TERM_IS_BV_LAMBDA_AT_IDX(bzla, term, idx)                \
  BZLA_ABORT(                                                               \
      !bzla_node_is_bv(bzla, term)                                          \
          && (!bzla_node_is_fun(term)                                       \
              || !bzla_sort_is_bv(bzla,                                     \
                                  bzla_sort_fun_get_codomain(               \
                                      bzla, bzla_node_get_sort_id(term)))), \
      "expected bit-vector term or bit-vector function term at index %u",   \
      (idx))

#define BZLA_CHECK_TERM_IS_FP(bzla, term) \
  BZLA_ABORT(!bzla_node_is_fp(bzla, term), "expected floating-point term")

#define BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, term, idx)    \
  BZLA_ABORT(!bzla_node_is_fp(bzla, term),               \
             "expected floating-point term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_RM(bzla, term) \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term), "expected rounding-mode term")

#define BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, term, idx)   \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term),              \
             "expected rounding-mode term at index %u", \
             (idx))

#define BZLA_CHECK_TERM_IS_ARRAY(term)                                        \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected array term")

#define BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(term, idx)                            \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected array term at index %u",                                      \
      (idx))

#define BZLA_CHECK_TERM_IS_BV_VAL(term)                              \
  BZLA_ABORT(!bzla_node_is_bv_const(                                 \
                 bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected bit-vector value")

#define BZLA_CHECK_TERM_IS_VAR(term)                                     \
  BZLA_ABORT(bzla_node_is_inverted(term)                                 \
                 || !bzla_node_is_param(                                 \
                     bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected variable term")

#define BZLA_CHECK_TERM_IS_VAR_AT_IDX(term, idx)                         \
  BZLA_ABORT(bzla_node_is_inverted(term)                                 \
                 || !bzla_node_is_param(                                 \
                     bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
             "expected variable term at index %u",                       \
             (idx))

#define BZLA_CHECK_TERM_IS_FUN(term)                                        \
  BZLA_ABORT(                                                               \
      !bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "unexpected function term at index")

#define BZLA_CHECK_TERM_IS_FUN_AT_IDX(term, idx)                            \
  BZLA_ABORT(                                                               \
      !bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected function term at index %u",                                 \
      (idx))

#define BZLA_CHECK_TERM_NOT_IS_FUN(term)                                       \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
        "unexpected array term");                                              \
    BZLA_ABORT(                                                                \
        bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)),   \
        "unexpected function term");                                           \
  } while (0)

#define BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(term, idx)                           \
  do                                                                           \
  {                                                                            \
    BZLA_ABORT(                                                                \
        bzla_node_is_array(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
        "unexpected array term at index %u",                                   \
        (idx));                                                                \
    BZLA_ABORT(                                                                \
        bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)),   \
        "unexpected function term at index %u",                                \
        (idx));                                                                \
  } while (0)

#define BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(term)                           \
  BZLA_ABORT(                                                                \
      bzla_node_real_addr(bzla_simplify_exp(bzla_node_get_bzla(term), term)) \
          ->parameterized,                                                   \
      "term must not be parameterized");

#define BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(term, idx)                           \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_lambda(bzla_simplify_exp(bzla_node_get_bzla(term), term)) \
          && bzla_node_is_fun(                                                \
              bzla_simplify_exp(bzla_node_get_bzla(term), term)),             \
      "unexpected function term at index %u",                                 \
      (idx))

#define BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(term, idx) \
  BZLA_ABORT(bzla_node_param_is_bound(term),               \
             "expected unbound variable term at index %u", \
             (idx))

/* -------------------------------------------------------------------------- */

static Node
mk_term_left_assoc(node::Kind kind, const std::vector<Node> &children)
{
  assert(children.size() >= 2);
  Node res, tmp;

  NodeManager &nm = NodeManager::get();
  res             = nm.mk_node(kind, {children[0], children[1]});
  for (uint32_t i = 2; i < children.size(); i++)
  {
    tmp = nm.mk_node(kind, {res, children[i]});
    res = tmp;
  }
  return res;
}

static Node
mk_term_right_assoc(node::Kind kind, const std::vector<Node> &children)
{
  assert(children.size() >= 2);
  Node res, tmp;
  NodeManager &nm = NodeManager::get();
  res             = children.back();
  for (uint32_t i = 1, size = children.size(); i < size; ++i)
  {
    tmp = nm.mk_node(kind, {children[size - i - 1], res});
    res = tmp;
  }
  assert(!res.is_null());
  return res;
}

static Node
mk_term_chained(node::Kind kind, const std::vector<Node> &children)
{
  assert(children.size() >= 2);
  Node res, tmp, old;

  NodeManager &nm = NodeManager::get();
  for (uint32_t i = 0, j = 1; j < children.size(); i++, j++)
  {
    tmp = nm.mk_node(kind, {children[i], children[j]});
    if (!res.is_null())
    {
      old = res;
      res = nm.mk_node(node::Kind::AND, {old, tmp});
    }
    else
    {
      res = tmp;
    }
  }
  assert(!res.is_null());
  return res;
}

static Node
mk_term_binder(node::Kind kind, const std::vector<Node> &children)
{
  assert(children.size() >= 2);
  NodeManager &nm = NodeManager::get();
  Node res        = children.back();
  for (size_t i = 1, size = children.size(); i < size; ++i)
  {
    const auto &var = children[size - 1 - i];
    assert(var.kind() == node::Kind::VARIABLE);
    res = nm.mk_node(kind, {var, res});
  }
  return res;
}

static const BitwuzlaSort *
export_sort(Bitwuzla *bitwuzla, const Type &type)
{
  assert(bitwuzla);
  assert(!type.is_null());

  BitwuzlaSort *res;
  const auto it = bitwuzla->d_sort_map.find(type);
  if (it == bitwuzla->d_sort_map.end())
  {
    res = new BitwuzlaSort(bitwuzla, type);
    bitwuzla->d_sort_map.emplace(type, res);
  }
  else
  {
    res = it->second.get();
  }
  return res;
}

static const BitwuzlaTerm *
export_term(Bitwuzla *bitwuzla, const Node &node)
{
  assert(bitwuzla);
  assert(!node.is_null());

  BitwuzlaTerm *res;
  const auto it = bitwuzla->d_node_map.find(node);
  if (it == bitwuzla->d_node_map.end())
  {
    res = new BitwuzlaTerm(bitwuzla, node);
    bitwuzla->d_node_map.emplace(node, res);
  }
  else
  {
    res = it->second.get();
  }
  return res;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaKind                                                               */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_kind_to_string(BitwuzlaKind kind)
{
  BZLA_ABORT(kind >= BITWUZLA_NUM_KINDS, "invalid term kind");
  return bzla_kind_to_str[kind];
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_rm_to_string(BitwuzlaRoundingMode rm)
{
  switch (rm)
  {
    case BITWUZLA_RM_RNA: return "RNA"; break;
    case BITWUZLA_RM_RNE: return "RNE"; break;
    case BITWUZLA_RM_RTN: return "RTN"; break;
    case BITWUZLA_RM_RTP: return "RTP"; break;
    default:
      BZLA_ABORT(rm != BITWUZLA_RM_RTZ, "invalid rounding mode");
      return "RTZ";
  }
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult                                                             */
/* -------------------------------------------------------------------------- */

const char *
bitwuzla_result_to_string(BitwuzlaResult result)
{
  switch (result)
  {
    case BITWUZLA_SAT: return "sat"; break;
    case BITWUZLA_UNSAT: return "unsat"; break;
    default:
      BZLA_ABORT(result != BITWUZLA_UNKNOWN, "invalid result kind");
      return "unknown";
  }
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_new(void)
{
  return new Bitwuzla();
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  delete bitwuzla;
}

void
bitwuzla_reset(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  bitwuzla->reset();
}

const char *
bitwuzla_copyright(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return BZLA_LICENSE
      "\n\n"
      "This version of Bitwuzla is linked against the following\n"
      "third party libraries. For copyright information of each\n"
      "library see the corresponding url.\n"
      "\n"
      "  Btor2Tools - tools for the BTOR2 format\n"
      "  https://https://github.com/Boolector/btor2tools\n"
      "\n"
      "  GMP - GNU Multiple Precision Arithmetic Library\n"
      "  https://gmplib.org \n"
#ifdef BZLA_USE_LINGELING
      "\n"
      "  Lingeling\n"
      "  https://github.com/arminbiere/lingeling\n"
#endif
#ifdef BZLA_USE_CADICAL
      "\n"
      "  CaDiCaL\n"
      "  https://github.com/arminbiere/cadical\n"
#endif
#ifdef BZLA_USE_CMS
      "\n"
      "  CryptoMiniSat\n"
      "  https://github.com/msoos/cryptominisat\n"
#endif
      "\n"
      "  SymFPU\n"
      "  https://github.com/martin-cs/symfpu \n"
      "";
}

const char *
bitwuzla_version(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO:
  assert(false);
  return nullptr;
}

const char *
bitwuzla_git_id(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO:
  assert(false);
  return nullptr;
}

bool
bitwuzla_terminate(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO:
  return false;
}

void
bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                  int32_t (*fun)(void *),
                                  void *state)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

void *
bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
  return nullptr;
}

void
bitwuzla_set_abort_callback(void (*fun)(const char *msg))
{
  // TODO
}

void
bitwuzla_set_option(Bitwuzla *bitwuzla, BitwuzlaOption option, uint32_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO
#if 0
  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_CHECK_OPTION_VALUE(bzla, opt, value);

  if (option == BITWUZLA_OPT_INCREMENTAL)
  {
    BZLA_ABORT(bzla->bzla_sat_bzla_called > 0,
               "enabling/disabling incremental usage after having called "
               "'bitwuzla_check_sat' is not allowed");
  }

  if (value)
  {
    if (option == BITWUZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)),
                 "incremental solving cannot be enabled "
                 "if unconstrained optimization is enabled");
    }
    else if (option == BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)
    {
      BZLA_ABORT(
          bzla_opt_get(
              bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_PRODUCE_MODELS)),
          "unconstrained optimization cannot be enabled "
          "if model generation is enabled");
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_INCREMENTAL)),
          "unconstrained optimization cannot be enabled "
          "in incremental mode");
    }
    else if (option == BITWUZLA_OPT_FUN_DUAL_PROP)
    {
      BZLA_ABORT(bzla_opt_get(
                     bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_JUST)),
                 "enabling multiple optimization techniques is not allowed");
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_NONDESTR_SUBST)),
                 "non-destructive substitution is not supported with dual "
                 "propagation");
    }
    else if (option == BITWUZLA_OPT_FUN_JUST)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_DUAL_PROP)),
          "enabling multiple optimization techniques is not allowed");
    }
    else if (option == BITWUZLA_OPT_PP_NONDESTR_SUBST)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_DUAL_PROP)),
          "non-destructive substitution is not supported with dual "
          "propagation");
    }
    else if (option == BITWUZLA_OPT_PRODUCE_MODELS)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION)),
                 "model generation cannot be enabled "
                 "if unconstrained optimization is enabled");
    }
  }
  else
  {
    if (option == BITWUZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT(bzla_opt_get(bzla,
                              BZLA_IMPORT_BITWUZLA_OPTION(
                                  BITWUZLA_OPT_PRODUCE_UNSAT_CORES)),
                 "incremental solving cannot be disabled "
                 "when unsat cores are enabled");
    }
  }

  uint32_t val = bzla_opt_get(bzla, opt);

  if (opt == BZLA_OPT_SAT_ENGINE)
  {
    if (false
#ifndef BZLA_USE_LINGELING
        || value == BZLA_SAT_ENGINE_LINGELING
#endif
#ifndef BZLA_USE_CADICAL
        || value == BZLA_SAT_ENGINE_CADICAL
#endif
#ifndef BZLA_USE_CMS
        || value == BZLA_SAT_ENGINE_CMS
#endif
    )
    {
      BZLA_WARN(true,
                "SAT solver %s not compiled in, using %s",
                g_bzla_se_name[value],
                g_bzla_se_name[val]);
      value = val;
    }
  }
#ifndef BZLA_USE_LINGELING
  if (opt == BZLA_OPT_SAT_ENGINE_LGL_FORK)
  {
    value = val;
    BZLA_WARN(true,
              "SAT solver Lingeling not compiled in, will not set option "
              "to clone/fork Lingeling");
  }
#endif
  if (opt == BZLA_OPT_RW_LEVEL)
  {
    BZLA_ABORT(
        BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }
  bzla_opt_set(bzla, opt, value);
#endif
}

void
bitwuzla_set_option_str(Bitwuzla *bitwuzla,
                        BitwuzlaOption option,
                        const char *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO
#if 0
  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_ABORT(
      !bzla_opt_is_enum_option(bzla, opt),
      "option expects an integer value, use bitwuzla_set_option instead.");
  BZLA_ABORT(!bzla_opt_is_enum_option_value(bzla, opt, value),
             "invalid option value '%s'",
             value);

  bzla_opt_set(bzla, opt, bzla_opt_get_enum_value(bzla, opt, value));
#endif
}

uint32_t
bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO
#if 0
  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  return bzla_opt_get(bzla, opt);
#endif
  return 0;
}

const char *
bitwuzla_get_option_str(Bitwuzla *bitwuzla, BitwuzlaOption option)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO

#if 0
  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_ABORT(!bzla_opt_is_enum_option(bzla, opt),
             "option is configured with an integer value, use "
             "bitwuzla_get_option instead.");
  return bzla_opt_get_str_value(bzla, opt);
#endif
  return nullptr;
}

void
bitwuzla_get_option_info(Bitwuzla *bitwuzla,
                         BitwuzlaOption option,
                         BitwuzlaOptionInfo *info)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(info);

  // TODO
#if 0
  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);

  BZLA_CLR(info);
  info->opt        = option;
  info->shrt       = bzla_opt_get_shrt(bzla, opt);
  info->lng        = bzla_opt_get_lng(bzla, opt);
  info->desc       = bzla_opt_get_desc(bzla, opt);
  info->is_numeric = !bzla_opt_is_enum_option(bzla, opt);

  if (info->is_numeric)
  {
    info->numeric.cur_val = bzla_opt_get(bzla, opt);
    info->numeric.def_val = bzla_opt_get_dflt(bzla, opt);
    info->numeric.min_val = bzla_opt_get_min(bzla, opt);
    info->numeric.max_val = bzla_opt_get_max(bzla, opt);
  }
  else
  {
    BZLA_RESET_STACK(bitwuzla->d_option_info_values);
    info->string.cur_val = bzla_opt_get_str_value(bzla, opt);

    int32_t def_val = bzla_opt_get_dflt(bzla, opt);
    BzlaPtrHashTableIterator it;
    BzlaOptHelp *oh;
    bzla_iter_hashptr_init(&it, bzla->options[opt].options);
    while (bzla_iter_hashptr_has_next(&it))
    {
      oh = static_cast<BzlaOptHelp *>(it.bucket->data.as_ptr);
      BZLA_PUSH_STACK(bitwuzla->d_option_info_values,
                      static_cast<const char *>(bzla_iter_hashptr_next(&it)));
      if (oh->val == def_val)
      {
        info->string.def_val = BZLA_TOP_STACK(bitwuzla->d_option_info_values);
      }
    }
    info->string.num_values = BZLA_COUNT_STACK(bitwuzla->d_option_info_values);
    info->string.values     = bitwuzla->d_option_info_values.start;
  }
#endif
}

const BitwuzlaSort *
bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                       const BitwuzlaSort *index,
                       const BitwuzlaSort *element)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(index);
  BZLA_CHECK_ARG_NOT_NULL(element);

  Type type = NodeManager::get().mk_array_type(index->d_type, element->d_type);
  return export_sort(bitwuzla, type);
}

const BitwuzlaSort *
bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Type type = NodeManager::get().mk_bool_type();
  return export_sort(bitwuzla, type);
}

const BitwuzlaSort *
bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(size);

  Type type = NodeManager::get().mk_bv_type(size);
  return export_sort(bitwuzla, type);
}

const BitwuzlaSort *
bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla, uint32_t exp_size, uint32_t sig_size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(exp_size <= 1, "argument 'exp_size' must be > 1")
  BZLA_ABORT(sig_size <= 1, "argument 'sig_size' must be > 1")

  Type type = NodeManager::get().mk_fp_type(exp_size, sig_size);
  return export_sort(bitwuzla, type);
}

const BitwuzlaSort *
bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                     uint32_t arity,
                     const BitwuzlaSort *domain[],
                     const BitwuzlaSort *codomain)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(arity);
  BZLA_CHECK_ARG_NOT_NULL(domain);
  BZLA_CHECK_ARG_NOT_NULL(codomain);

  // TODO: checks
  // BZLA_CHECK_SORT_NOT_IS_FUN(bzla, cdom);

  std::vector<Type> types;
  for (uint32_t i = 0; i < arity; i++)
  {
    // TODO: checks
    //    BZLA_CHECK_SORT_BITWUZLA_AT_IDX(bitwuzla, domain[i], i);
    //    BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, dom[i], i);
    types.push_back(domain[i]->d_type);
  }
  types.push_back(codomain->d_type);

  Type type = NodeManager::get().mk_fun_type(types);
  return export_sort(bitwuzla, type);
}

const BitwuzlaSort *
bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Type type = NodeManager::get().mk_rm_type();
  return export_sort(bitwuzla, type);
}

const BitwuzlaTerm *
bitwuzla_mk_true(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  Node term = NodeManager::get().mk_value(true);
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_false(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  Node term = NodeManager::get().mk_value(false);
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(BitVector::mk_zero(sort->d_type.bv_size()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(BitVector::mk_one(sort->d_type.bv_size()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(BitVector::mk_ones(sort->d_type.bv_size()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  Node term = NodeManager::get().mk_value(
      BitVector::mk_min_signed(sort->d_type.bv_size()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  Node term = NodeManager::get().mk_value(
      BitVector::mk_max_signed(sort->d_type.bv_size()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(FloatingPoint::fpzero(sort->d_type, true));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(FloatingPoint::fpzero(sort->d_type, false));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(FloatingPoint::fpinf(sort->d_type, true));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term =
      NodeManager::get().mk_value(FloatingPoint::fpinf(sort->d_type, false));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term = NodeManager::get().mk_value(FloatingPoint::fpnan(sort->d_type));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                     const BitwuzlaSort *sort,
                     const char *value,
                     BitwuzlaBVBase base)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(value);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  // uint32_t size = bzla_sort_bv_get_width(bzla, bzla_sort);
  // BZLA_ABORT(
  //    !bzla_bv_str_fits_in_size(size,
  //                              value,
  //                              base == BITWUZLA_BV_BASE_BIN
  //                                  ? 2
  //                                  : (base == BITWUZLA_BV_BASE_DEC ? 10 :
  //                                  16)),
  //    "given string does not fit into a bit-vector of size %u",
  //    size);

  uint64_t size  = sort->d_type.bv_size();
  uint32_t _base = 0;
  switch (base)
  {
    case BITWUZLA_BV_BASE_BIN: {
      _base = 2;
      for (const char *p = value; *p; p++)
      {
        BZLA_ABORT(*p != '1' && *p != '0', "invalid binary string '%s'", value);
      }
      BZLA_ABORT(size < strlen(value),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      break;
    }

    case BITWUZLA_BV_BASE_DEC: {
      _base         = 10;
      const char *p = value;
      if (*p && p[0] == '-')
      {
        ++p;
      }
      BZLA_ABORT(!*p, "invalid decimal string '%s'", value);
      for (; *p; p++)
      {
        /* 48-57: 0-9 */
        BZLA_ABORT(*p < '0' || *p > '9', "invalid decimal string '%s'", value);
      }
      // TODO: check
      // BZLA_ABORT(!bzla_util_check_dec_to_bv(bzla->mm, value, size),
      //           "value '%s' does not fit into a bit-vector of size %u",
      //           value,
      //           size);
      break;
    }

    default:
      BZLA_ABORT(base != BITWUZLA_BV_BASE_HEX,
                 "invalid base for numerical string '%s'",
                 value);
      _base = 16;
      for (const char *p = value; *p; p++)
      {
        /* 48-57: 0-9, 65-70: A-F, 97-102: a-f */
        BZLA_ABORT((*p < 48 || *p > 57) && (*p < 65 || *p > 70)
                       && (*p < 97 || *p > 102),
                   "invalid hex string '%s'",
                   value);
      }
      // TODO: check
      // BZLA_ABORT(!bzla_util_check_hex_to_bv(bzla->mm, value, size),
      //           "value '%s' does not fit into a bit-vector of size %u",
      //           value,
      //           size);
      break;
  }
  Node term = NodeManager::get().mk_value(
      BitVector(sort->d_type.bv_size(), value, _base));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
                            const BitwuzlaSort *sort,
                            uint64_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: checks
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  // BZLA_ABORT(!bzla_bv_uint64_fits_in_size(
  //               bzla_sort_bv_get_width(bzla, bzla_sort), value),
  //           "given value '%lu' does not fit into a bit-vector of size %u",
  //           value,
  //           bzla_sort_bv_get_width(bzla, bzla_sort));

  Node term = NodeManager::get().mk_value(
      BitVector::from_ui(sort->d_type.bv_size(), value));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_bv_value_int64(Bitwuzla *bitwuzla,
                           const BitwuzlaSort *sort,
                           int64_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: checks
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  // BZLA_ABORT(!bzla_bv_int64_fits_in_size(
  //               bzla_sort_bv_get_width(bzla, bzla_sort), value),
  //           "given value '%lu' does not fit into a bit-vector of size %u",
  //           value,
  //           bzla_sort_bv_get_width(bzla, bzla_sort));

  Node term = NodeManager::get().mk_value(
      BitVector::from_si(sort->d_type.bv_size(), value));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                     const BitwuzlaTerm *bv_sign,
                     const BitwuzlaTerm *bv_exponent,
                     const BitwuzlaTerm *bv_significand)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(bv_sign);
  BZLA_CHECK_ARG_NOT_NULL(bv_exponent);
  BZLA_CHECK_ARG_NOT_NULL(bv_significand);

  // TODO: checks
  // BZLA_CHECK_TERM_BZLA(bzla, sign);
  // BZLA_CHECK_TERM_BZLA(bzla, exp);
  // BZLA_CHECK_TERM_BZLA(bzla, sig);
  // BZLA_CHECK_TERM_IS_BV(bzla, sign);
  // BZLA_CHECK_TERM_IS_BV(bzla, exp);
  // BZLA_CHECK_TERM_IS_BV(bzla, sig);
  // BZLA_CHECK_TERM_IS_BV_VAL(sign);
  // BZLA_CHECK_TERM_IS_BV_VAL(exp);
  // BZLA_CHECK_TERM_IS_BV_VAL(sig);
  // BZLA_ABORT(
  //    bzla_node_bv_get_width(bzla, sign) != 1,
  //    "invalid bit-vector size for argument 'bv_sign', expected size one");

  Node term = NodeManager::get().mk_value(
      FloatingPoint::fpfp(bv_sign->d_node.value<BitVector>(),
                          bv_exponent->d_node.value<BitVector>(),
                          bv_significand->d_node.value<BitVector>()));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value_from_real(Bitwuzla *bitwuzla,
                               const BitwuzlaSort *sort,
                               const BitwuzlaTerm *rm,
                               const char *real)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(rm);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(real);
  // TODO: checks
  // BZLA_ABORT(!bzla_util_is_valid_real(real),
  //           "invalid value '%s', expected real number",
  //           real);
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term = NodeManager::get().mk_value(FloatingPoint::from_real(
      sort->d_type, rm->d_node.value<RoundingMode>(), real));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_fp_value_from_rational(Bitwuzla *bitwuzla,
                                   const BitwuzlaSort *sort,
                                   const BitwuzlaTerm *rm,
                                   const char *num,
                                   const char *den)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(rm);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(num);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(den);
  // TODO: checks
  // BZLA_ABORT(!bzla_util_is_valid_real(num),
  //           "invalid value '%s' for numerator, expected real number");
  // BZLA_ABORT(!bzla_util_is_valid_real(den),
  //           "invalid value '%s' for denominator, expected real number");
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  Node term = NodeManager::get().mk_value(FloatingPoint::from_rational(
      sort->d_type, rm->d_node.value<RoundingMode>(), num, den));
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(rm >= BITWUZLA_RM_MAX, "invalid rounding mode");
  RoundingMode _rm;
  switch (rm)
  {
    case BITWUZLA_RM_RNA: _rm = RoundingMode::RNA; break;
    case BITWUZLA_RM_RNE: _rm = RoundingMode::RNE; break;
    case BITWUZLA_RM_RTN: _rm = RoundingMode::RTN; break;
    case BITWUZLA_RM_RTP: _rm = RoundingMode::RTP; break;
    default: assert(rm == BITWUZLA_RM_RTZ); _rm = RoundingMode::RTZ;
  }
  Node term = NodeManager::get().mk_value(_rm);
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg)
{
  const BitwuzlaTerm *args[] = {arg};
  return bitwuzla_mk_term(bitwuzla, kind, 1, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  return bitwuzla_mk_term(bitwuzla, kind, 2, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1,
                  const BitwuzlaTerm *arg2)
{
  const BitwuzlaTerm *args[] = {arg0, arg1, arg2};
  return bitwuzla_mk_term(bitwuzla, kind, 3, args);
}

const BitwuzlaTerm *
bitwuzla_mk_term(Bitwuzla *bitwuzla,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 const BitwuzlaTerm *args[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  NodeManager &nm = NodeManager::get();
  Node term;
  std::vector<Node> children;
  for (uint32_t i = 0; i < argc; ++i)
  {
    BZLA_CHECK_ARG_NOT_NULL(args[i]);
    children.push_back(args[i]->d_node);
  }
  switch (kind)
  {
    case BITWUZLA_KIND_EQUAL:
      // TODO: checks
      //      BZLA_CHECK_MK_TERM_ARGS(
      //          kind, true, bzla_args.data(), 2, argc, 0, sort_any, true);
      term = mk_term_chained(node::Kind::EQUAL, children);
      break;

    case BITWUZLA_KIND_DISTINCT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, sort_any, true);
      term = nm.mk_node(node::Kind::DISTINCT, children);
      break;

    case BITWUZLA_KIND_IMPLIES:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bool, true);
      term = mk_term_right_assoc(node::Kind::IMPLIES, children);
      break;

    case BITWUZLA_KIND_IFF:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bool, true);
      term = nm.mk_node(node::Kind::EQUAL, children);
      break;

    case BITWUZLA_KIND_NOT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bool, true);
      term = nm.mk_node(node::Kind::NOT, children);
      break;

    case BITWUZLA_KIND_AND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bool, true);
      term = mk_term_left_assoc(node::Kind::AND, children);
      break;

    case BITWUZLA_KIND_OR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bool, true);
      term = mk_term_left_assoc(node::Kind::OR, children);
      break;

    case BITWUZLA_KIND_XOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bool, true);
      term = mk_term_left_assoc(node::Kind::XOR, children);
      break;

    case BITWUZLA_KIND_BV_COMP:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_COMP, children);
      break;

    case BITWUZLA_KIND_BV_NOT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_NOT, children);
      break;

    case BITWUZLA_KIND_BV_NEG:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_NEG, children);
      break;

    case BITWUZLA_KIND_BV_REDOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_REDOR, children);
      break;

    case BITWUZLA_KIND_BV_REDXOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_REDXOR, children);
      break;

    case BITWUZLA_KIND_BV_REDAND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_REDAND, children);
      break;

    case BITWUZLA_KIND_BV_XOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = mk_term_left_assoc(node::Kind::BV_XOR, children);
      break;

    case BITWUZLA_KIND_BV_XNOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_XNOR, children);
      break;

    case BITWUZLA_KIND_BV_AND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_AND, children);
      break;

    case BITWUZLA_KIND_BV_NAND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_NAND, children);
      break;

    case BITWUZLA_KIND_BV_OR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_OR, children);
      break;

    case BITWUZLA_KIND_BV_NOR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_NOR, children);
      break;

    case BITWUZLA_KIND_BV_ADD:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = mk_term_left_assoc(node::Kind::BV_ADD, children);
      break;

    case BITWUZLA_KIND_BV_UADD_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UADDO, children);
      break;

    case BITWUZLA_KIND_BV_SADD_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SADDO, children);
      break;

    case BITWUZLA_KIND_BV_MUL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_MUL, children);
      break;

    case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UMULO, children);
      break;

    case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SMULO, children);
      break;

    case BITWUZLA_KIND_BV_ULT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ULT, children);
      break;

    case BITWUZLA_KIND_BV_SLT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SLT, children);
      break;

    case BITWUZLA_KIND_BV_ULE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ULE, children);
      break;

    case BITWUZLA_KIND_BV_SLE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SLE, children);
      break;

    case BITWUZLA_KIND_BV_UGT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UGT, children);
      break;

    case BITWUZLA_KIND_BV_SGT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SGT, children);
      break;

    case BITWUZLA_KIND_BV_UGE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UGE, children);
      break;

    case BITWUZLA_KIND_BV_SGE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SGE, children);
      break;

    case BITWUZLA_KIND_BV_SHL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SHL, children);
      break;

    case BITWUZLA_KIND_BV_SHR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SHR, children);
      break;

    case BITWUZLA_KIND_BV_ASHR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ASHR, children);
      break;

    case BITWUZLA_KIND_BV_SUB:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SUB, children);
      break;

    case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_USUBO, children);
      break;

    case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SSUBO, children);
      break;

    case BITWUZLA_KIND_BV_UDIV:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UDIV, children);
      break;

    case BITWUZLA_KIND_BV_SDIV:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SDIV, children);
      break;

    case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SDIVO, children);
      break;

    case BITWUZLA_KIND_BV_UREM:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_UREM, children);
      break;

    case BITWUZLA_KIND_BV_SREM:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SREM, children);
      break;

    case BITWUZLA_KIND_BV_SMOD:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_SMOD, children);
      break;

    case BITWUZLA_KIND_BV_ROL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ROL, children);
      break;

    case BITWUZLA_KIND_BV_ROR:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ROR, children);
      break;

    case BITWUZLA_KIND_BV_INC:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      assert(false);
      // TODO: remove?
      break;

    case BITWUZLA_KIND_BV_DEC:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_bv, true);
      assert(false);
      // TODO: remove?
      break;

    case BITWUZLA_KIND_BV_CONCAT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_bv, false);
      term = mk_term_left_assoc(node::Kind::BV_CONCAT, children);
      break;

    case BITWUZLA_KIND_FP_FP: {
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 0, bzla_sort_is_bv, false);
      // BZLA_ABORT(
      //    bzla_node_bv_get_width(bzla, bzla_args[0]) != 1,
      //    "invalid bit-vector size for argument at index 0, expected size 1");
      term = nm.mk_node(
          node::Kind::FP_TO_FP_FROM_BV,
          {nm.mk_node(
              node::Kind::BV_CONCAT,
              {children[0],
               nm.mk_node(node::Kind::BV_CONCAT, {children[1], children[2]})})},
          {children[0].type().bv_size() + children[2].type().bv_size(),
           children[1].type().bv_size()});
    }
    break;

    case BITWUZLA_KIND_FP_ABS:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_ABS, children);
      break;

    case BITWUZLA_KIND_FP_NEG:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_NEG, children);
      break;

    case BITWUZLA_KIND_FP_IS_NORMAL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_NORM, children);
      break;

    case BITWUZLA_KIND_FP_IS_SUBNORMAL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_SUBNORM, children);
      break;

    case BITWUZLA_KIND_FP_IS_NAN:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_NAN, children);
      break;

    case BITWUZLA_KIND_FP_IS_ZERO:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_ZERO, children);
      break;

    case BITWUZLA_KIND_FP_IS_INF:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_INF, children);
      break;

    case BITWUZLA_KIND_FP_IS_NEG:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_NEG, children);
      break;

    case BITWUZLA_KIND_FP_IS_POS:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 1, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_IS_POS, children);
      break;

    case BITWUZLA_KIND_FP_MIN:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_MIN, children);
      break;

    case BITWUZLA_KIND_FP_MAX:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_MAX, children);
      break;

    case BITWUZLA_KIND_FP_REM:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = nm.mk_node(node::Kind::FP_REM, children);
      break;

    case BITWUZLA_KIND_FP_EQ:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = mk_term_chained(node::Kind::FP_EQUAL, children);
      break;

    case BITWUZLA_KIND_FP_LEQ:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = mk_term_chained(node::Kind::FP_LE, children);
      break;

    case BITWUZLA_KIND_FP_LT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = mk_term_chained(node::Kind::FP_LT, children);
      break;

    case BITWUZLA_KIND_FP_GEQ:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = mk_term_chained(node::Kind::FP_GE, children);
      break;

    case BITWUZLA_KIND_FP_GT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, true, bzla_args.data(), 2, argc, 0, bzla_sort_is_fp, true);
      term = mk_term_chained(node::Kind::FP_GT, children);
      break;

    case BITWUZLA_KIND_FP_SQRT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_SQRT, children);
      break;

    case BITWUZLA_KIND_FP_RTI:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_RTI, children);
      break;

    case BITWUZLA_KIND_FP_ADD:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_ADD, children);
      break;

    case BITWUZLA_KIND_FP_SUB:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_SUB, children);
      break;

    case BITWUZLA_KIND_FP_MUL:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_MUL, children);
      break;

    case BITWUZLA_KIND_FP_DIV:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_DIV, children);
      break;

    case BITWUZLA_KIND_FP_FMA:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 4, argc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_FMA, children);
      break;

    case BITWUZLA_KIND_ARRAY_SELECT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 2, argc, 0, sort_any, false);
      // BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      // BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      // BZLA_ABORT(
      //    bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
      //        != bzla_node_get_sort_id(bzla_args[1]),
      //    "sort of index term does not match index sort of array");
      term = nm.mk_node(node::Kind::SELECT, children);
      break;

    case BITWUZLA_KIND_ARRAY_STORE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 0, sort_any, false);
      // BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      // BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      // BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[2], 2);
      // BZLA_ABORT(
      //    bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
      //        != bzla_node_get_sort_id(bzla_args[1]),
      //    "sort of index term does not match index sort of array");
      // BZLA_ABORT(
      //    bzla_sort_array_get_element(bzla,
      //    bzla_node_get_sort_id(bzla_args[0]))
      //        != bzla_node_get_sort_id(bzla_args[2]),
      //    "sort of element term does not match element sort of array");
      term = nm.mk_node(node::Kind::STORE, children);
      break;

    case BITWUZLA_KIND_ITE:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS(
      //    kind, false, bzla_args.data(), 3, argc, 1, sort_any, true);
      // BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::ITE, children);
      break;

    case BITWUZLA_KIND_APPLY: {
      // TODO: checks
      // BZLA_ABORT(argc < 2,
      //           "invalid number of arguments for kind '%s', expected at least
      //           " "2, got %u", bzla_kind_to_str[kind], argc);
      term = nm.mk_node(node::Kind::APPLY, children);
    }
    break;

    case BITWUZLA_KIND_LAMBDA: {
      // TODO: checks
      // BZLA_ABORT(
      //    argc < 2,
      //    "invalid number of arguments for kind 'lambda', expected at least "
      //    "2, got %u",
      //    argc);
      term = mk_term_binder(node::Kind::LAMBDA, children);
    }
    break;

    case BITWUZLA_KIND_FORALL: {
      // TODO: checks
      // BZLA_ABORT(
      //    argc < 2,
      //    "invalid number of arguments for kind 'forall', expected at least "
      //    "2, got %u",
      //    argc);
      term = mk_term_binder(node::Kind::FORALL, children);
    }
    break;

    case BITWUZLA_KIND_EXISTS: {
      // TODO: checks
      // BZLA_ABORT(
      //    argc < 2,
      //    "invalid number of arguments for kind 'exists', expected at least "
      //    "2, got %u",
      //    argc);
      term = mk_term_binder(node::Kind::EXISTS, children);
    }
    break;

    default:
      BZLA_ABORT(true, "unexpected operator kind '%s'", bzla_kind_to_str[kind]);
  }
  assert(!term.is_null());
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg};
  const uint32_t idxs[]      = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 1, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg};
  const uint32_t idxs[]      = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 2, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  const uint32_t idxs[]      = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 1, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  const uint32_t idxs[]      = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 2, idxs);
}

const BitwuzlaTerm *
bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                         BitwuzlaKind kind,
                         uint32_t argc,
                         const BitwuzlaTerm *args[],
                         uint32_t idxc,
                         const uint32_t idxs[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  std::vector<Node> children;
  for (uint32_t i = 0; i < argc; i++)
  {
    children.push_back(args[i]->d_node);
  }

  NodeManager &nm = NodeManager::get();
  Node term;
  switch (kind)
  {
    case BITWUZLA_KIND_BV_EXTRACT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //     kind, bzla_args.data(), 1, argc, 2, idxc, 0, bzla_sort_is_bv,
      //     true);
      // BZLA_ABORT(idxs[0] > bzla_node_bv_get_width(bzla, bzla_args[0]),
      //            "upper index must be < bit-vector size of given term");
      // BZLA_ABORT(idxs[0] < idxs[1], "upper index must be >= lower index");
      term = nm.mk_node(node::Kind::BV_EXTRACT, children, {idxs[0], idxs[1]});
      break;

    case BITWUZLA_KIND_BV_ZERO_EXTEND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      // BZLA_ABORT(
      //    idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
      //    "extending term of bit-vector size %u with %u bits exceeds maximum "
      //    "bit-vector size of %u",
      //    bzla_node_bv_get_width(bzla, bzla_args[0]),
      //    idxs[0],
      //    UINT32_MAX);
      term = nm.mk_node(node::Kind::BV_ZERO_EXTEND, children, {idxs[0]});
      break;

    case BITWUZLA_KIND_BV_SIGN_EXTEND:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      // BZLA_ABORT(
      //    idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
      //    "extending term of bit-vector size %u with %u bits exceeds maximum "
      //    "bit-vector size of %u",
      //    bzla_node_bv_get_width(bzla, bzla_args[0]),
      //    idxs[0],
      //    UINT32_MAX);
      term = nm.mk_node(node::Kind::BV_SIGN_EXTEND, children, {idxs[0]});
      break;

    case BITWUZLA_KIND_BV_ROLI:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_ROLI, children, {idxs[0]});
      break;

    case BITWUZLA_KIND_BV_RORI:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      term = nm.mk_node(node::Kind::BV_RORI, children, {idxs[0]});
      break;

    case BITWUZLA_KIND_BV_REPEAT:
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      // BZLA_ABORT(((uint32_t) (UINT32_MAX / idxs[0]))
      //               < bzla_node_bv_get_width(bzla, bzla_args[0]),
      //           "resulting bit-vector size of 'repeat' exceeds maximum "
      //           "bit-vector size of %u",
      //           UINT32_MAX);
      term = nm.mk_node(node::Kind::BV_REPEAT, children, {idxs[0]});
      break;

    case BITWUZLA_KIND_FP_TO_SBV: {
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_TO_SBV, children, {idxs[0]});
    }
    break;

    case BITWUZLA_KIND_FP_TO_UBV: {
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(node::Kind::FP_TO_UBV, children, {idxs[0]});
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_BV: {
      // TODO: checks
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //    kind, bzla_args.data(), 1, argc, 2, idxc, 0, bzla_sort_is_bv, true);
      // BZLA_ABORT(idxs[0] <= 1, "expected exponent size > 1");
      // BZLA_ABORT(idxs[1] <= 1, "expected significand size > 1");
      // BZLA_ABORT(
      //    idxs[0] + idxs[1] != bzla_node_bv_get_width(bzla, bzla_args[0]),
      //    "size of bit-vector does not match given floating-point format");
      term = nm.mk_node(
          node::Kind::FP_TO_FP_FROM_BV, children, {idxs[0], idxs[1]});
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_FP: {
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //     kind, bzla_args.data(), 2, argc, 2, idxc, 1, bzla_sort_is_fp,
      //     true);
      // BZLA_ABORT(idxs[0] <= 1, "expected exponent size > 1");
      // BZLA_ABORT(idxs[1] <= 1, "expected significand size > 1");
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(
          node::Kind::FP_TO_FP_FROM_FP, children, {idxs[0], idxs[1]});
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_SBV: {
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //     kind, bzla_args.data(), 2, argc, 2, idxc, 1, bzla_sort_is_bv,
      //     true);
      // BZLA_ABORT(idxs[0] <= 1, "expected exponent size > 1");
      // BZLA_ABORT(idxs[1] <= 1, "expected significand size > 1");
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(
          node::Kind::FP_TO_FP_FROM_SBV, children, {idxs[0], idxs[1]});
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_UBV: {
      // BZLA_CHECK_MK_TERM_ARGS_IDXED(
      //     kind, bzla_args.data(), 2, argc, 2, idxc, 1, bzla_sort_is_bv,
      //     true);
      // BZLA_ABORT(idxs[0] <= 1, "expected exponent size > 1");
      // BZLA_ABORT(idxs[1] <= 1, "expected significand size > 1");
      // BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      term = nm.mk_node(
          node::Kind::FP_TO_FP_FROM_UBV, children, {idxs[0], idxs[1]});
    }
    break;
    default:
      BZLA_ABORT(true, "unexpected operator kind '%s'", bzla_kind_to_str[kind]);
  }
  assert(!term.is_null());
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_const(Bitwuzla *bitwuzla,
                  const BitwuzlaSort *sort,
                  const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Node term;
  if (symbol)
  {
    term = NodeManager::get().mk_const(sort->d_type, symbol);
  }
  else
  {
    term = NodeManager::get().mk_const(sort->d_type);
  }
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                        const BitwuzlaSort *sort,
                        const BitwuzlaTerm *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(value);

  // TODO: checks
  // BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_val);
  // BZLA_CHECK_TERM_NOT_IS_FUN(bzla_val);
  // BZLA_ABORT(bzla_node_get_sort_id(bzla_val)
  //               != bzla_sort_array_get_element(bzla, bzla_sort),
  //           "sort of 'value' does not match array element sort");
  Node term = NodeManager::get().mk_const_array(sort->d_type, value->d_node);
  return export_term(bitwuzla, term);
}

const BitwuzlaTerm *
bitwuzla_mk_var(Bitwuzla *bitwuzla,
                const BitwuzlaSort *sort,
                const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  // TODO: checks
  // BZLA_CHECK_SORT_NOT_IS_FUN(bzla, bzla_sort);

  Node term;
  if (symbol)
  {
    term = NodeManager::get().mk_var(sort->d_type, symbol);
  }
  else
  {
    term = NodeManager::get().mk_var(sort->d_type);
  }
  return export_term(bitwuzla, term);
}

void
bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO: check?
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);
  for (uint32_t i = 0; i < nlevels; i++)
  {
    bitwuzla->d_ctx.push();
  }
}

void
bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // TODO: check?
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);
  // BZLA_ABORT(
  //    nlevels > BZLA_COUNT_STACK(bzla->assertions_trail),
  //    "number of levels to pop (%u) greater than number of pushed levels
  //    (%u)", nlevels, BZLA_COUNT_STACK(bzla->assertions_trail));

  for (uint32_t i = 0; i < nlevels; i++)
  {
    bitwuzla->d_ctx.pop();
  }
}

void
bitwuzla_assert(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO: assumption handling?
  //  reset_assumptions(bitwuzla);

  // TODO: checks
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  // BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  // BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  bitwuzla->d_ctx.assert_formula(term->d_node);
}

void
bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO: assumption handling?
  // reset_assumptions(bitwuzla);

  // TODO: checks
  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  // BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  // BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  // bzla_assume_exp(bzla, bzla_term);
  // BZLA_PUSH_STACK(bitwuzla->d_assumptions, term);
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  // TODO: assumption handling?
  //  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  //  BZLA_CHECK_ARG_NOT_NULL(term);
  //
  //  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  //  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  //  BZLA_CHECK_UNSAT(bzla, "check for unsat assumptions");
  //
  //  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  //  assert(bzla_node_get_ext_refs(bzla_term));
  //  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  //  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  //  BZLA_ABORT(!bzla_is_assumption_exp(bzla, bzla_term),
  //             "'exp' must be an assumption");
  //  return bzla_failed_exp(bzla, bzla_term);
  return false;
}

const BitwuzlaTerm **
bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size)
{
  // TODO: assumption handling?
  // BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // BZLA_CHECK_ARG_NOT_NULL(size);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);
  // BZLA_CHECK_UNSAT(bzla, "get unsat assumptions");

  // BZLA_RESET_STACK(bitwuzla->d_unsat_assumptions);

  // for (size_t i = 0; i < BZLA_COUNT_STACK(bitwuzla->d_assumptions); i++)
  //{
  //   const BitwuzlaTerm *term  = BZLA_PEEK_STACK(bitwuzla->d_assumptions, i);
  //   BzlaNode *bzla_assumption = term->d_bzla_node;
  //   assert(bzla_is_assumption_exp(bzla, bzla_assumption));
  //   if (bzla_failed_exp(bzla, bzla_assumption))
  //   {
  //     BZLA_PUSH_STACK(bitwuzla->d_unsat_assumptions,
  //                     BZLA_EXPORT_BITWUZLA_TERM(bzla_assumption,
  //                     term->d_node));
  //   }
  // }
  //*size = BZLA_COUNT_STACK(bitwuzla->d_unsat_assumptions);
  // return bitwuzla->d_unsat_assumptions.start;
  (void) bitwuzla;
  (void) size;
  return nullptr;
}

const BitwuzlaTerm **
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size)
{
  // TODO: unsat cores
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(size);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla);
  // BZLA_CHECK_UNSAT(bzla, "get unsat core");

  // BZLA_RESET_STACK(bitwuzla->d_unsat_core);

  // for (uint32_t i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
  //{
  //   BzlaNode *cur = BZLA_PEEK_STACK(bzla->assertions, i);
  //   if (cur == NULL) continue;

  //  if (bzla_failed_exp(bzla, cur))
  //  {
  //    BZLA_PUSH_STACK(
  //        bitwuzla->d_unsat_core,
  //        BZLA_EXPORT_BITWUZLA_TERM(bzla_node_copy(bzla, cur),
  //                                  bitwuzla->d_assertions[i]->d_node));
  //    bzla_node_inc_ext_ref_counter(bzla, cur);
  //  }
  //}
  //*size = BZLA_COUNT_STACK(bitwuzla->d_unsat_core);
  // return bitwuzla->d_unsat_core.start;
  return nullptr;
}

void
bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla)
{
  // TODO: assumption handling?
  // BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);
  // bzla_fixate_assumptions(bzla);
}

void
bitwuzla_reset_assumptions(Bitwuzla *bitwuzla)
{
  // TODO: assumption handling
  // BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_INCREMENTAL(bzla);
  // bzla_reset_assumptions(bzla);
}

BitwuzlaResult
bitwuzla_simplify(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Result res = bitwuzla->d_ctx.preprocess();
  if (res == Result::SAT) return BITWUZLA_SAT;
  if (res == Result::UNSAT) return BITWUZLA_UNSAT;
  assert(res == Result::UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaResult
bitwuzla_check_sat(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Result res = bitwuzla->d_ctx.solve();
  if (res == Result::SAT) return BITWUZLA_SAT;
  if (res == Result::UNSAT) return BITWUZLA_UNSAT;
  assert(res == Result::UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

const BitwuzlaTerm *
bitwuzla_get_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO: checks
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");

  Node value = bitwuzla->d_ctx.get_value(term->d_node);
  return export_term(bitwuzla, value);
}

const char *
bitwuzla_get_bv_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");
  // BZLA_ABORT(bzla->quantifiers->count,
  //            "'get-value' is currently not supported with quantifiers");

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  // BZLA_ABORT(!bzla_node_is_bv(bzla, bzla_term),
  //            "given term is not a bit-vector term");

  // if (bitwuzla->d_bv_value)
  //{
  //   bzla_mem_freestr(bitwuzla->d_mm, bitwuzla->d_bv_value);
  // }
  // const BzlaBitVector *bv = bzla_model_get_bv(bzla, bzla_term);
  // bitwuzla->d_bv_value    = bzla_bv_to_char(bitwuzla->d_mm, bv);
  Node value = bitwuzla->d_ctx.get_value(term->d_node);
  assert(value.is_value());
  assert(value.type().is_bv());
  bitwuzla->d_bv_value = value.value<BitVector>().to_string();
  return bitwuzla->d_bv_value.c_str();
}

void
bitwuzla_get_fp_value(Bitwuzla *bitwuzla,
                      const BitwuzlaTerm *term,
                      const char **sign,
                      const char **exponent,
                      const char **significand)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(sign);
  BZLA_CHECK_ARG_NOT_NULL(exponent);
  BZLA_CHECK_ARG_NOT_NULL(significand);

  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");
  // BZLA_ABORT(bzla->quantifiers->count,
  //            "'get-value' is currently not supported with quantifiers");
  // BZLA_ABORT(!bzla_node_is_fp(bzla, bzla_term),
  //            "given term is not a floating-point term");

  Node value = bitwuzla->d_ctx.get_value(term->d_node);
  assert(value.is_value());
  assert(value.type().is_fp());
  BitVector fp_value = value.value<FloatingPoint>().as_bv();
  BitVector bv_sign, bv_exponent, bv_significand;
  FloatingPoint::ieee_bv_as_bvs(
      value.type(), fp_value, bv_sign, bv_exponent, bv_significand);
  bitwuzla->d_fp_value_sign        = bv_sign.to_string();
  bitwuzla->d_fp_value_exponent    = bv_exponent.to_string();
  bitwuzla->d_fp_value_significand = bv_significand.to_string();
  *sign                            = bitwuzla->d_fp_value_sign.c_str();
  *exponent                        = bitwuzla->d_fp_value_exponent.c_str();
  *significand                     = bitwuzla->d_fp_value_significand.c_str();
}

const char *
bitwuzla_get_rm_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO: checks
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");
  // BZLA_ABORT(!bzla_node_is_rm(bzla, bzla_term),
  //           "given term is not a rounding mode term");

  Node value = bitwuzla->d_ctx.get_value(term->d_node);
  assert(value.is_value());
  RoundingMode rm = value.value<RoundingMode>();

  if (rm == RoundingMode::RNA) return "RNA";
  if (rm == RoundingMode::RNE) return "RNE";
  if (rm == RoundingMode::RTN) return "RTN";
  if (rm == RoundingMode::RTP) return "RTP";
  assert(rm == RoundingMode::RTZ);
  return "RTZ";
}

void
bitwuzla_get_array_value(Bitwuzla *bitwuzla,
                         const BitwuzlaTerm *term,
                         const BitwuzlaTerm ***indices,
                         const BitwuzlaTerm ***values,
                         size_t *size,
                         const BitwuzlaTerm **default_value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(indices);
  BZLA_CHECK_ARG_NOT_NULL(values);
  BZLA_CHECK_ARG_NOT_NULL(size);
  BZLA_CHECK_ARG_NOT_NULL(default_value);

  // TODO:
  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");
  // BZLA_ABORT(bzla->quantifiers->count,
  //           "'get-value' is currently not supported with quantifiers");

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  // BZLA_ABORT(!bzla_node_is_array(bzla_term), "given term is not an array
  // term");

  // BzlaNodePtrStack _indices, _values;
  // BzlaNode *_default_value = 0, *index, *value;

  // BZLA_INIT_STACK(bitwuzla->d_mm, _indices);
  // BZLA_INIT_STACK(bitwuzla->d_mm, _values);
  // bzla_model_get_array_model(
  //     bzla, bzla_term, &_indices, &_values, &_default_value);
  // assert(BZLA_COUNT_STACK(_indices) == BZLA_COUNT_STACK(_values));

  //*indices       = 0;
  //*values        = 0;
  //*size          = 0;
  //*default_value = 0;

  // if (BZLA_EMPTY_STACK(_indices) && !_default_value)
  //{
  //   BZLA_RELEASE_STACK(_indices);
  //   BZLA_RELEASE_STACK(_values);
  //   return;
  // }

  // BZLA_RESET_STACK(bitwuzla->d_array_indices);
  // BZLA_RESET_STACK(bitwuzla->d_array_values);

  // for (size_t i = 0; i < BZLA_COUNT_STACK(_indices); ++i)
  //{
  //   index = BZLA_PEEK_STACK(_indices, i);
  //   value = BZLA_PEEK_STACK(_values, i);
  //   BZLA_PUSH_STACK(bitwuzla->d_array_indices,
  //                   BZLA_EXPORT_BITWUZLA_TERM(index, Node()));
  //   bzla_node_inc_ext_ref_counter(bzla, index);
  //   BZLA_PUSH_STACK(bitwuzla->d_array_values,
  //                   BZLA_EXPORT_BITWUZLA_TERM(value, Node()));
  //   bzla_node_inc_ext_ref_counter(bzla, value);
  // }

  //*size = BZLA_COUNT_STACK(_values);

  // if (*size)
  //{
  //   *indices = bitwuzla->d_array_indices.start;
  //   *values  = bitwuzla->d_array_values.start;
  // }

  // if (_default_value)
  //{
  //   *default_value = BZLA_EXPORT_BITWUZLA_TERM(_default_value, Node());
  //   bzla_node_inc_ext_ref_counter(bzla, _default_value);
  // }
  // BZLA_RELEASE_STACK(_indices);
  // BZLA_RELEASE_STACK(_values);
}

void
bitwuzla_get_fun_value(Bitwuzla *bitwuzla,
                       const BitwuzlaTerm *term,
                       const BitwuzlaTerm ****args,
                       size_t *arity,
                       const BitwuzlaTerm ***values,
                       size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(args);
  BZLA_CHECK_ARG_NOT_NULL(arity);
  BZLA_CHECK_ARG_NOT_NULL(values);
  BZLA_CHECK_ARG_NOT_NULL(size);

  // TODO:
  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "retrieve model");
  // BZLA_ABORT(bzla->quantifiers->count,
  //           "'get-value' is currently not supported with quantifiers");

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  // BZLA_ABORT(!bzla_sort_is_fun(bzla, bzla_node_get_sort_id(bzla_term)),
  //            "given term is not a function term");

  // uint32_t _arity = bzla_node_fun_get_arity(bzla, bzla_term);
  // BzlaNodePtrStack _args, _values;

  // BZLA_INIT_STACK(bitwuzla->d_mm, _args);
  // BZLA_INIT_STACK(bitwuzla->d_mm, _values);
  // bzla_model_get_fun_model(bzla, bzla_term, &_args, &_values);
  // assert(BZLA_COUNT_STACK(_values) * _arity == BZLA_COUNT_STACK(_args));

  //*args   = 0;
  //*arity  = 0;
  //*values = 0;
  //*size   = 0;

  // if (BZLA_EMPTY_STACK(_args))
  //{
  //   BZLA_RELEASE_STACK(_args);
  //   BZLA_RELEASE_STACK(_values);
  //   return;
  // }

  // BZLA_RESET_STACK(bitwuzla->d_fun_args_ptr);
  // BZLA_RESET_STACK(bitwuzla->d_fun_args);
  // BZLA_RESET_STACK(bitwuzla->d_fun_values);

  // BzlaNode *arg, *value;
  // for (size_t i = 0; i < BZLA_COUNT_STACK(_args); ++i)
  //{
  //   arg = BZLA_PEEK_STACK(_args, i);
  //   BZLA_PUSH_STACK(bitwuzla->d_fun_args,
  //                   BZLA_EXPORT_BITWUZLA_TERM(arg, Node()));
  //   bzla_node_inc_ext_ref_counter(bzla, arg);
  // }

  // for (size_t i = 0; i < BZLA_COUNT_STACK(_values); ++i)
  //{
  //   BZLA_PUSH_STACK(bitwuzla->d_fun_args_ptr,
  //                   bitwuzla->d_fun_args.start + i * _arity);
  //   value = BZLA_PEEK_STACK(_values, i);
  //   BZLA_PUSH_STACK(bitwuzla->d_fun_values,
  //                   BZLA_EXPORT_BITWUZLA_TERM(value, Node()));
  //   bzla_node_inc_ext_ref_counter(bzla, value);
  // }

  // assert(BZLA_COUNT_STACK(bitwuzla->d_fun_args_ptr)
  //        == BZLA_COUNT_STACK(bitwuzla->d_fun_values));

  //*arity  = _arity;
  //*args   = bitwuzla->d_fun_args_ptr.start;
  //*values = bitwuzla->d_fun_values.start;
  //*size   = BZLA_COUNT_STACK(_values);
  // BZLA_RELEASE_STACK(_args);
  // BZLA_RELEASE_STACK(_values);
}

void
bitwuzla_print_model(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);
  BZLA_ABORT(strcmp(format, "btor") && strcmp(format, "smt2"),
             "invalid model output format: %s",
             format);

  // TODO:
  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_ABORT(bzla->quantifiers->count,
  //           "model printing is currently not supported with quantifiers");
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "print model");
  // bzla_print_model(bzla, format, file);
}

void
bitwuzla_dump_formula(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  // TODO:
  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
  //           "dumping in incremental mode is currently not supported");
  // if (strcmp(format, "smt2") == 0)
  //{
  //  bzla_dumpsmt_dump(bzla, file);
  //}
  // else if (strcmp(format, "btor") == 0)
  //{
  //  bzla_dumpbtor_dump(bzla, file, 1);
  //}
  // else if (strcmp(format, "aiger_ascii") == 0)
  //{
  //  bzla_dumpaig_dump(bzla, false, file, true);
  //}
  // else if (strcmp(format, "aiger_binary") == 0)
  //{
  //  bzla_dumpaig_dump(bzla, true, file, true);
  //}
  // else
  //{
  //  BZLA_ABORT(true,
  //             "unknown format '%s', expected one of 'smt2', 'bzla', "
  //             "'aiger_ascii' or 'aiger_binary'",
  //             format);
  //}
}

BitwuzlaResult
bitwuzla_parse(Bitwuzla *bitwuzla,
               FILE *infile,
               const char *infile_name,
               FILE *outfile,
               char **error_msg,
               BitwuzlaResult *parsed_status,
               bool *parsed_smt2)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);
  BZLA_CHECK_ARG_NOT_NULL(parsed_smt2);

  int32_t bzla_res = bzla_parse(bitwuzla,
                                infile,
                                infile_name,
                                outfile,
                                error_msg,
                                parsed_status,
                                parsed_smt2);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaResult
bitwuzla_parse_format(Bitwuzla *bitwuzla,
                      const char *format,
                      FILE *infile,
                      const char *infile_name,
                      FILE *outfile,
                      char **error_msg,
                      BitwuzlaResult *parsed_status)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);

  int32_t bzla_res = 0;
  if (strcmp(format, "smt2") == 0)
  {
    bzla_res = bzla_parse_smt2(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_res = bzla_parse_btor(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor2") == 0)
  {
    bzla_res = bzla_parse_btor2(
        bitwuzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else
  {
    BZLA_ABORT(true,
               "unknown format '%s', expected one of 'smt2', 'bzla' or 'btor2'",
               format);
  }
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

const BitwuzlaTerm *
bitwuzla_substitute_term(Bitwuzla *bitwuzla,
                         const BitwuzlaTerm *term,
                         size_t map_size,
                         const BitwuzlaTerm *map_keys[],
                         const BitwuzlaTerm *map_values[])
{
  // TODO:
  // const BitwuzlaTerm *terms[1] = {term};
  // bitwuzla_substitute_terms(bitwuzla, 1, terms, map_size, map_keys,
  // map_values); return terms[0];
  return nullptr;
}

void
bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
                          size_t terms_size,
                          const BitwuzlaTerm *terms[],
                          size_t map_size,
                          const BitwuzlaTerm *map_keys[],
                          const BitwuzlaTerm *map_values[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(terms_size == 0, "no terms to substitute");
  BZLA_ABORT(map_size == 0, "empty substitution map");

  // TODO
  // BzlaNode *k, *v;
  // Bzla *bzla                 = BZLA_IMPORT_BITWUZLA(bitwuzla);
  // std::vector<BzlaNode *> bzla_map_keys, bzla_map_values;

  // BzlaNodePtrStack keys, values;
  // BZLA_INIT_STACK(bzla->mm, keys);
  // BZLA_INIT_STACK(bzla->mm, values);
  // for (size_t i = 0; i < map_size; ++i)
  //{
  //   bzla_map_keys.push_back(map_keys[i]->d_bzla_node);
  //   bzla_map_values.push_back(map_values[i]->d_bzla_node);
  //   k = bzla_map_keys[i];
  //   v = bzla_map_values[i];
  //   BZLA_ABORT(bzla_node_is_inverted(k)
  //                  || (!bzla_node_is_param(k) && !bzla_node_is_var(k)
  //                      && !bzla_node_is_uf(k)),
  //              "expected variable or constant as key at index %u",
  //              i);
  //   BZLA_PUSH_STACK(keys, k);
  //   BZLA_PUSH_STACK(values, bzla_simplify_exp(bzla, v));
  // }

  // BzlaNodePtrStack bzla_terms;
  // BZLA_INIT_STACK(bzla->mm, bzla_terms);
  // for (size_t i = 0; i < terms_size; ++i)
  //{
  //   BZLA_PUSH_STACK(
  //       bzla_terms,
  //       bzla_simplify_exp(bzla, BZLA_IMPORT_BITWUZLA_TERM(terms[i])));
  // }

  // bzla_substitute_terms(
  //     bzla, terms_size, bzla_terms.start, map_size, keys.start,
  //     values.start);
  // BZLA_RELEASE_STACK(keys);
  // BZLA_RELEASE_STACK(values);

  ///* Replace terms[i] with substitutions. */
  // for (size_t i = 0; i < terms_size; ++i)
  //{
  //   k        = BZLA_PEEK_STACK(bzla_terms, i);
  //   terms[i] = BZLA_EXPORT_BITWUZLA_TERM(k, Node());
  //   bzla_node_inc_ext_ref_counter(bzla, k);
  // }
  // BZLA_RELEASE_STACK(bzla_terms);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_sort_hash(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return std::hash<Type>{}(sort->d_type);
}

uint32_t
bitwuzla_sort_bv_get_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  return sort->d_type.bv_size();
}

uint32_t
bitwuzla_sort_fp_get_exp_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return sort->d_type.fp_exp_size();
}

uint32_t
bitwuzla_sort_fp_get_sig_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return sort->d_type.fp_sig_size();
}

const BitwuzlaSort *
bitwuzla_sort_array_get_index(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  return export_sort(sort->d_bzla, sort->d_type.array_index());
}

const BitwuzlaSort *
bitwuzla_sort_array_get_element(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  // TODO: check
  // BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  return export_sort(sort->d_bzla, sort->d_type.array_element());
}

const BitwuzlaSort **
bitwuzla_sort_fun_get_domain_sorts(const BitwuzlaSort *sort, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(size);

  // TODO: checks
  // BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  auto &sorts = sort->d_bzla->d_sorts;
  sorts.clear();
  for (const Type &type : sort->d_type.fun_types())
  {
    sorts.push_back(export_sort(sort->d_bzla, type));
  }
  *size = sorts.size();
  return sorts.data();
}

const BitwuzlaSort *
bitwuzla_sort_fun_get_codomain(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  // TODO: check
  // BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  return export_sort(sort->d_bzla, sort->d_type.fun_types().back());
}

uint32_t
bitwuzla_sort_fun_get_arity(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  // TODO: check
  // BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);
  return sort->d_type.fun_types().size() - 1;
}

bool
bitwuzla_sort_is_equal(const BitwuzlaSort *sort0, const BitwuzlaSort *sort1)
{
  BZLA_CHECK_ARG_NOT_NULL(sort0);
  BZLA_CHECK_ARG_NOT_NULL(sort1);
  return sort0->d_type == sort1->d_type;
}

bool
bitwuzla_sort_is_array(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_array();
}

bool
bitwuzla_sort_is_bool(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_bool();
}

bool
bitwuzla_sort_is_bv(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_bv();
}

bool
bitwuzla_sort_is_fp(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_fp();
}

bool
bitwuzla_sort_is_fun(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_fun();
}

bool
bitwuzla_sort_is_rm(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_type.is_rm();
}

void
bitwuzla_sort_dump(const BitwuzlaSort *sort, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  // TODO

  //  if (strcmp(format, "smt2") == 0)
  //  {
  //    bzla_dumpsmt_dump_sort(bzla_sort_get_by_id(bzla, bzla_sort), file);
  //  }
  //  else if (strcmp(format, "btor") == 0)
  //  {
  //    // Sorts are dumped when dumping terms.
  //  }
  //  else
  //  {
  //    BZLA_ABORT(
  //        true, "unknown format '%s', expected one of 'smt2' or 'bzla'",
  //        format);
  //  }
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_term_hash(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return std::hash<Node>{}(term->d_node);
}

BitwuzlaKind
bitwuzla_term_get_kind(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  // TODO: check no null d_node
  return s_kind_internal_to_external.at(term->d_node.kind());
}

const BitwuzlaTerm **
bitwuzla_term_get_children(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  auto &children = term->d_bzla->d_term_children;
  children.clear();
  for (const Node &child : term->d_node)
  {
    children.push_back(export_term(term->d_bzla, child));
  }
  return children.data();
}

uint32_t *
bitwuzla_term_get_indices(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO: check
  // BZLA_ABORT(!bzla_node_is_indexed(bzla_term),
  //           "cannot get indices of non-indexed term");

  auto &indices = term->d_bzla->d_term_indices;
  indices.clear();
  for (auto index : term->d_node.indices())
  {
    indices.push_back(index);
  }
  return indices.data();
}

bool
bitwuzla_term_is_indexed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.num_indices() > 0;
}

Bitwuzla *
bitwuzla_term_get_bitwuzla(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_bzla;
}

const BitwuzlaSort *
bitwuzla_term_get_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return export_sort(term->d_bzla, term->d_node.type());
}

const BitwuzlaSort *
bitwuzla_term_array_get_index_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return export_sort(term->d_bzla, term->d_node.type().array_index());
}

const BitwuzlaSort *
bitwuzla_term_array_get_element_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return export_sort(term->d_bzla, term->d_node.type().array_element());
}

const BitwuzlaSort **
bitwuzla_term_fun_get_domain_sorts(const BitwuzlaTerm *term, size_t *size)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(size);

  auto &sorts = term->d_bzla->d_sorts;
  sorts.clear();
  for (const Type &type : term->d_node.type().fun_types())
  {
    sorts.push_back(export_sort(term->d_bzla, type));
  }
  *size = sorts.size();
  return sorts.data();
}

const BitwuzlaSort *
bitwuzla_term_fun_get_codomain_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return export_sort(term->d_bzla, term->d_node.type().fun_types().back());
}

uint32_t
bitwuzla_term_bv_get_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  // TODO: check
  // BZLA_CHECK_TERM_IS_BV(bzla, bzla_term);
  return term->d_node.type().bv_size();
}

uint32_t
bitwuzla_term_fp_get_exp_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  // TODO: check
  // BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return term->d_node.type().fp_exp_size();
}

uint32_t
bitwuzla_term_fp_get_sig_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  // TODO: check
  // BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return term->d_node.type().fp_sig_size();
}

uint32_t
bitwuzla_term_fun_get_arity(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  // TODO: check
  // BZLA_CHECK_TERM_IS_FUN(bzla_term);
  return term->d_node.type().fun_types().size() - 1;
}

const char *
bitwuzla_term_get_symbol(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  auto symbol = term->d_node.symbol();
  if (symbol)
  {
    return (*symbol).get().c_str();
  }
  return nullptr;
}

void
bitwuzla_term_set_symbol(const BitwuzlaTerm *term, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(symbol);

  // TODO: do we still want to support this?
}

bool
bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
                            const BitwuzlaTerm *term1)
{
  BZLA_CHECK_ARG_NOT_NULL(term0);
  BZLA_CHECK_ARG_NOT_NULL(term1);
  return term0->d_node.type() == term1->d_node.type();
}

bool
bitwuzla_term_is_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_array();
}

bool
bitwuzla_term_is_const(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.kind() == node::Kind::CONSTANT;
}

bool
bitwuzla_term_is_fun(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_fun();
}

bool
bitwuzla_term_is_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.kind() == node::Kind::VARIABLE;
}

bool
bitwuzla_term_is_bound_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  // TODO
  return true;
}

bool
bitwuzla_term_is_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.is_value();
}

bool
bitwuzla_term_is_bv_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.is_value() && term->d_node.type().is_bv();
}

bool
bitwuzla_term_is_fp_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.is_value() && term->d_node.type().is_fp();
}

bool
bitwuzla_term_is_rm_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.is_value() && term->d_node.type().is_rm();
}

bool
bitwuzla_term_is_bool(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_bool();
}

bool
bitwuzla_term_is_bv(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_bv();
}

bool
bitwuzla_term_is_fp(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_fp();
}

bool
bitwuzla_term_is_rm(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.type().is_rm();
}

bool
bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_bv_value(term))
  {
    return term->d_node.value<BitVector>().is_zero();
  }
  return false;
}

bool
bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_bv_value(term))
  {
    return term->d_node.value<BitVector>().is_one();
  }
  return false;
}

bool
bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_bv_value(term))
  {
    return term->d_node.value<BitVector>().is_ones();
  }
  return false;
}

bool
bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_bv_value(term))
  {
    return term->d_node.value<BitVector>().is_min_signed();
  }
  return false;
}

bool
bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_bv_value(term))
  {
    return term->d_node.value<BitVector>().is_max_signed();
  }
  return false;
}

bool
bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_fp_value(term))
  {
    const FloatingPoint &value = term->d_node.value<FloatingPoint>();
    return value.fpiszero() && value.fpispos();
  }
  return false;
}

bool
bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_fp_value(term))
  {
    const FloatingPoint &value = term->d_node.value<FloatingPoint>();
    return value.fpiszero() && value.fpisneg();
  }
  return false;
}

bool
bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_fp_value(term))
  {
    const FloatingPoint &value = term->d_node.value<FloatingPoint>();
    return value.fpisinf() && value.fpispos();
  }
  return false;
}

bool
bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_fp_value(term))
  {
    const FloatingPoint &value = term->d_node.value<FloatingPoint>();
    return value.fpisinf() && value.fpisneg();
  }
  return false;
}

bool
bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_fp_value(term))
  {
    return term->d_node.value<FloatingPoint>().fpisnan();
  }
  return false;
}

bool
bitwuzla_term_is_rm_value_rna(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_rm_value(term))
  {
    return term->d_node.value<RoundingMode>() == RoundingMode::RNA;
  }
  return false;
}

bool
bitwuzla_term_is_rm_value_rne(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_rm_value(term))
  {
    return term->d_node.value<RoundingMode>() == RoundingMode::RNE;
  }
  return false;
}

bool
bitwuzla_term_is_rm_value_rtn(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_rm_value(term))
  {
    return term->d_node.value<RoundingMode>() == RoundingMode::RTN;
  }
  return false;
}

bool
bitwuzla_term_is_rm_value_rtp(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_rm_value(term))
  {
    return term->d_node.value<RoundingMode>() == RoundingMode::RTP;
  }
  return false;
}

bool
bitwuzla_term_is_rm_value_rtz(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  if (bitwuzla_term_is_rm_value(term))
  {
    return term->d_node.value<RoundingMode>() == RoundingMode::RTZ;
  }
  return false;
}

bool
bitwuzla_term_is_const_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  return term->d_node.kind() == node::Kind::CONST_ARRAY;
}

void
bitwuzla_term_dump(const BitwuzlaTerm *term, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  // TODO:
}

extern "C" {

/* main only ---------------------------------------------------------------- */

Bzla *
bitwuzla_get_bzla(Bitwuzla *bitwuzla)
{
  return bitwuzla->d_bzla_dummy;
}

/* parser only -------------------------------------------------------------- */

BzlaMsg *
bitwuzla_get_bzla_msg(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bitwuzla->d_bzla_dummy->msg;
}

/* smt2 parser only --------------------------------------------------------- */

void
bitwuzla_term_var_mark_bool(const BitwuzlaTerm *term)
{
  // not needed anymore
  // BZLA_CHECK_ARG_NOT_NULL(term);

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // Bzla *bzla = bzla_node_get_bzla(bzla_term);
  // BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);

  // BzlaPtrHashBucket *b = bzla_hashptr_table_get(bzla->inputs, bzla_term);
  // assert(b);
  // b->data.flag = true;
}

void
bitwuzla_term_print_value_smt2(const BitwuzlaTerm *term,
                               char *symbol,
                               FILE *file)
{
  // TODO:
  // BZLA_CHECK_ARG_NOT_NULL(term);

  // BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  // assert(bzla_node_get_ext_refs(bzla_term));
  // Bzla *bzla = bzla_node_get_bzla(bzla_term);
  // BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  // BZLA_CHECK_SAT(bzla, "print model value");
  // BZLA_ABORT(bzla->quantifiers->count,
  //            "'get-value' is currently not supported with quantifiers");
  // bzla_print_value_smt2(bzla, bzla_term, symbol, file);
}

BitwuzlaOption
bitwuzla_get_option_from_string(Bitwuzla *bitwuzla, const char *str)
{
  // TODO
  // BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(str);

  // Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);

  // if (!bzla_hashptr_table_get(bzla->str2opt, str))
  //{
  //   return BITWUZLA_OPT_NUM_OPTS;
  // }
  // return BZLA_EXPORT_BITWUZLA_OPTION(static_cast<BzlaOption>(
  //     bzla_hashptr_table_get(bzla->str2opt, str)->data.as_int));
  return BITWUZLA_OPT_SEED;
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_set_bzla_id(Bitwuzla *bitwuzla, const BitwuzlaTerm *term, int32_t id)
{
  // should not be needed
#if 0
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BZLA_ABORT(
      !bzla_node_is_bv_var(bzla_term) && !bzla_node_is_uf_array(bzla_term),
      "expected bit-vector/array variable or UF");
  bzla_node_set_bzla_id(bzla, bzla_term, id);
#endif
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_add_output(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  // TODO:
#if 0
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BZLA_PUSH_STACK(bzla->outputs, bzla_node_copy(bzla, bzla_term));
#endif
}
}
