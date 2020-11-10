/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  This file is part of Bitwuzla.
 *
 *  See COPYING for more information on using this software.
 */

#include "bitwuzla.h"

#include "bzlaconfig.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaparse.h"
#include "bzlaprintmodel.h"
#include "dumper/bzladumpaig.h"
#include "dumper/bzladumpbtor.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlaabort.h"
#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */

BZLA_DECLARE_STACK(BitwuzlaTermPtr, BitwuzlaTerm *);
BZLA_DECLARE_STACK(BitwuzlaTermConstPtr, const BitwuzlaTerm *);
BZLA_DECLARE_STACK(BitwuzlaSortPtr, BitwuzlaSort *);

/* -------------------------------------------------------------------------- */

struct Bitwuzla
{
  /* Non-simplified assumptions as assumed via bitwuzla_assume. */
  BitwuzlaTermConstPtrStack d_assumptions;
  /* Unsat assumptions of current bitwuzla_get_unsat_assumptions query. */
  BitwuzlaTermPtrStack d_unsat_assumptions;
  /* Unsat core of the current bitwuzla_get_unsat_core query. */
  BitwuzlaTermPtrStack d_unsat_core;
  /* Domain sorts of current bitwuzla_term_fun_get_domain_sorts query. */
  BitwuzlaSortPtrStack d_fun_domain_sorts;
  /* Domain sorts of current bitwuzla_sort_fun_get_domain_sorts query. */
  BitwuzlaSortPtrStack d_sort_fun_domain_sorts;
  /* Map internal sort id to external sort wrapper. */
  BzlaIntHashTable *d_sort_map;
  /* Internal solver. */
  Bzla *d_bzla;
  /* API memory manager. */
  BzlaMemMgr *d_mm;
};

struct BitwuzlaSort
{
  /* Internal sort. */
  BzlaSortId d_bzla_sort;
  /* Associated solver. */
  Bitwuzla *d_bzla;
};

static BzlaOption bzla_options[BITWUZLA_OPT_NUM_OPTS] = {
    BZLA_OPT_INCREMENTAL,
    BZLA_OPT_MODEL_GEN,
    BZLA_OPT_INPUT_FORMAT,
    BZLA_OPT_OUTPUT_NUMBER_FORMAT,
    BZLA_OPT_OUTPUT_FORMAT,
    BZLA_OPT_ENGINE,
    BZLA_OPT_SAT_ENGINE,
    BZLA_OPT_PRETTY_PRINT,
    BZLA_OPT_EXIT_CODES,
    BZLA_OPT_SEED,
    BZLA_OPT_VERBOSITY,
    BZLA_OPT_LOGLEVEL,
    BZLA_OPT_REWRITE_LEVEL,
    BZLA_OPT_SKELETON_PREPROC,
    BZLA_OPT_ACKERMANN,
    BZLA_OPT_BETA_REDUCE,
    BZLA_OPT_ELIMINATE_ITES,
    BZLA_OPT_ELIMINATE_SLICES,
    BZLA_OPT_VAR_SUBST,
    BZLA_OPT_UCOPT,
    BZLA_OPT_MERGE_LAMBDAS,
    BZLA_OPT_EXTRACT_LAMBDAS,
    BZLA_OPT_NORMALIZE,
    BZLA_OPT_NORMALIZE_ADD,
    BZLA_OPT_FUN_PREPROP,
    BZLA_OPT_FUN_PRESLS,
    BZLA_OPT_FUN_DUAL_PROP,
    BZLA_OPT_FUN_DUAL_PROP_QSORT,
    BZLA_OPT_FUN_JUST,
    BZLA_OPT_FUN_JUST_HEURISTIC,
    BZLA_OPT_FUN_LAZY_SYNTHESIZE,
    BZLA_OPT_FUN_EAGER_LEMMAS,
    BZLA_OPT_FUN_STORE_LAMBDAS,
    BZLA_OPT_PRINT_DIMACS,
    BZLA_OPT_SLS_NFLIPS,
    BZLA_OPT_SLS_STRATEGY,
    BZLA_OPT_SLS_JUST,
    BZLA_OPT_SLS_MOVE_GW,
    BZLA_OPT_SLS_MOVE_RANGE,
    BZLA_OPT_SLS_MOVE_SEGMENT,
    BZLA_OPT_SLS_MOVE_RAND_WALK,
    BZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
    BZLA_OPT_SLS_MOVE_RAND_ALL,
    BZLA_OPT_SLS_MOVE_RAND_RANGE,
    BZLA_OPT_SLS_MOVE_PROP,
    BZLA_OPT_SLS_MOVE_PROP_N_PROP,
    BZLA_OPT_SLS_MOVE_PROP_N_SLS,
    BZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
    BZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
    BZLA_OPT_SLS_USE_RESTARTS,
    BZLA_OPT_SLS_USE_BANDIT,
    BZLA_OPT_PROP_NPROPS,
    BZLA_OPT_PROP_NUPDATES,
    BZLA_OPT_PROP_ENTAILED,
    BZLA_OPT_PROP_CONST_BITS,
    BZLA_OPT_PROP_CONST_DOMAINS,
    BZLA_OPT_PROP_USE_RESTARTS,
    BZLA_OPT_PROP_USE_BANDIT,
    BZLA_OPT_PROP_PATH_SEL,
    BZLA_OPT_PROP_PROB_USE_INV_VALUE,
    BZLA_OPT_PROP_PROB_FLIP_COND,
    BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
    BZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
    BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
    BZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
    BZLA_OPT_PROP_PROB_CONC_FLIP,
    BZLA_OPT_PROP_PROB_SLICE_FLIP,
    BZLA_OPT_PROP_PROB_EQ_FLIP,
    BZLA_OPT_PROP_PROB_AND_FLIP,
    BZLA_OPT_PROP_PROB_RANDOM_INPUT,
    BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
    BZLA_OPT_PROP_SKIP_NO_PROGRESS,
    BZLA_OPT_PROP_USE_INV_LT_CONCAT,
    BZLA_OPT_PROP_INFER_INEQ_BOUNDS,
    BZLA_OPT_PROP_SEXT,
    BZLA_OPT_PROP_XOR,
    BZLA_OPT_PROP_SRA,
    BZLA_OPT_AIGPROP_USE_RESTARTS,
    BZLA_OPT_AIGPROP_USE_BANDIT,
    BZLA_OPT_AIGPROP_NPROPS,
    BZLA_OPT_QUANT_SYNTH,
    BZLA_OPT_QUANT_DUAL_SOLVER,
    BZLA_OPT_QUANT_SYNTH_LIMIT,
    BZLA_OPT_QUANT_SYNTH_QI,
    BZLA_OPT_QUANT_DER,
    BZLA_OPT_QUANT_CER,
    BZLA_OPT_QUANT_MINISCOPE,
    /* internal options --------------------------------------------------- */
    BZLA_OPT_SORT_EXP,
    BZLA_OPT_SORT_AIG,
    BZLA_OPT_SORT_AIGVEC,
    BZLA_OPT_SIMPLIFY_CONSTRAINTS,
    BZLA_OPT_CHK_FAILED_ASSUMPTIONS,
    BZLA_OPT_CHK_MODEL,
    BZLA_OPT_CHK_UNCONSTRAINED,
    BZLA_OPT_LS_SHARE_SAT,
    BZLA_OPT_PARSE_INTERACTIVE,
    BZLA_OPT_SAT_ENGINE_LGL_FORK,
    BZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
    BZLA_OPT_SAT_ENGINE_N_THREADS,
    BZLA_OPT_SLT_ELIM,
    BZLA_OPT_SIMP_NORMAMLIZE_ADDERS,
    BZLA_OPT_DECLSORT_BV_WIDTH,
    BZLA_OPT_QUANT_SYNTH_ITE_COMPLETE,
    BZLA_OPT_QUANT_FIXSYNTH,
    BZLA_OPT_RW_ZERO_LOWER_SLICE,
    BZLA_OPT_NONDESTR_SUBST,
    BZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
    BZLA_OPT_UNSAT_CORES,
    BZLA_OPT_SMT_COMP_MODE,
};

static BitwuzlaOption bitwuzla_options[BZLA_OPT_NUM_OPTS] = {
    BITWUZLA_OPT_PRODUCE_MODELS,
    BITWUZLA_OPT_INCREMENTAL,
    BITWUZLA_OPT_INPUT_FORMAT,
    BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT,
    BITWUZLA_OPT_OUTPUT_FORMAT,
    BITWUZLA_OPT_ENGINE,
    BITWUZLA_OPT_SAT_ENGINE,
    BITWUZLA_OPT_NUM_OPTS,
    BITWUZLA_OPT_PRETTY_PRINT,
    BITWUZLA_OPT_EXIT_CODES,
    BITWUZLA_OPT_SEED,
    BITWUZLA_OPT_VERBOSITY,
    BITWUZLA_OPT_LOGLEVEL,
    BITWUZLA_OPT_REWRITE_LEVEL,
    BITWUZLA_OPT_SKELETON_PREPROC,
    BITWUZLA_OPT_ACKERMANN,
    BITWUZLA_OPT_BETA_REDUCE,
    BITWUZLA_OPT_ELIMINATE_ITES,
    BITWUZLA_OPT_ELIMINATE_SLICES,
    BITWUZLA_OPT_VAR_SUBST,
    BITWUZLA_OPT_UCOPT,
    BITWUZLA_OPT_MERGE_LAMBDAS,
    BITWUZLA_OPT_EXTRACT_LAMBDAS,
    BITWUZLA_OPT_NORMALIZE,
    BITWUZLA_OPT_NORMALIZE_ADD,
    BITWUZLA_OPT_FUN_PREPROP,
    BITWUZLA_OPT_FUN_PRESLS,
    BITWUZLA_OPT_FUN_DUAL_PROP,
    BITWUZLA_OPT_FUN_DUAL_PROP_QSORT,
    BITWUZLA_OPT_FUN_JUST,
    BITWUZLA_OPT_FUN_JUST_HEURISTIC,
    BITWUZLA_OPT_FUN_LAZY_SYNTHESIZE,
    BITWUZLA_OPT_FUN_EAGER_LEMMAS,
    BITWUZLA_OPT_FUN_STORE_LAMBDAS,
    BITWUZLA_OPT_PRINT_DIMACS,
    BITWUZLA_OPT_SLS_NFLIPS,
    BITWUZLA_OPT_SLS_STRATEGY,
    BITWUZLA_OPT_SLS_JUST,
    BITWUZLA_OPT_SLS_MOVE_GW,
    BITWUZLA_OPT_SLS_MOVE_RANGE,
    BITWUZLA_OPT_SLS_MOVE_SEGMENT,
    BITWUZLA_OPT_SLS_MOVE_RAND_WALK,
    BITWUZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
    BITWUZLA_OPT_SLS_MOVE_RAND_ALL,
    BITWUZLA_OPT_SLS_MOVE_RAND_RANGE,
    BITWUZLA_OPT_SLS_MOVE_PROP,
    BITWUZLA_OPT_SLS_MOVE_PROP_N_PROP,
    BITWUZLA_OPT_SLS_MOVE_PROP_N_SLS,
    BITWUZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
    BITWUZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
    BITWUZLA_OPT_SLS_USE_RESTARTS,
    BITWUZLA_OPT_SLS_USE_BANDIT,
    BITWUZLA_OPT_PROP_NPROPS,
    BITWUZLA_OPT_PROP_NUPDATES,
    BITWUZLA_OPT_PROP_ENTAILED,
    BITWUZLA_OPT_PROP_CONST_BITS,
    BITWUZLA_OPT_PROP_CONST_DOMAINS,
    BITWUZLA_OPT_PROP_USE_RESTARTS,
    BITWUZLA_OPT_PROP_USE_BANDIT,
    BITWUZLA_OPT_PROP_PATH_SEL,
    BITWUZLA_OPT_PROP_PROB_USE_INV_VALUE,
    BITWUZLA_OPT_PROP_PROB_FLIP_COND,
    BITWUZLA_OPT_PROP_PROB_FLIP_COND_CONST,
    BITWUZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
    BITWUZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
    BITWUZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
    BITWUZLA_OPT_PROP_PROB_CONC_FLIP,
    BITWUZLA_OPT_PROP_PROB_SLICE_FLIP,
    BITWUZLA_OPT_PROP_PROB_EQ_FLIP,
    BITWUZLA_OPT_PROP_PROB_AND_FLIP,
    BITWUZLA_OPT_PROP_PROB_RANDOM_INPUT,
    BITWUZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
    BITWUZLA_OPT_PROP_SKIP_NO_PROGRESS,
    BITWUZLA_OPT_PROP_USE_INV_LT_CONCAT,
    BITWUZLA_OPT_PROP_INFER_INEQ_BOUNDS,
    BITWUZLA_OPT_PROP_SEXT,
    BITWUZLA_OPT_PROP_XOR,
    BITWUZLA_OPT_PROP_SRA,
    BITWUZLA_OPT_AIGPROP_USE_RESTARTS,
    BITWUZLA_OPT_AIGPROP_USE_BANDIT,
    BITWUZLA_OPT_AIGPROP_NPROPS,
    BITWUZLA_OPT_QUANT_SYNTH,
    BITWUZLA_OPT_QUANT_DUAL_SOLVER,
    BITWUZLA_OPT_QUANT_SYNTH_LIMIT,
    BITWUZLA_OPT_QUANT_SYNTH_QI,
    BITWUZLA_OPT_QUANT_DER,
    BITWUZLA_OPT_QUANT_CER,
    BITWUZLA_OPT_QUANT_MINISCOPE,
    BITWUZLA_OPT_SORT_EXP,
    BITWUZLA_OPT_SORT_AIG,
    BITWUZLA_OPT_SORT_AIGVEC,
    BITWUZLA_OPT_NUM_OPTS,
    BITWUZLA_OPT_SIMPLIFY_CONSTRAINTS,
    BITWUZLA_OPT_CHECK_UNSAT_ASSUMPTIONS,
    BITWUZLA_OPT_CHECK_MODEL,
    BITWUZLA_OPT_CHECK_UNCONSTRAINED,
    BITWUZLA_OPT_LS_SHARE_SAT,
    BITWUZLA_OPT_PARSE_INTERACTIVE,
    BITWUZLA_OPT_SAT_ENGINE_LGL_FORK,
    BITWUZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
    BITWUZLA_OPT_SAT_ENGINE_N_THREADS,
    BITWUZLA_OPT_SLT_ELIM,
    BITWUZLA_OPT_SIMP_NORMAMLIZE_ADDERS,
    BITWUZLA_OPT_DECLSORT_BV_WIDTH,
    BITWUZLA_OPT_QUANT_SYNTH_ITE_COMPLETE,
    BITWUZLA_OPT_QUANT_FIXSYNTH,
    BITWUZLA_OPT_RW_ZERO_LOWER_SLICE,
    BITWUZLA_OPT_NONDESTR_SUBST,
    BITWUZLA_OPT_PROP_PROB_FALLBACK_RANDOM_VALUE,
    BITWUZLA_OPT_PRODUCE_UNSAT_CORES,
    BITWUZLA_OPT_SMT_COMP_MODE,
};

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA(bitwuzla) (bitwuzla->d_bzla)
#define BZLA_EXPORT_BITWUZLA(bzla) ((Bitwuzla *) (bzla)->bitwuzla)

#define BZLA_IMPORT_BITWUZLA_TERM(term) (((BzlaNode *) (term)))
#define BZLA_IMPORT_BITWUZLA_TERMS(terms) (((BzlaNode **) (terms)))
#define BZLA_EXPORT_BITWUZLA_TERM(node) (((BitwuzlaTerm *) (node)))
#define BZLA_EXPORT_BITWUZLA_TERMS(terms) (((const BitwuzlaTerm **) (terms)))

#define BZLA_IMPORT_BITWUZLA_SORT(sort) ((sort)->d_bzla_sort)
#define BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, sort) wrap_sort(bitwuzla, sort)

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options[option])
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (bitwuzla_options[option])

#define BZLA_IMPORT_BITWUZLA_RM(rm)                                \
  (rm == BITWUZLA_RM_RNA                                           \
       ? BZLA_RM_RNA                                               \
       : (rm == BITWUZLA_RM_RNE                                    \
              ? BZLA_RM_RNE                                        \
              : (rm == BITWUZLA_RM_RTN                             \
                     ? BZLA_RM_RTN                                 \
                     : (rm == BITWUZLA_RM_RTP                      \
                            ? BZLA_RM_RTP                          \
                            : (rm == BITWUZLA_RM_RTZ ? BZLA_RM_RTZ \
                                                     : BZLA_RM_MAX)))))

#define BZLA_EXPORT_BITWUZLA_RM(rm)                                \
  (rm == BZLA_RM_RNA                                               \
       ? BITWUZLA_RM_RNA                                           \
       : (rm == BZLA_RM_RNE                                        \
              ? BITWUZLA_RM_RNE                                    \
              : (rm == BZLA_RM_RTN                                 \
                     ? BITWUZLA_RM_RTN                             \
                     : (rm == BZLA_RM_RTP                          \
                            ? BITWUZLA_RM_RTP                      \
                            : (rm == BZLA_RM_RTZ ? BITWUZLA_RM_RTZ \
                                                 : BITWUZLA_RM_MAX)))))

/* -------------------------------------------------------------------------- */

#define BZLA_CHECK_OPT_INCREMENTAL(bzla)                \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL), \
             "incremental usage not enabled");

#define BZLA_CHECK_OPT_PRODUCE_MODELS(bzla)           \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN), \
             "model production not enabled");

#define BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla)        \
  BZLA_ABORT(!bzla_opt_get(bzla, BZLA_OPT_UNSAT_CORES), \
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
      kind,                                                                    \
      expected,                                                                \
      argc)

#define BZLA_CHECK_IDX_CNT(kind, expected, argc)                             \
  BZLA_ABORT(                                                                \
      (argc) != (expected),                                                  \
      "invalid number of indices for kind '%s', expected '%u' and got '%u'", \
      kind,                                                                  \
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

#define BZLA_CHECK_TERM_IS_VAR(term)                                          \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_param(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected variable term")

#define BZLA_CHECK_TERM_IS_VAR_AT_IDX(term, idx)                              \
  BZLA_ABORT(                                                                 \
      !bzla_node_is_param(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "expected variable term at index %u",                                   \
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

#define BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(term, idx)                       \
  BZLA_ABORT(                                                             \
      bzla_node_is_uf(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "unexpected function term at index %u",                             \
      (idx))

#define BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(term, idx) \
  BZLA_ABORT(bzla_node_param_is_bound(term),               \
             "expected unbound variable term at index %u", \
             (idx))

/* -------------------------------------------------------------------------- */

/** Increment external reference counter. */
static void
inc_ext_refs_sort(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  assert(id);
  BzlaSort *sort = bzla_sort_get_by_id(bzla, id);
  BZLA_ABORT(sort->ext_refs == INT32_MAX, "sort reference counter overflow");
  sort->ext_refs += 1;
  bzla->external_refs += 1;
}

/** Return start address of (original) symbol without prefix.  */
static const char *
remove_unique_symbol_prefix(Bzla *bzla, const char *symbol)
{
  if (symbol)
  {
    size_t len    = strlen(symbol);
    size_t offset = 5 + bzla_util_num_digits(bzla->num_push_pop);
    if (len > offset && !strncmp(symbol, "BZLA_", 5) && symbol[offset] == '@')
    {
      return symbol + offset + 1;
    }
  }
  return symbol;
}

/**
 * Create symbol that is unique in the current context.
 * For this, symbols are prefixed with BZLA_<num_push_pop>@<symbol>.
 */
static char *
mk_unique_symbol(Bzla *bzla, const char *symbol)
{
  char *res;
  size_t len;
  if (bzla->num_push_pop)
  {
    len = strlen(symbol) + 1;
    len += strlen("BZLA_@");
    len += bzla_util_num_digits(bzla->num_push_pop);
    BZLA_CNEWN(bzla->mm, res, len);
    sprintf(res, "BZLA_%u@%s", bzla->num_push_pop, symbol);
  }
  else
  {
    res = bzla_mem_strdup(bzla->mm, symbol);
  }
  assert(!symbol || !strcmp(symbol, remove_unique_symbol_prefix(bzla, res)));
  return res;
}

/** Dummy helper for sort argument check for mk_term. */
static bool
sort_any(Bzla *bzla, BzlaSortId node)
{
  (void) bzla;
  (void) node;
  return true;
}

/** Return true given variable terms are distinct. */
static bool
vars_distinct(Bzla *bzla, BzlaNode *vars[], uint32_t paramc)
{
  bool res                = true;
  BzlaIntHashTable *cache = bzla_hashint_table_new(bzla->mm);
  for (uint32_t i = 0; i < paramc; i++)
  {
    if (bzla_hashint_table_contains(cache, bzla_node_get_id(vars[i])))
    {
      res = false;
      break;
    }
    bzla_hashint_table_add(cache, bzla_node_get_id(vars[i]));
  }
  bzla_hashint_table_delete(cache);
  return res;
}

static BzlaNode *
mk_term_left_assoc(Bzla *bzla,
                   BzlaNode *args[],
                   uint32_t argc,
                   BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp;

  res = fun(bzla, args[0], args[1]);
  for (uint32_t i = 2; i < argc; i++)
  {
    tmp = fun(bzla, res, args[i]);
    bzla_node_release(bzla, res);
    res = tmp;
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_right_assoc(Bzla *bzla,
                    BzlaNode *args[],
                    uint32_t argc,
                    BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp;
  res = bzla_node_copy(bzla, args[argc - 1]);
  for (uint32_t i = 1; i < argc; ++i)
  {
    tmp = fun(bzla, args[argc - i - 1], res);
    bzla_node_release(bzla, res);
    res = tmp;
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_pairwise(Bzla *bzla,
                 BzlaNode *args[],
                 uint32_t argc,
                 BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0; i < argc - 1; i++)
  {
    for (uint32_t j = i + 1; j < argc; j++)
    {
      tmp = fun(bzla, args[i], args[j]);
      if (res)
      {
        old = res;
        res = bzla_exp_bv_and(bzla, old, tmp);
        bzla_node_release(bzla, old);
        bzla_node_release(bzla, tmp);
      }
      else
      {
        res = tmp;
      }
    }
  }
  assert(res);
  return res;
}

static BzlaNode *
mk_term_chained(Bzla *bzla,
                BzlaNode *args[],
                uint32_t argc,
                BzlaNode *(*fun)(Bzla *, BzlaNode *, BzlaNode *) )
{
  assert(argc >= 2);
  BzlaNode *res, *tmp, *old;

  res = 0;
  for (uint32_t i = 0, j = 1; j < argc; i++, j++)
  {
    tmp = fun(bzla, args[i], args[j]);
    if (res)
    {
      old = res;
      res = bzla_exp_bv_and(bzla, old, tmp);
      bzla_node_release(bzla, old);
      bzla_node_release(bzla, tmp);
    }
    else
    {
      res = tmp;
    }
  }
  assert(res);
  return res;
}

static BitwuzlaSort *
wrap_sort(Bitwuzla *bitwuzla, BzlaSortId bzla_sort)
{
  assert(bitwuzla);
  assert(bzla_sort);

  BitwuzlaSort *res;
  if (bzla_hashint_map_contains(bitwuzla->d_sort_map, bzla_sort))
  {
    res = bzla_hashint_map_get(bitwuzla->d_sort_map, bzla_sort)->as_ptr;
  }
  else
  {
    BZLA_NEW(bitwuzla->d_mm, res);
    res->d_bzla_sort                                              = bzla_sort;
    res->d_bzla                                                   = bitwuzla;
    bzla_hashint_map_add(bitwuzla->d_sort_map, bzla_sort)->as_ptr = res;
  }
  return res;
}

static void
reset_assumptions(Bitwuzla *bitwuzla)
{
  assert(bitwuzla);
  assert(bitwuzla->d_bzla);
  if (bitwuzla->d_bzla->valid_assignments)
  {
    BZLA_RESET_STACK(bitwuzla->d_assumptions);
  }
}

/* -------------------------------------------------------------------------- */

static void
abort_aux(const char *msg)
{
  if (bzla_abort_callback.cb_fun)
    ((void (*)(const char *)) bzla_abort_callback.cb_fun)(msg);
}

BzlaAbortCallback bzla_abort_callback = {.abort_fun = abort_aux,
                                         .cb_fun    = bzla_abort_fun};

/* -------------------------------------------------------------------------- */

#define BZLA_RETURN_BITWUZLA_SORT(bitwuzla, sort)    \
  do                                                 \
  {                                                  \
    assert(res);                                     \
    inc_ext_refs_sort(bzla, res);                    \
    return BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, res); \
  } while (0)

#define BZLA_RETURN_BITWUZLA_TERM(term)       \
  do                                          \
  {                                           \
    assert(res);                              \
    bzla_node_inc_ext_ref_counter(bzla, res); \
    return BZLA_EXPORT_BITWUZLA_TERM(res);    \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_new(void)
{
  Bitwuzla *res;
  BzlaMemMgr *mm = bzla_mem_mgr_new();
  BZLA_NEW(mm, res);
  res->d_mm             = mm;
  res->d_bzla           = bzla_new();
  res->d_bzla->bitwuzla = res;
  res->d_sort_map       = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, res->d_assumptions);
  BZLA_INIT_STACK(mm, res->d_unsat_assumptions);
  BZLA_INIT_STACK(mm, res->d_unsat_core);
  BZLA_INIT_STACK(mm, res->d_fun_domain_sorts);
  BZLA_INIT_STACK(mm, res->d_sort_fun_domain_sorts);
  bzla_opt_set(res->d_bzla, BZLA_OPT_AUTO_CLEANUP, 1);
  return res;
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  BzlaIntHashTableIterator it;
  bzla_iter_hashint_init(&it, bitwuzla->d_sort_map);
  while (bzla_iter_hashint_has_next(&it))
  {
    BitwuzlaSort *sort = bzla_iter_hashint_next_data(&it)->as_ptr;
    BZLA_DELETE(bitwuzla->d_mm, sort);
  }
  bzla_hashint_map_delete(bitwuzla->d_sort_map);
  BZLA_RELEASE_STACK(bitwuzla->d_assumptions);
  BZLA_RELEASE_STACK(bitwuzla->d_unsat_assumptions);
  BZLA_RELEASE_STACK(bitwuzla->d_unsat_core);
  BZLA_RELEASE_STACK(bitwuzla->d_fun_domain_sorts);
  BZLA_RELEASE_STACK(bitwuzla->d_sort_fun_domain_sorts);
  bzla_delete(bitwuzla->d_bzla);
  BzlaMemMgr *mm = bitwuzla->d_mm;
  BZLA_DELETE(mm, bitwuzla);
  bzla_mem_mgr_delete(mm);
}

const char *
bitwuzla_copyright(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return BZLA_LICENSE
#if defined(BZLA_USE_LINGELING) || defined(BZLA_USE_PICOSAT)  \
    || defined(BZLA_USE_MINISAT) || defined(BZLA_USE_CADICAL) \
    || defined(BZLA_USE_CMS) || defined(BZLA_USE_GMP)
      "\n\n"
      "This version of Bitwuzla is linked against the following\n"
      "third party libraries. For copyright information of each\n"
      "library see the corresponding url.\n"
#endif
#ifdef BZLA_USE_LINGELING
      "\n"
      "  Lingeling\n"
      "  https://github.com/arminbiere/lingeling\n"
#endif
#ifdef BZLA_USE_PICOSAT
      "\n"
      "  PicoSAT\n"
      "  http://fmv.jku.at/picosat\n"
#endif
#ifdef BZLA_USE_MINISAT
      "\n"
      "  MiniSAT\n"
      "  https://github.com/niklasso/minisat\n"
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
#ifdef BZLA_USE_GMP
      "\n"
      "  GMP - GNU Multiple Precision Arithmetic Library\n"
      "  https://gmplib.org \n"
#endif
#ifdef BZLA_USE_SYMFPU
      "\n"
      "  SymFPU\n"
      "  https://github.com/martin-cs/symfpu \n"
#endif
      "";
}

const char *
bitwuzla_version(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_version(BZLA_IMPORT_BITWUZLA(bitwuzla));
}

bool
bitwuzla_terminate(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_terminate(BZLA_IMPORT_BITWUZLA(bitwuzla)) != 0;
}

void
bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                  int32_t (*fun)(void *),
                                  void *state)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  bzla_set_term(BZLA_IMPORT_BITWUZLA(bitwuzla), fun, state);
}

void *
bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  return bzla_get_term_state(BZLA_IMPORT_BITWUZLA(bitwuzla));
}

void
bitwuzla_set_abort_callback(void (*fun)(const char *msg))
{
  bzla_abort_callback.abort_fun = abort_aux;
  bzla_abort_callback.cb_fun    = fun;
}

void
bitwuzla_set_option(Bitwuzla *bitwuzla, BitwuzlaOption option, uint32_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

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
      BZLA_ABORT(
          bzla_opt_get(bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_UCOPT)),
          "incremental solving cannot be enabled "
          "if unconstrained optimization is enabled");
    }
    else if (option == BITWUZLA_OPT_UCOPT)
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
      BZLA_ABORT(
          bzla_opt_get(
              bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_NONDESTR_SUBST)),
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
    else if (option == BITWUZLA_OPT_NONDESTR_SUBST)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla,
                       BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_FUN_DUAL_PROP)),
          "non-destructive substitution is not supported with dual "
          "propagation");
    }
    else if (option == BITWUZLA_OPT_PRODUCE_MODELS)
    {
      BZLA_ABORT(
          bzla_opt_get(bzla, BZLA_IMPORT_BITWUZLA_OPTION(BITWUZLA_OPT_UCOPT)),
          "model generation cannot be enabled "
          "if unconstrained optimization is enabled");
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
#ifndef BZLA_USE_MINISAT
        || value == BZLA_SAT_ENGINE_MINISAT
#endif
#ifndef BZLA_USE_PICOSAT
        || value == BZLA_SAT_ENGINE_PICOSAT
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
#if 0
#ifndef BZLA_USE_LINGELING
  if (opt == BZLA_OPT_SAT_ENGINE_LGL_FORK)
  {
    value = val;
    BZLA_WARN (true,
              "SAT solver Lingeling not compiled in, will not set option "
              "to clone/fork Lingeling");
  }
#endif
  if (opt == BZLA_OPT_REWRITE_LEVEL)
  {
    BZLA_ABORT(
        BZLA_COUNT_STACK (bzla->nodes_id_table) > 2,
        "setting rewrite level must be done before creating expressions");
  }
#endif
  bzla_opt_set(bzla, opt, value);
}

uint32_t
bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  return bzla_opt_get(bzla, opt);
}

BitwuzlaSort *
bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                       const BitwuzlaSort *index,
                       const BitwuzlaSort *element)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(index);
  BZLA_CHECK_ARG_NOT_NULL(element);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, index);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, element);

  Bzla *bzla       = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId isort = BZLA_IMPORT_BITWUZLA_SORT(index);
  BzlaSortId esort = BZLA_IMPORT_BITWUZLA_SORT(element);

  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, isort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, esort);

  BzlaSortId res = bzla_sort_array(bzla, isort, esort);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaSort *
bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bool(bzla);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaSort *
bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bv(bzla, size);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaSort *
bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla, uint32_t exp_size, uint32_t sig_size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(exp_size);
  BZLA_CHECK_ARG_NOT_ZERO(sig_size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_fp(bzla, exp_size, sig_size);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaSort *
bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                     uint32_t arity,
                     const BitwuzlaSort *domain[],
                     const BitwuzlaSort *codomain)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(arity);
  BZLA_CHECK_ARG_NOT_NULL(domain);
  BZLA_CHECK_ARG_NOT_NULL(codomain);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, codomain);

  Bzla *bzla      = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId cdom = BZLA_IMPORT_BITWUZLA_SORT(codomain);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, cdom);

  BzlaSortId dom[arity];
  for (uint32_t i = 0; i < arity; i++)
  {
    dom[i] = BZLA_IMPORT_BITWUZLA_SORT(domain[i]);
    BZLA_CHECK_SORT_BITWUZLA_AT_IDX(bitwuzla, domain[i], i);
    BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, dom[i], i);
  }
  BzlaSortId tupsort = bzla_sort_tuple(bzla, dom, arity);

  BzlaSortId res = bzla_sort_fun(bzla, tupsort, cdom);
  bzla_sort_release(bzla, tupsort);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaSort *
bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_rm(bzla);
  BZLA_RETURN_BITWUZLA_SORT(bitwuzla, res);
}

BitwuzlaTerm *
bitwuzla_mk_true(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_true(bzla);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_false(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_false(bzla);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_one(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_ones(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_min_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_max_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_nan(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                     const BitwuzlaSort *sort,
                     const char *value,
                     BitwuzlaBVBase base)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(value);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  uint32_t size = bzla_sort_bv_get_width(bzla, bzla_sort);
  BzlaBitVector *bv;
  switch (base)
  {
    case BITWUZLA_BV_BASE_BIN:
      for (const char *p = value; *p; p++)
      {
        BZLA_ABORT(*p != '1' && *p != '0', "invalid binary string");
      }
      BZLA_ABORT(size < strlen(value),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_char_to_bv(bzla->mm, value);
      break;

    case BITWUZLA_BV_BASE_DEC:
      for (const char *p = value; *p; p++)
      {
        /* 48-57: 0-9 */
        BZLA_ABORT(*p < 48 || *p > 57, "invalid decimal string");
      }
      BZLA_ABORT(!bzla_util_check_dec_to_bv(bzla->mm, value, size),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_constd(bzla->mm, value, size);
      break;

    case BITWUZLA_BV_BASE_HEX:
      for (const char *p = value; *p; p++)
      {
        /* 48-57: 0-9, 65-70: A-F, 97-102: a-f */
        BZLA_ABORT((*p < 48 || *p > 57) && (*p < 65 || *p > 70)
                       && (*p < 97 || *p > 102),
                   "invalid hex string");
      }
      BZLA_ABORT(!bzla_util_check_hex_to_bv(bzla->mm, value, size),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_consth(bzla->mm, value, size);
      break;

    default: BZLA_ABORT(true, "invalid base for numerical string");
  }
  BzlaNode *res = bzla_exp_bv_const(bzla, bv);
  assert(bzla_node_get_sort_id(res) == bzla_sort);
  bzla_bv_free(bzla->mm, bv);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
                            const BitwuzlaSort *sort,
                            uint64_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  BzlaBitVector *bv = bzla_bv_uint64_to_bv(
      bzla->mm, value, bzla_sort_bv_get_width(bzla, bzla_sort));
  BzlaNode *res = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                     const BitwuzlaTerm *bv_sign,
                     const BitwuzlaTerm *bv_exponent,
                     const BitwuzlaTerm *bv_significand)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(bv_sign);
  BZLA_CHECK_ARG_NOT_NULL(bv_exponent);
  BZLA_CHECK_ARG_NOT_NULL(bv_significand);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *sign = BZLA_IMPORT_BITWUZLA_TERM(bv_sign);
  BzlaNode *exp  = BZLA_IMPORT_BITWUZLA_TERM(bv_exponent);
  BzlaNode *sig  = BZLA_IMPORT_BITWUZLA_TERM(bv_significand);
  assert(bzla_node_get_ext_refs(sign));
  assert(bzla_node_get_ext_refs(exp));
  assert(bzla_node_get_ext_refs(sig));
  BZLA_CHECK_TERM_BZLA(bzla, sign);
  BZLA_CHECK_TERM_BZLA(bzla, exp);
  BZLA_CHECK_TERM_BZLA(bzla, sig);
  BZLA_CHECK_TERM_IS_BV(bzla, sign);
  BZLA_CHECK_TERM_IS_BV(bzla, exp);
  BZLA_CHECK_TERM_IS_BV(bzla, sig);
  BZLA_CHECK_TERM_IS_BV_VAL(sign);
  BZLA_CHECK_TERM_IS_BV_VAL(exp);
  BZLA_CHECK_TERM_IS_BV_VAL(sig);
  BZLA_ABORT(
      bzla_node_bv_get_width(bzla, sign) != 1,
      "invalid bit-vector size for argument 'bv_sign', expected size one");

  BzlaNode *res = bzla_exp_fp_const(bzla, sign, exp, sig);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_rm_value(Bitwuzla *bitwuzla, BitwuzlaRoundingMode rm)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_ABORT(rm >= BITWUZLA_RM_MAX, "invalid rounding mode");

  Bzla *bzla    = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *res = bzla_exp_rm_const(bzla, BZLA_IMPORT_BITWUZLA_RM(rm));
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg)
{
  const BitwuzlaTerm *args[] = {arg};
  return bitwuzla_mk_term(bitwuzla, kind, 1, args);
}

BitwuzlaTerm *
bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  return bitwuzla_mk_term(bitwuzla, kind, 2, args);
}

BitwuzlaTerm *
bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  const BitwuzlaTerm *arg0,
                  const BitwuzlaTerm *arg1,
                  const BitwuzlaTerm *arg2)
{
  const BitwuzlaTerm *args[] = {arg0, arg1, arg2};
  return bitwuzla_mk_term(bitwuzla, kind, 3, args);
}

BitwuzlaTerm *
bitwuzla_mk_term(Bitwuzla *bitwuzla,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 const BitwuzlaTerm *args[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode **bzla_args = BZLA_IMPORT_BITWUZLA_TERMS(args);

  BzlaNode *res = NULL;
  switch (kind)
  {
    case BITWUZLA_KIND_EQUAL:
      BZLA_CHECK_MK_TERM_ARGS(
          "equal", true, bzla_args, 2, argc, 0, sort_any, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_eq);
      break;

    case BITWUZLA_KIND_DISTINCT:
      BZLA_CHECK_MK_TERM_ARGS(
          "distinct", true, bzla_args, 2, argc, 0, sort_any, true);
      res = mk_term_pairwise(bzla, bzla_args, argc, bzla_exp_ne);
      break;

    case BITWUZLA_KIND_IMPLIES:
      BZLA_CHECK_MK_TERM_ARGS(
          "implies", true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_right_assoc(bzla, bzla_args, argc, bzla_exp_implies);
      break;

    case BITWUZLA_KIND_IFF:
      BZLA_CHECK_MK_TERM_ARGS(
          "iff", false, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = bzla_exp_iff(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_NOT:
      BZLA_CHECK_MK_TERM_ARGS(
          "not", false, bzla_args, 1, argc, 0, bzla_sort_is_bool, true);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_AND:
      BZLA_CHECK_MK_TERM_ARGS(
          "and", true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_and);
      break;

    case BITWUZLA_KIND_OR:
      BZLA_CHECK_MK_TERM_ARGS(
          "or", true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_or);
      break;

    case BITWUZLA_KIND_XOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "xor", true, bzla_args, 2, argc, 0, bzla_sort_is_bool, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_xor);
      break;

    case BITWUZLA_KIND_BV_COMP:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_comp", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_eq(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_NOT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_not", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_neg", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_redor", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDXOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_redxor", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redxor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDAND:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_redand", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_redand(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_XOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_xor", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_xor);
      break;

    case BITWUZLA_KIND_BV_XNOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_xnor", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_xnor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_AND:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_and", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_and);
      break;

    case BITWUZLA_KIND_BV_NAND:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_nand", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_nand(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_OR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_or", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_or);
      break;

    case BITWUZLA_KIND_BV_NOR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_nor", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_nor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ADD:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_add", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_add);
      break;

    case BITWUZLA_KIND_BV_UADD_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_uadd_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_uaddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SADD_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_sadd_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_saddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_MUL:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_mul", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_mul);
      break;

    case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_umul_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_umulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_smul_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_smulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_ult", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ult(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_slt", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_slt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULE:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_ule", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ulte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLE:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_sle", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_slte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_ugt", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ugt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_sgt", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sgt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGE:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_uge", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ugte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGE:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_sge", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sgte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHL:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_shl", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sll(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_shr", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_srl(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ASHR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_ashr", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sra(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SUB:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_sub", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sub(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_usub_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_usubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_ssub_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_ssubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UDIV:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_udiv", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_udiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_sdiv", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_sdiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
      BZLA_CHECK_MK_TERM_ARGS("bv_sdiv_overflow",
                              false,
                              bzla_args,
                              2,
                              argc,
                              0,
                              bzla_sort_is_bv,
                              true);
      res = bzla_exp_bv_sdivo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UREM:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_urem", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_urem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SREM:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_srem", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_srem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMOD:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_smod", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_smod(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROL:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_rol", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_rol(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROR:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_ror", false, bzla_args, 2, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_ror(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_INC:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_inc", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_inc(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_DEC:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_dec", false, bzla_args, 1, argc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_dec(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_CONCAT:
      BZLA_CHECK_MK_TERM_ARGS(
          "bv_concat", true, bzla_args, 2, argc, 0, bzla_sort_is_bv, false);
      res = mk_term_left_assoc(bzla, bzla_args, argc, bzla_exp_bv_concat);
      break;

    case BITWUZLA_KIND_FP_FP:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_fp", false, bzla_args, 3, argc, 0, bzla_sort_is_bv, false);
      BZLA_ABORT(
          bzla_node_bv_get_width(bzla, bzla_args[0]) != 1,
          "invalid bit-vector size for argument at index 0, expected size 1");
      res = bzla_exp_fp_fp(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_ABS:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_abs", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_abs(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_neg", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NORMAL:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_normal", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_normal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_SUBNORMAL:
      BZLA_CHECK_MK_TERM_ARGS("fp_is_subnormal",
                              false,
                              bzla_args,
                              1,
                              argc,
                              0,
                              bzla_sort_is_fp,
                              true);
      res = bzla_exp_fp_is_subnormal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NAN:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_nan", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_nan(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_ZERO:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_zero", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_zero(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_INF:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_inf", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_inf(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NEG:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_neg", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_POS:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_is_pos", false, bzla_args, 1, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_is_pos(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_MIN:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_min", false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_min(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_MAX:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_max", false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_max(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_REM:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_rem", false, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = bzla_exp_fp_rem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_EQ:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_eq", true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_fpeq);
      break;

    case BITWUZLA_KIND_FP_LEQ:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_leq", true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_lte);
      break;

    case BITWUZLA_KIND_FP_LT:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_lt", true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_lt);
      break;

    case BITWUZLA_KIND_FP_GEQ:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_geq", true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_gte);
      break;

    case BITWUZLA_KIND_FP_GT:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_gt", true, bzla_args, 2, argc, 0, bzla_sort_is_fp, true);
      res = mk_term_chained(bzla, bzla_args, argc, bzla_exp_fp_gt);
      break;

    case BITWUZLA_KIND_FP_SQRT:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_sqrt", false, bzla_args, 2, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_sqrt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_RTI:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_rti", false, bzla_args, 2, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_rti(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_ADD:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_add", false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_add(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_SUB:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_sub", false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_sub(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_MUL:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_mul", false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_mul(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_DIV:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_div", false, bzla_args, 3, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_div(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_FMA:
      BZLA_CHECK_MK_TERM_ARGS(
          "fp_fma", false, bzla_args, 4, argc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_fp_fma(
          bzla, bzla_args[0], bzla_args[1], bzla_args[2], bzla_args[3]);
      break;

    case BITWUZLA_KIND_ARRAY_SELECT:
      BZLA_CHECK_MK_TERM_ARGS(
          "array_select", false, bzla_args, 2, argc, 0, sort_any, false);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      BZLA_ABORT(
          bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[1]),
          "sort of index term does not match index sort of array");
      res = bzla_exp_read(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_ARRAY_STORE:
      BZLA_CHECK_MK_TERM_ARGS(
          "array_store", false, bzla_args, 3, argc, 0, sort_any, false);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[2], 2);
      BZLA_ABORT(
          bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[1]),
          "sort of index term does not match index sort of array");
      BZLA_ABORT(
          bzla_sort_array_get_element(bzla, bzla_node_get_sort_id(bzla_args[0]))
              != bzla_node_get_sort_id(bzla_args[2]),
          "sort of element term does not match element sort of array");
      res = bzla_exp_write(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_ITE:
      BZLA_CHECK_MK_TERM_ARGS(
          "ite", false, bzla_args, 3, argc, 1, sort_any, true);
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[0], 0);
      res = bzla_exp_cond(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_APPLY: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'apply', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack apply_args;
      BZLA_INIT_STACK(bzla->mm, apply_args);
      uint32_t apply_argc = argc - 1;
      for (uint32_t i = 0; i < apply_argc; i++)
      {
        BZLA_CHECK_ARG_NOT_NULL_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(apply_args, bzla_args[i]);
      }
      BzlaNode *fun = bzla_args[apply_argc];
      BZLA_CHECK_TERM_IS_FUN_AT_IDX(fun, apply_argc);
      BZLA_ABORT(
          bzla_node_fun_get_arity(bzla, fun) != argc - 1,
          "number of given arguments to function must match arity of function");
      BzlaNode *apply_args_node =
          bzla_exp_args(bzla, apply_args.start, apply_argc);
      BZLA_ABORT(
          bzla_node_get_sort_id(apply_args_node)
              != bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun)),
          "sorts of arguments to apply don't match domain sorts of "
          "given function");
      res = bzla_exp_apply(bzla, fun, apply_args_node);
      BZLA_RELEASE_STACK(apply_args);
      bzla_node_release(bzla, apply_args_node);
    }
    break;

    case BITWUZLA_KIND_LAMBDA: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'lambda', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(bzla_args[paramc], paramc);
      BZLA_CHECK_TERM_IS_BV_LAMBDA_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_fun(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_FORALL: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'forall', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_forall_n(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_EXISTS: {
      BZLA_ABORT(
          argc < 2,
          "invalid number of arguments for kind 'exists', expected at least "
          "2, got %u",
          argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_IS_VAR_AT_IDX(bzla_args[i], i);
        BZLA_CHECK_TERM_NOT_IS_VAR_BOUND_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[paramc], paramc);
      res = bzla_exp_exists_n(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    default: BZLA_ABORT(true, "unexpected operator kind");
  }
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg};
  uint32_t idxs[]            = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 1, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg};
  uint32_t idxs[]            = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 2, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  uint32_t idxs[]            = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 1, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           const BitwuzlaTerm *arg0,
                           const BitwuzlaTerm *arg1,
                           uint32_t idx0,
                           uint32_t idx1)
{
  const BitwuzlaTerm *args[] = {arg0, arg1};
  uint32_t idxs[]            = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 2, args, 2, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                         BitwuzlaKind kind,
                         uint32_t argc,
                         const BitwuzlaTerm *args[],
                         uint32_t idxc,
                         uint32_t idxs[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode **bzla_args = BZLA_IMPORT_BITWUZLA_TERMS(args);
  for (uint32_t i = 0; i < argc; i++)
  {
    assert(bzla_node_get_ext_refs(bzla_args[i]));
    BZLA_CHECK_TERM_BZLA(bzla, bzla_args[i]);
  }

  BzlaNode *res = NULL;
  switch (kind)
  {
    case BITWUZLA_KIND_BV_EXTRACT:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "bv_extract", bzla_args, 1, argc, 2, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(idxs[0] > bzla_node_bv_get_width(bzla, bzla_args[0]),
                 "upper index must be < bit-vector size of given term");
      BZLA_ABORT(idxs[0] < idxs[1], "upper index must be >= lower index");
      res = bzla_exp_bv_slice(bzla, bzla_args[0], idxs[0], idxs[1]);
      break;

    case BITWUZLA_KIND_BV_ZERO_EXTEND:
      BZLA_CHECK_MK_TERM_ARGS_IDXED("bv_zero_extend",
                                    bzla_args,
                                    1,
                                    argc,
                                    1,
                                    idxc,
                                    0,
                                    bzla_sort_is_bv,
                                    true);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      res = bzla_exp_bv_uext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_SIGN_EXTEND:
      BZLA_CHECK_MK_TERM_ARGS_IDXED("bv_sign_extend",
                                    bzla_args,
                                    1,
                                    argc,
                                    1,
                                    idxc,
                                    0,
                                    bzla_sort_is_bv,
                                    true);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      res = bzla_exp_bv_sext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_ROLI:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "bv_roli", bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_roli(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_RORI:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "bv_rori", bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      res = bzla_exp_bv_rori(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_REPEAT:
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "bv_repeat", bzla_args, 1, argc, 1, idxc, 0, bzla_sort_is_bv, true);
      BZLA_ABORT(((uint32_t)(UINT32_MAX / idxs[0]))
                     < bzla_node_bv_get_width(bzla, bzla_args[0]),
                 "resulting bit-vector size of 'repeat' exceeds maximum "
                 "bit-vector size of %u",
                 UINT32_MAX);
      res = bzla_exp_bv_repeat(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_FP_TO_SBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "fp_to_sbv", bzla_args, 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_sbv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_UBV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED(
          "fp_to_ubv", bzla_args, 2, argc, 1, idxc, 1, bzla_sort_is_fp, true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_ubv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_BV: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED("fp_to_fp_from_bv",
                                    bzla_args,
                                    1,
                                    argc,
                                    2,
                                    idxc,
                                    0,
                                    bzla_sort_is_bv,
                                    true);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res             = bzla_exp_fp_to_fp_from_bv(bzla, bzla_args[0], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_FP: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED("fp_to_fp_from_fp",
                                    bzla_args,
                                    2,
                                    argc,
                                    2,
                                    idxc,
                                    1,
                                    bzla_sort_is_fp,
                                    true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_fp(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_INT: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED("fp_to_fp_from_int",
                                    bzla_args,
                                    2,
                                    argc,
                                    2,
                                    idxc,
                                    1,
                                    bzla_sort_is_bv,
                                    true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_int(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_UINT: {
      BZLA_CHECK_MK_TERM_ARGS_IDXED("fp_to_fp_from_uint",
                                    bzla_args,
                                    2,
                                    argc,
                                    2,
                                    idxc,
                                    1,
                                    bzla_sort_is_bv,
                                    true);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_uint(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;
    default: BZLA_ABORT(true, "unexpected operator kind");
  }
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_const(Bitwuzla *bitwuzla,
                  const BitwuzlaSort *sort,
                  const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);

  char *s = mk_unique_symbol(bzla, symbol);
  BZLA_ABORT(s != NULL && bzla_hashptr_table_get(bzla->symbols, (char *) s),
             "symbol '%s' already in use in the current context",
             s);
  BzlaNode *res;
  if (bzla_sort_is_array(bzla, bzla_sort))
  {
    res = bzla_exp_array(bzla, bzla_sort, s);
  }
  else if (bzla_sort_is_fun(bzla, bzla_sort))
  {
    res = bzla_exp_uf(bzla, bzla_sort, s);
  }
  else
  {
    res = bzla_exp_var(bzla, bzla_sort, s);
  }
  bzla_mem_freestr(bzla->mm, s);
  (void) bzla_hashptr_table_add(bzla->inputs, bzla_node_copy(bzla, res));
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                        const BitwuzlaSort *sort,
                        const BitwuzlaTerm *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_ARG_NOT_NULL(value);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  BzlaNode *bzla_val = BZLA_IMPORT_BITWUZLA_TERM(value);
  assert(bzla_node_get_ext_refs(bzla_val));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_val);
  BZLA_CHECK_TERM_NOT_IS_FUN(bzla_val);
  BZLA_ABORT(bzla_node_get_sort_id(bzla_val)
                 != bzla_sort_array_get_element(bzla, bzla_sort),
             "sort of 'value' does not match array element sort");
  BzlaNode *res = bzla_exp_const_array(bzla, bzla_sort, bzla_val);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_var(Bitwuzla *bitwuzla,
                const BitwuzlaSort *sort,
                const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(sort);
  BZLA_CHECK_SORT_BITWUZLA(bitwuzla, sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, bzla_sort);

  char *s = mk_unique_symbol(bzla, symbol);
  BZLA_ABORT(s != NULL && bzla_hashptr_table_get(bzla->symbols, (char *) s),
             "symbol '%s' already in use in the current context",
             s);
  BzlaNode *res = bzla_exp_param(bzla, bzla_sort, s);
  bzla_mem_freestr(bzla->mm, s);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

void
bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  if (nlevels)
  {
    for (uint32_t i = 0; i < nlevels; i++)
    {
      BZLA_PUSH_STACK(bzla->assertions_trail,
                      BZLA_COUNT_STACK(bzla->assertions));
    }
    bzla->num_push_pop++;
  }
}

void
bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_ABORT(
      nlevels > BZLA_COUNT_STACK(bzla->assertions_trail),
      "number of levels to pop (%u) greater than number of pushed levels (%u)",
      nlevels,
      BZLA_COUNT_STACK(bzla->assertions_trail));

  if (nlevels)
  {
    uint32_t pos = 0;
    for (uint32_t i = 0; i < nlevels; i++)
    {
      pos = BZLA_POP_STACK(bzla->assertions_trail);
    }
    while (BZLA_COUNT_STACK(bzla->assertions) > pos)
    {
      BzlaNode *cur = BZLA_POP_STACK(bzla->assertions);
      bzla_hashint_table_remove(bzla->assertions_cache, bzla_node_get_id(cur));
      bzla_node_release(bzla, cur);
    }
    bzla->num_push_pop++;
  }
}

void
bitwuzla_assert(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  reset_assumptions(bitwuzla);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  /* Note: All assertions at a context level > 0 are internally handled as
   *       assumptions. */
  if (BZLA_COUNT_STACK(bzla->assertions_trail) > 0
      || bzla_opt_get(bzla, BZLA_OPT_UNSAT_CORES))
  {
    int32_t id = bzla_node_get_id(bzla_term);
    if (!bzla_hashint_table_contains(bzla->assertions_cache, id))
    {
      BZLA_PUSH_STACK(bzla->assertions, bzla_node_copy(bzla, bzla_term));
      bzla_hashint_table_add(bzla->assertions_cache, id);
    }
  }
  else
  {
    bzla_assert_exp(bzla, bzla_term);
  }
}

void
bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  reset_assumptions(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  bzla_assume_exp(bzla, bzla_term);
  BZLA_PUSH_STACK(bitwuzla->d_assumptions, term);
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_UNSAT(bzla, "check for unsat assumptions");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_ABORT(!bzla_is_assumption_exp(bzla, bzla_term),
             "'exp' must be an assumption");
  return bzla_failed_exp(bzla, bzla_term);
}

const BitwuzlaTerm **
bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_UNSAT(bzla, "get unsat assumptions");

  BZLA_RESET_STACK(bitwuzla->d_unsat_assumptions);

  for (size_t i = 0; i < BZLA_COUNT_STACK(bitwuzla->d_assumptions); i++)
  {
    BzlaNode *bzla_assumption =
        BZLA_IMPORT_BITWUZLA_TERM(BZLA_PEEK_STACK(bitwuzla->d_assumptions, i));
    if (bzla_failed_exp(bzla, bzla_assumption))
    {
      BZLA_PUSH_STACK(bitwuzla->d_unsat_assumptions,
                      BZLA_EXPORT_BITWUZLA_TERM(bzla_assumption));
    }
  }
  BZLA_PUSH_STACK(bitwuzla->d_unsat_assumptions, NULL);
  return (const BitwuzlaTerm **) bitwuzla->d_unsat_assumptions.start;
}

const BitwuzlaTerm **
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla);
  BZLA_CHECK_UNSAT(bzla, "get unsat core");

  BZLA_RESET_STACK(bitwuzla->d_unsat_core);

  for (uint32_t i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
  {
    BzlaNode *cur = BZLA_PEEK_STACK(bzla->assertions, i);
    if (cur == NULL) continue;

    if (bzla_failed_exp(bzla, cur))
    {
      BZLA_PUSH_STACK(bitwuzla->d_unsat_core,
                      BZLA_EXPORT_BITWUZLA_TERM(bzla_node_copy(bzla, cur)));
      bzla_node_inc_ext_ref_counter(bzla, cur);
    }
  }
  BZLA_PUSH_STACK(bitwuzla->d_unsat_core, NULL);
  return (const BitwuzlaTerm **) bitwuzla->d_unsat_core.start;
}

void
bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  bzla_fixate_assumptions(bzla);
}

void
bitwuzla_reset_assumptions(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  bzla_reset_assumptions(bzla);
}

BitwuzlaResult
bitwuzla_simplify(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  reset_assumptions(bitwuzla);

  Bzla *bzla                = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSolverResult bzla_res = bzla_simplify(bzla);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaResult
bitwuzla_check_sat(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  reset_assumptions(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  if (bzla->bzla_sat_bzla_called > 0)
  {
    BZLA_CHECK_OPT_INCREMENTAL(bzla);
  }
  BZLA_ABORT(
      bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL) && bzla->quantifiers->count,
      "incremental solving is currently not supported with quantifiers");

  BzlaSolverResult bzla_res = bzla_check_sat(bzla, -1, -1);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaTerm *
bitwuzla_get_value(Bitwuzla *bitwuzla, const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "retrieve model");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BzlaNode *res = bzla_model_get_value(bzla, bzla_term);
  BZLA_RETURN_BITWUZLA_TERM(res);
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

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "print model");
  bzla_print_model(bzla, format, file);
}

void
bitwuzla_dump_formula(Bitwuzla *bitwuzla, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(file);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL),
             "dumping in incremental mode is currently not supported");
  if (strcmp(format, "smt2") == 0)
  {
    bzla_dumpsmt_dump(bzla, file);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_dumpbtor_dump(bzla, file, 1);
  }
  else if (strcmp(format, "aiger_ascii") == 0)
  {
    bzla_dumpaig_dump(bzla, false, file, true);
  }
  else if (strcmp(format, "aiger_binary") == 0)
  {
    bzla_dumpaig_dump(bzla, true, file, true);
  }
  else
  {
    BZLA_ABORT(true,
               "unknown format '%s', expected one of 'smt2', 'bzla', "
               "'aiger_ascii' or 'aiger_binary'",
               format);
  }
}

BitwuzlaResult
bitwuzla_parse(Bitwuzla *bitwuzla,
               FILE *infile,
               const char *infile_name,
               FILE *outfile,
               char **error_msg,
               int32_t *parsed_status,
               bool *parsed_smt2)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);
  BZLA_CHECK_ARG_NOT_NULL(parsed_smt2);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing after having created expressions is not allowed");
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
                      int32_t *parsed_status)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(format);
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing after having created expressions is not allowed");
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
    BZLA_ABORT(
        true, "unknown format '%s', expected one of 'smt2', 'bzla' or 'btor2 ");
  }
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_sort_hash(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);
  return sort->d_bzla_sort;
}

uint32_t
bitwuzla_sort_bv_get_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  return bzla_sort_bv_get_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_exp_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_exp_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_sig_size(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_sig_width(bzla, bzla_sort);
}

BitwuzlaSort *
bitwuzla_sort_array_get_index(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(sort->d_bzla,
                                   bzla_sort_array_get_index(bzla, bzla_sort));
}

BitwuzlaSort *
bitwuzla_sort_array_get_element(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      sort->d_bzla, bzla_sort_array_get_element(bzla, bzla_sort));
}

BitwuzlaSort *
bitwuzla_sort_fun_get_domain(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(sort->d_bzla,
                                   bzla_sort_fun_get_domain(bzla, bzla_sort));
}

const BitwuzlaSort **
bitwuzla_sort_fun_get_domain_sorts(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bitwuzla *bitwuzla   = sort->d_bzla;
  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  uint32_t arity = bzla_sort_fun_get_arity(bzla, bzla_sort);
  BZLA_RESET_STACK(bitwuzla->d_sort_fun_domain_sorts);
  BzlaTupleSort *tuple_sort =
      &bzla_sort_get_by_id(bzla, bzla_sort_fun_get_domain(bzla, bzla_sort))
           ->tuple;
  assert(arity == tuple_sort->num_elements);
  for (uint32_t i = 0; i < arity; i++)
  {
    BzlaSortId id = tuple_sort->elements[i]->id;
    BZLA_PUSH_STACK(bitwuzla->d_sort_fun_domain_sorts,
                    BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, id));
    bzla_sort_copy(bzla, id);
    inc_ext_refs_sort(bzla, id);
  }
  BZLA_PUSH_STACK(bitwuzla->d_sort_fun_domain_sorts, 0);
  return (const BitwuzlaSort **) bitwuzla->d_sort_fun_domain_sorts.start;
}

BitwuzlaSort *
bitwuzla_sort_fun_get_codomain(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(sort->d_bzla,
                                   bzla_sort_fun_get_codomain(bzla, bzla_sort));
}

uint32_t
bitwuzla_sort_fun_get_arity(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  return bzla_sort_fun_get_arity(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_equal(const BitwuzlaSort *sort0, const BitwuzlaSort *sort1)
{
  BZLA_CHECK_ARG_NOT_NULL(sort0);
  BZLA_CHECK_ARG_NOT_NULL(sort1);
  BZLA_ABORT(sort0->d_bzla != sort1->d_bzla,
             "given sorts are not associated with the same solver object");

  Bzla *bzla            = BZLA_IMPORT_BITWUZLA(sort0->d_bzla);
  BzlaSortId bzla_sort0 = BZLA_IMPORT_BITWUZLA_SORT(sort0);
  BzlaSortId bzla_sort1 = BZLA_IMPORT_BITWUZLA_SORT(sort1);
  assert(bzla_sort_is_valid(bzla, bzla_sort0));
  assert(bzla_sort_is_valid(bzla, bzla_sort1));

  return bzla_sort0 == bzla_sort1;
}

bool
bitwuzla_sort_is_array(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_array(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_bv(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_bv(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fp(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_fp(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fun(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_fun(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_rm(const BitwuzlaSort *sort)
{
  BZLA_CHECK_ARG_NOT_NULL(sort);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(sort->d_bzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  assert(bzla_sort_is_valid(bzla, bzla_sort));

  return bzla_sort_is_rm(bzla, bzla_sort);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

size_t
bitwuzla_term_hash(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_get_id(bzla_term);
}

Bitwuzla *
bitwuzla_term_get_bitwuzla(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *res = bzla_node_get_bzla(bzla_term);
  return BZLA_EXPORT_BITWUZLA(res);
}

BitwuzlaSort *
bitwuzla_term_get_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_node_get_sort_id(bzla_term));
}

BitwuzlaSort *
bitwuzla_term_array_get_index_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_array_get_index(bzla_node_get_bzla(bzla_term),
                                bzla_node_get_sort_id(bzla_term)));
}

BitwuzlaSort *
bitwuzla_term_array_get_element_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_array_get_element(bzla_node_get_bzla(bzla_term),
                                  bzla_node_get_sort_id(bzla_term)));
}

BitwuzlaSort *
bitwuzla_term_fun_get_domain_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_fun_get_domain(bzla_node_get_bzla(bzla_term),
                               bzla_node_get_sort_id(bzla_term)));
}

const BitwuzlaSort **
bitwuzla_term_fun_get_domain_sorts(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  Bzla *bzla         = bzla_node_get_bzla(bzla_term);
  Bitwuzla *bitwuzla = BZLA_EXPORT_BITWUZLA(bzla);
  uint32_t arity     = bzla_node_fun_get_arity(bzla, bzla_term);
  BZLA_RESET_STACK(bitwuzla->d_fun_domain_sorts);
  BzlaTupleSort *tuple_sort =
      &bzla_sort_get_by_id(
           bzla,
           bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(bzla_term)))
           ->tuple;
  assert(arity == tuple_sort->num_elements);
  for (uint32_t i = 0; i < arity; i++)
  {
    BzlaSortId id = tuple_sort->elements[i]->id;
    BZLA_PUSH_STACK(bitwuzla->d_fun_domain_sorts,
                    BZLA_EXPORT_BITWUZLA_SORT(bitwuzla, id));
    bzla_sort_copy(bzla, id);
    inc_ext_refs_sort(bzla, id);
  }
  BZLA_PUSH_STACK(bitwuzla->d_fun_domain_sorts, 0);
  return (const BitwuzlaSort **) bitwuzla->d_fun_domain_sorts.start;
}

BitwuzlaSort *
bitwuzla_term_fun_get_codomain_sort(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      BZLA_EXPORT_BITWUZLA(bzla_node_get_bzla(bzla_term)),
      bzla_sort_fun_get_codomain(bzla_node_get_bzla(bzla_term),
                                 bzla_node_get_sort_id(bzla_term)));
}

uint32_t
bitwuzla_term_bv_get_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_BV(bzla, bzla_term);
  return bzla_node_bv_get_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_exp_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_exp_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_sig_size(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_sig_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fun_get_arity(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  return bzla_node_fun_get_arity(bzla, bzla_term);
}

const char *
bitwuzla_term_get_symbol(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return remove_unique_symbol_prefix(bzla,
                                     bzla_node_get_symbol(bzla, bzla_term));
}

void
bitwuzla_term_set_symbol(BitwuzlaTerm *term, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);

  char *s = mk_unique_symbol(bzla, symbol);
  if (bzla_hashptr_table_get(bzla->symbols, s))
  {
    BZLA_WARN(true, "symbol %s already defined, will not set symbol", symbol);
  }
  else
  {
    bzla_node_set_symbol(bzla, bzla_term, s);
  }
  bzla_mem_freestr(bzla->mm, s);
}

bool
bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
                            const BitwuzlaTerm *term1)
{
  BZLA_CHECK_ARG_NOT_NULL(term0);
  BZLA_CHECK_ARG_NOT_NULL(term1);

  BzlaNode *bzla_term0 = BZLA_IMPORT_BITWUZLA_TERM(term0);
  BzlaNode *bzla_term1 = BZLA_IMPORT_BITWUZLA_TERM(term1);
  assert(bzla_node_get_ext_refs(bzla_term0));
  assert(bzla_node_get_ext_refs(bzla_term0));
  return bzla_node_get_sort_id(bzla_term0) == bzla_node_get_sort_id(bzla_term1);
}

bool
bitwuzla_term_is_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_const(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_var(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_fun(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fun(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_param(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bound_var(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_VAR(bzla_term);
  return bzla_node_param_is_bound(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bv_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_fp_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_rm_value(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bv(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_bv(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_fp(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_fp(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_rm(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_rm(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_zero(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_one(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_ones(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_min_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_max_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_const_array(const BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_const_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

void
bitwuzla_term_dump(const BitwuzlaTerm *term, const char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(term);
  BZLA_CHECK_ARG_NOT_NULL(file);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  Bzla *bzla          = bzla_node_get_bzla(bzla_term);
  if (strcmp(format, "smt2") == 0)
  {
    bzla_dumpsmt_dump(bzla, file);
    bzla_dumpsmt_dump_node(bzla, file, bzla_simplify_exp(bzla, bzla_term), 0);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_dumpbtor_dump_node(bzla, file, bzla_simplify_exp(bzla, bzla_term));
  }
  else
  {
    BZLA_ABORT(true, "unknown format '%s', expected one of 'smt2' or 'bzla'");
  }
}

/* main only ---------------------------------------------------------------- */

Bzla *
bitwuzla_get_bzla(Bitwuzla *bitwuzla)
{
  return bitwuzla->d_bzla;
}

/* parser only -------------------------------------------------------------- */

BzlaMsg *
bitwuzla_get_bzla_msg(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  return bzla->msg;
}

/* smt2 parser only --------------------------------------------------------- */

void
bitwuzla_term_var_mark_bool(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);

  BzlaPtrHashBucket *b = bzla_hashptr_table_get(bzla->inputs, bzla_term);
  assert(b);
  b->data.flag = true;
}

void
bitwuzla_term_print_value_smt2(BitwuzlaTerm *term, char *symbol, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "print model value");
  BZLA_ABORT(bzla->quantifiers->count,
             "'get-value' is currently not supported with quantifiers");
  bzla_print_value_smt2(bzla, bzla_term, symbol, file);
}

BitwuzlaOption
bitwuzla_get_option_from_string(Bitwuzla *bitwuzla, const char *str)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(str);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);

  if (!bzla_hashptr_table_get(bzla->str2opt, str))
  {
    return BITWUZLA_OPT_NUM_OPTS;
  }
  return BZLA_EXPORT_BITWUZLA_OPTION(
      bzla_hashptr_table_get(bzla->str2opt, str)->data.as_int);
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_set_bzla_id(Bitwuzla *bitwuzla, BitwuzlaTerm *term, int32_t id)
{
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
}

/* bzla parser only --------------------------------------------------------- */

void
bitwuzla_add_output(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla          = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);

  BZLA_PUSH_STACK(bzla->outputs, bzla_node_copy(bzla, bzla_term));
}
