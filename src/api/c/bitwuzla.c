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

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA(bitwuzla) ((Bzla *) (bitwuzla))
#define BZLA_EXPORT_BITWUZLA(bzla) ((Bitwuzla *) (bzla))

#define BZLA_IMPORT_BITWUZLA_TERM(term) (((BzlaNode *) (term)))
#define BZLA_IMPORT_BITWUZLA_TERMS(terms) (((BzlaNode **) (terms)))
#define BZLA_EXPORT_BITWUZLA_TERM(node) (((BitwuzlaTerm *) (node)))
#define BZLA_EXPORT_BITWUZLA_TERMS(terms) (((const BitwuzlaTerm **) (terms)))

#define BZLA_IMPORT_BITWUZLA_SORT(sort) (((BzlaSortId)(long) (sort)))
#define BZLA_EXPORT_BITWUZLA_SORT(sort) (((BitwuzlaSort)(long) (sort)))

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (bzla_options[option])

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

#define BZLA_CHECK_ARG_NOT_ZERO(arg) \
  BZLA_ABORT(arg == 0, "argument '%s' must be > 0", #arg)

#define BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(arg) \
  BZLA_ABORT(arg == NULL || *arg == '\0', "expected non-empty string")

#define BZLA_CHECK_ARG_CNT(kind, expected, argc)                               \
  BZLA_ABORT(                                                                  \
      (argc) != (expected),                                                    \
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

#define BZLA_CHECK_ARGS_SORT(bzla, args, argc, start, sort_check)              \
  for (uint32_t i = (start), j = (start) + 1; i < (argc); i++, j++)            \
  {                                                                            \
    BzlaSortId sorti = bzla_node_get_sort_id(args[i]);                         \
    BZLA_ABORT(                                                                \
        !sort_check(bzla, sorti), "node with unexpected sort at index %u", i); \
    if (j < (argc))                                                            \
    {                                                                          \
      BZLA_ABORT(sorti != bzla_node_get_sort_id(args[j]),                      \
                 "terms with mismatching sort at indices %u and %u",           \
                 i,                                                            \
                 j);                                                           \
    }                                                                          \
  }

#define BZLA_CHECK_ARGS_SORT_ONLY(bzla, args, argc, start, sort_check)         \
  for (uint32_t i = (start), j = (start) + 1; i < (argc); i++, j++)            \
  {                                                                            \
    BzlaSortId sorti = bzla_node_get_sort_id(args[i]);                         \
    BZLA_ABORT(                                                                \
        !sort_check(bzla, sorti), "node with unexpected sort at index %u", i); \
  }

#define BZLA_CHECK_OPTION(bzla, opt) \
  BZLA_ABORT(!bzla_opt_is_valid(bzla, opt), "invalid option")

#define BZLA_CHECK_OPTION_VALUE(bzla, opt, value)                              \
  BZLA_ABORT(                                                                  \
      value<bzla_opt_get_min(bzla, opt) || value> bzla_opt_get_max(bzla, opt), \
      "invalid value '%u' for option '%s'",                                    \
      value,                                                                   \
      bzla_opt_get_lng(bzla, opt))

#define BZLA_CHECK_SORT(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_valid(bzla, sort), "invalid sort")

#define BZLA_CHECK_SORT_AT_IDX(bzla, sort, idx) \
  BZLA_ABORT(!bzla_sort_is_valid(bzla, sort), "invalid sort at index %u", (idx))

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

#define BZLA_CHECK_SORT_NOT_IS_FUN(bzla, sort) \
  BZLA_ABORT(bzla_sort_is_fun(bzla, sort), "unexpected function sort")

#define BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, sort, idx) \
  BZLA_ABORT(bzla_sort_is_fun(bzla, sort),                 \
             "unexpected function sort at index %u",       \
             (idx))

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

#define BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(term, idx)                       \
  BZLA_ABORT(                                                              \
      bzla_node_is_fun(bzla_simplify_exp(bzla_node_get_bzla(term), term)), \
      "unexpected function term at index %u",                              \
      (idx))

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
  BZLA_ABORT(sort->ext_refs == INT32_MAX, "Node reference counter overflow");
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
    len += strlen("BZla_@");
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

/* -------------------------------------------------------------------------- */

#define BZLA_RETURN_BITWUZLA_SORT(sort) \
  inc_ext_refs_sort(bzla, res);         \
  return BZLA_EXPORT_BITWUZLA_SORT(res);

#define BZLA_RETURN_BITWUZLA_TERM(term)     \
  bzla_node_inc_ext_ref_counter(bzla, res); \
  return BZLA_EXPORT_BITWUZLA_TERM(res)

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_new(void)
{
  Bzla *bzla = bzla_new();
  bzla_opt_set(bzla, BZLA_OPT_AUTO_CLEANUP, 1);
  return BZLA_EXPORT_BITWUZLA(bzla);
}

void
bitwuzla_delete(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  bzla_delete(BZLA_IMPORT_BITWUZLA(bitwuzla));
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

void
bitwuzla_set_option(Bitwuzla *bitwuzla, BitwuzlaOption option, uint32_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaOption opt = BZLA_IMPORT_BITWUZLA_OPTION(option);

  BZLA_CHECK_OPTION(bzla, opt);
  BZLA_CHECK_OPTION_VALUE(bzla, opt, value);

#if 0
  if (value)
  {
    if (opt == BZLA_OPT_INCREMENTAL)
    {
      BZLA_ABORT (bzla->bzla_sat_bzla_called > 0,
                      "enabling/disabling incremental usage must be done "
                      "before calling 'bitwuzla_check_sat'");
      BZLA_ABORT (bzla_opt_get (bzla, BZLA_OPT_UCOPT),
                      "incremental solving cannot be enabled "
                      "if unconstrained optimization is enabled");
    }
    else if (opt == BZLA_OPT_UCOPT)
    {
      BZLA_ABORT (bzla_opt_get (bzla, BZLA_OPT_MODEL_GEN),
                      "unconstrained optimization cannot be enabled "
                      "if model generation is enabled");
      BZLA_ABORT (bzla_opt_get (bzla, BZLA_OPT_INCREMENTAL),
                      "unconstrained optimization cannot be enabled "
                      "in incremental mode");
    }
    else if (opt == BZLA_OPT_FUN_DUAL_PROP)
    {
      BZLA_ABORT (
          bzla_opt_get (bzla, BZLA_OPT_FUN_JUST),
          "enabling multiple optimization techniques is not allowed");
      BZLA_ABORT (bzla_opt_get (bzla, BZLA_OPT_NONDESTR_SUBST),
                      "Non-destructive substitution is not supported with dual "
                      "propagation");
    }
    else if (opt == BZLA_OPT_FUN_JUST)
    {
      BZLA_ABORT (
          bzla_opt_get (bzla, BZLA_OPT_FUN_DUAL_PROP),
          "enabling multiple optimization techniques is not allowed");
    }
    else if (opt == BZLA_OPT_NONDESTR_SUBST)
    {
      BZLA_ABORT (bzla_opt_get (bzla, BZLA_OPT_FUN_DUAL_PROP),
                      "non-destructive substitution is not supported with dual "
                      "propagation");
    }
  }
#endif
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

BitwuzlaSort
bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                       BitwuzlaSort index,
                       BitwuzlaSort element)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla       = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId isort = BZLA_IMPORT_BITWUZLA_SORT(index);
  BzlaSortId esort = BZLA_IMPORT_BITWUZLA_SORT(element);

  BZLA_CHECK_SORT(bzla, isort);
  BZLA_CHECK_SORT(bzla, esort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, isort);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, esort);

  BzlaSortId res = bzla_sort_array(bzla, isort, esort);
  BZLA_RETURN_BITWUZLA_SORT(res);
}

BitwuzlaSort
bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bool(bzla);
  BZLA_RETURN_BITWUZLA_SORT(res);
}

BitwuzlaSort
bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_bv(bzla, size);
  BZLA_RETURN_BITWUZLA_SORT(res);
}

BitwuzlaSort
bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla, uint32_t exp_size, uint32_t sig_size)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(exp_size);
  BZLA_CHECK_ARG_NOT_ZERO(sig_size);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_fp(bzla, exp_size, sig_size);
  BZLA_RETURN_BITWUZLA_SORT(res);
}

BitwuzlaSort
bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                     uint32_t arity,
                     BitwuzlaSort domain[],
                     BitwuzlaSort codomain)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_ZERO(arity);
  BZLA_CHECK_ARG_NOT_NULL(domain);

  Bzla *bzla      = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId cdom = BZLA_IMPORT_BITWUZLA_SORT(codomain);
  BZLA_CHECK_SORT(bzla, cdom);
  BZLA_CHECK_SORT_NOT_IS_FUN(bzla, cdom);

  BzlaSortId dom[arity];
  for (uint32_t i = 0; i < arity; i++)
  {
    dom[i] = BZLA_IMPORT_BITWUZLA_SORT(domain[i]);
    BZLA_CHECK_SORT_AT_IDX(bzla, dom[i], i);
    BZLA_CHECK_SORT_NOT_IS_FUN_AT_IDX(bzla, dom[i], i);
  }
  BzlaSortId tupsort = bzla_sort_tuple(bzla, dom, arity);

  BzlaSortId res = bzla_sort_fun(bzla, tupsort, cdom);
  bzla_sort_release(bzla, tupsort);
  BZLA_RETURN_BITWUZLA_SORT(res);
}

BitwuzlaSort
bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla     = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId res = bzla_sort_rm(bzla);
  BZLA_RETURN_BITWUZLA_SORT(res);
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
bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_one(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_one(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_ones(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_min_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_bv_max_signed(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_zero(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_pos_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_neg_inf(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  BzlaNode *res = bzla_exp_fp_nan(bzla, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                     BitwuzlaSort sort,
                     const char *value,
                     BitwuzlaBVBase base)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(value);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  uint32_t size = bzla_sort_bv_get_width(bzla, bzla_sort);
  BzlaBitVector *bv;
  switch (base)
  {
    case BITWUZLA_BV_BASE_BIN:
      BZLA_ABORT(size < strlen(value),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_char_to_bv(bzla->mm, value);
      break;
    case BITWUZLA_BV_BASE_DEC:
      BZLA_ABORT(!bzla_util_check_dec_to_bv(bzla->mm, value, size),
                 "value '%s' does not fit into a bit-vector of size %u",
                 value,
                 size);
      bv = bzla_bv_constd(bzla->mm, value, size);
      break;
    case BITWUZLA_BV_BASE_HEX:
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
bitwuzla_mk_bv_value_uint32(Bitwuzla *bitwuzla,
                            BitwuzlaSort sort,
                            uint32_t value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);
  BzlaNode *res = bzla_exp_bv_unsigned(bzla, value, bzla_sort);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_fp_value(Bitwuzla *bitwuzla,
                     BitwuzlaTerm *bv_sign,
                     BitwuzlaTerm *bv_exponent,
                     BitwuzlaTerm *bv_significand)
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
bitwuzla_mk_term1(Bitwuzla *bitwuzla, BitwuzlaKind kind, BitwuzlaTerm *arg)
{
  BitwuzlaTerm *args[] = {arg};
  return bitwuzla_mk_term(bitwuzla, kind, 1, args);
}

BitwuzlaTerm *
bitwuzla_mk_term2(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  BitwuzlaTerm *arg0,
                  BitwuzlaTerm *arg1)
{
  BitwuzlaTerm *args[] = {arg0, arg1};
  return bitwuzla_mk_term(bitwuzla, kind, 2, args);
}

BitwuzlaTerm *
bitwuzla_mk_term3(Bitwuzla *bitwuzla,
                  BitwuzlaKind kind,
                  BitwuzlaTerm *arg0,
                  BitwuzlaTerm *arg1,
                  BitwuzlaTerm *arg2)
{
  BitwuzlaTerm *args[] = {arg0, arg1, arg2};
  return bitwuzla_mk_term(bitwuzla, kind, 3, args);
}

BitwuzlaTerm *
bitwuzla_mk_term(Bitwuzla *bitwuzla,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 BitwuzlaTerm *args[])
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
    case BITWUZLA_KIND_EQUAL:
      BZLA_CHECK_ARG_CNT("equal", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, sort_any);
      res = bzla_exp_eq(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_DISTINCT:
      BZLA_CHECK_ARG_CNT("distinct", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, sort_any);
      res = bzla_exp_ne(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_IMPLIES:
      BZLA_CHECK_ARG_CNT("implies", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_implies(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_IFF:
      BZLA_CHECK_ARG_CNT("iff", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_iff(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_NOT:
      BZLA_CHECK_ARG_CNT("not", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_AND:
      BZLA_CHECK_ARG_CNT("and", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_bv_and(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_OR:
      BZLA_CHECK_ARG_CNT("or", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_bv_or(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_XOR:
      BZLA_CHECK_ARG_CNT("xor", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bool);
      res = bzla_exp_bv_xor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_NOT:
      BZLA_CHECK_ARG_CNT("bv_not", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_not(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_NEG:
      BZLA_CHECK_ARG_CNT("bv_neg", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDOR:
      BZLA_CHECK_ARG_CNT("bv_redor", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_redor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDXOR:
      BZLA_CHECK_ARG_CNT("bv_redxor", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_redxor(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_REDAND:
      BZLA_CHECK_ARG_CNT("bv_redand", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_redand(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_XOR:
      BZLA_CHECK_ARG_CNT("bv_xor", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_xor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_XNOR:
      BZLA_CHECK_ARG_CNT("bv_xnor", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_xnor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_AND:
      BZLA_CHECK_ARG_CNT("bv_and", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_and(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_NAND:
      BZLA_CHECK_ARG_CNT("bv_nand", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_nand(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_OR:
      BZLA_CHECK_ARG_CNT("bv_or", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_or(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_NOR:
      BZLA_CHECK_ARG_CNT("bv_nor", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_nor(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ADD:
      BZLA_CHECK_ARG_CNT("bv_add", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_add(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UADD_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_uadd_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_uaddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SADD_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_sadd_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_saddo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_MUL:
      BZLA_CHECK_ARG_CNT("bv_nand", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_mul(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_umul_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_umulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_smul_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_smulo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULT:
      BZLA_CHECK_ARG_CNT("bv_ult", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ult(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLT:
      BZLA_CHECK_ARG_CNT("bv_slt", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_slt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ULE:
      BZLA_CHECK_ARG_CNT("bv_uleq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ulte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SLE:
      BZLA_CHECK_ARG_CNT("bv_sleq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_slte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGT:
      BZLA_CHECK_ARG_CNT("bv_ugt", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ugt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGT:
      BZLA_CHECK_ARG_CNT("bv_sgt", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sgt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UGE:
      BZLA_CHECK_ARG_CNT("bv_ugeq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ugte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SGE:
      BZLA_CHECK_ARG_CNT("bv_sgeq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sgte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHL:
      BZLA_CHECK_ARG_CNT("bv_shl", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sll(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SHR:
      BZLA_CHECK_ARG_CNT("bv_shr", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_srl(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ASHR:
      BZLA_CHECK_ARG_CNT("bv_ashr", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sra(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SUB:
      BZLA_CHECK_ARG_CNT("bv_sub", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sub(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_usub_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_usubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_ssub_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ssubo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UDIV:
      BZLA_CHECK_ARG_CNT("bv_udiv", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_udiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV:
      BZLA_CHECK_ARG_CNT("bv_sdiv", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sdiv(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
      BZLA_CHECK_ARG_CNT("bv_sdiv_overflow", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_sdivo(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_UREM:
      BZLA_CHECK_ARG_CNT("bv_urem", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_urem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SREM:
      BZLA_CHECK_ARG_CNT("bv_srem", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_srem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_SMOD:
      BZLA_CHECK_ARG_CNT("bv_smod", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_smod(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROL:
      BZLA_CHECK_ARG_CNT("bv_rol", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_rol(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_ROR:
      BZLA_CHECK_ARG_CNT("bv_ror", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_ror(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_BV_INC:
      BZLA_CHECK_ARG_CNT("bv_inc", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_inc(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_DEC:
      BZLA_CHECK_ARG_CNT("bv_dec", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_dec(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_BV_CONCAT:
      BZLA_CHECK_ARG_CNT("bv_concat", 2, argc);
      BZLA_CHECK_ARGS_SORT_ONLY(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      res = bzla_exp_bv_concat(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_FP:
      BZLA_CHECK_ARG_CNT("fp_fp", 3, argc);
      BZLA_CHECK_ARGS_SORT_ONLY(bzla, bzla_args, argc, 0, bzla_sort_is_bv);
      BZLA_ABORT(
          bzla_node_bv_get_width(bzla, bzla_args[0]) != 1,
          "invalid bit-vector size for argument at index 0, expected size 1");
      res = bzla_exp_fp_fp(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_ABS:
      BZLA_CHECK_ARG_CNT("fp_abs", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_abs(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_NEG:
      BZLA_CHECK_ARG_CNT("fp_neg", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NORMAL:
      BZLA_CHECK_ARG_CNT("fp_is_normal", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_normal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_SUBNORMAL:
      BZLA_CHECK_ARG_CNT("fp_is_subnormal", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_subnormal(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NAN:
      BZLA_CHECK_ARG_CNT("fp_is_nan", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_nan(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_ZERO:
      BZLA_CHECK_ARG_CNT("fp_is_zero", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_zero(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_INF:
      BZLA_CHECK_ARG_CNT("fp_is_inf", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_inf(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_NEG:
      BZLA_CHECK_ARG_CNT("fp_is_neg", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_neg(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_IS_POS:
      BZLA_CHECK_ARG_CNT("fp_is_pos", 1, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_is_pos(bzla, bzla_args[0]);
      break;

    case BITWUZLA_KIND_FP_MIN:
      BZLA_CHECK_ARG_CNT("fp_min", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_min(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_MAX:
      BZLA_CHECK_ARG_CNT("fp_max", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_max(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_REM:
      BZLA_CHECK_ARG_CNT("fp_rem", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_rem(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_EQ:
      BZLA_CHECK_ARG_CNT("fp_eq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_fpeq(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_LEQ:
      BZLA_CHECK_ARG_CNT("fp_leq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_lte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_LT:
      BZLA_CHECK_ARG_CNT("fp_lt", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_lt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_GEQ:
      BZLA_CHECK_ARG_CNT("fp_geq", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_gte(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_GT:
      BZLA_CHECK_ARG_CNT("fp_gt", 2, argc);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 0, bzla_sort_is_fp);
      res = bzla_exp_fp_gt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_SQRT:
      BZLA_CHECK_ARG_CNT("fp_sqrt", 2, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, bzla_args[1], 1);
      res = bzla_exp_fp_sqrt(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_RTI:
      BZLA_CHECK_ARG_CNT("fp_rti", 2, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, bzla_args[1], 1);
      res = bzla_exp_fp_rti(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_FP_ADD:
      BZLA_CHECK_ARG_CNT("fp_add", 3, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_fp);
      res = bzla_exp_fp_add(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_SUB:
      BZLA_CHECK_ARG_CNT("fp_sub", 3, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_fp);
      res = bzla_exp_fp_sub(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_MUL:
      BZLA_CHECK_ARG_CNT("fp_mul", 3, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_fp);
      res = bzla_exp_fp_mul(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_DIV:
      BZLA_CHECK_ARG_CNT("fp_div", 3, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_fp);
      res = bzla_exp_fp_div(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_FP_FMA:
      BZLA_CHECK_ARG_CNT("fp_fma", 4, argc);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_fp);
      res = bzla_exp_fp_fma(
          bzla, bzla_args[0], bzla_args[1], bzla_args[2], bzla_args[3]);
      break;

    case BITWUZLA_KIND_ARRAY_SELECT:
      BZLA_CHECK_ARG_CNT("array_select", 2, argc);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      res = bzla_exp_read(bzla, bzla_args[0], bzla_args[1]);
      break;

    case BITWUZLA_KIND_ARRAY_STORE:
      BZLA_CHECK_ARG_CNT("array_store", 3, argc);
      BZLA_CHECK_TERM_IS_ARRAY_AT_IDX(bzla_args[0], 0);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[1], 1);
      BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[2], 2);
      res = bzla_exp_write(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_ITE:
      BZLA_CHECK_ARG_CNT("ite", 3, argc);
      BZLA_CHECK_TERM_IS_BOOL_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, sort_any);
      res = bzla_exp_cond(bzla, bzla_args[0], bzla_args[1], bzla_args[2]);
      break;

    case BITWUZLA_KIND_APPLY: {
      BZLA_ABORT(argc < 2,
                 "invalid argument count for kind 'apply', expected at least "
                 "2, got %u",
                 argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_CHECK_TERM_NOT_IS_FUN_AT_IDX(bzla_args[i], i);
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(
          bzla_node_fun_get_arity(bzla, bzla_args[paramc]) != argc - 1,
          "number of given arguments to function must match arity of function");
      BZLA_CHECK_TERM_IS_FUN_AT_IDX(bzla_args[paramc], paramc);
      res = bzla_exp_apply_n(bzla, bzla_args[paramc], params.start, paramc);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_LAMBDA: {
      BZLA_CHECK_ARG_CNT("lambda", 2, argc);
      BzlaNodePtrStack params;
      BZLA_INIT_STACK(bzla->mm, params);
      uint32_t paramc = argc - 1;
      for (uint32_t i = 0; i < paramc; i++)
      {
        BZLA_PUSH_STACK(params, bzla_args[i]);
      }
      BZLA_ABORT(!vars_distinct(bzla, params.start, paramc),
                 "given variables are not distinct");
      BZLA_CHECK_TERM_NOT_IS_UF_AT_IDX(bzla_args[paramc], paramc);
      res = bzla_exp_fun(bzla, params.start, paramc, bzla_args[paramc]);
      BZLA_RELEASE_STACK(params);
    }
    break;

    case BITWUZLA_KIND_FORALL: {
      BZLA_ABORT(argc < 2,
                 "invalid argument count for kind 'forall', expected at least "
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
      BZLA_ABORT(argc < 2,
                 "invalid argument count for kind 'exists', expected at least "
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
                           BitwuzlaTerm *arg,
                           uint32_t idx)
{
  BitwuzlaTerm *args[] = {arg};
  uint32_t idxs[]      = {idx};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 1, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
                           BitwuzlaKind kind,
                           BitwuzlaTerm *arg,
                           uint32_t idx0,
                           uint32_t idx1)
{
  BitwuzlaTerm *args[] = {arg};
  uint32_t idxs[]      = {idx0, idx1};
  return bitwuzla_mk_term_indexed(bitwuzla, kind, 1, args, 2, idxs);
}

BitwuzlaTerm *
bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                         BitwuzlaKind kind,
                         uint32_t argc,
                         BitwuzlaTerm *args[],
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
      BZLA_CHECK_ARG_CNT("bv_extract", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_extract", idxc, 2);
      BZLA_ABORT(idxs[0] < idxs[1], "upper index must be >= lower index");
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_slice(bzla, bzla_args[0], idxs[0], idxs[1]);
      break;

    case BITWUZLA_KIND_BV_ZERO_EXTEND:
      BZLA_CHECK_ARG_CNT("bv_zero_extend", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_zero_extend", idxc, 1);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_uext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_SIGN_EXTEND:
      BZLA_CHECK_ARG_CNT("bv_sign_extend", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_sign_extend", idxc, 1);
      BZLA_ABORT(
          idxs[0] > UINT32_MAX - bzla_node_bv_get_width(bzla, bzla_args[0]),
          "extending term of bit-vector size %u with %u bits exceeds maximum "
          "bit-vector size of %u",
          bzla_node_bv_get_width(bzla, bzla_args[0]),
          idxs[0],
          UINT32_MAX);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_sext(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_ROLI:
      BZLA_CHECK_ARG_CNT("bv_roli", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_roli", idxc, 1);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_roli(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_RORI:
      BZLA_CHECK_ARG_CNT("bv_rori", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_rori", idxc, 1);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_rori(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_BV_REPEAT:
      BZLA_CHECK_ARG_CNT("bv_repeat", argc, 1);
      BZLA_CHECK_IDX_CNT("bv_repeat", idxc, 1);
      BZLA_ABORT(((uint32_t)(UINT32_MAX / idxs[0]))
                     < bzla_node_bv_get_width(bzla, bzla_args[0]),
                 "resulting bit-vector size of 'repeat' exceeds maximum "
                 "bit-vector size of %u",
                 UINT32_MAX);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      res = bzla_exp_bv_repeat(bzla, bzla_args[0], idxs[0]);
      break;

    case BITWUZLA_KIND_FP_TO_SBV: {
      BZLA_CHECK_ARG_CNT("fp_to_sbv", argc, 2);
      BZLA_CHECK_IDX_CNT("fp_to_sbv", idxc, 1);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, bzla_args[1], 1);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_sbv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_UBV: {
      BZLA_CHECK_ARG_CNT("fp_to_ubv", argc, 1);
      BZLA_CHECK_IDX_CNT("fp_to_ubv", idxc, 1);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, bzla_args[1], 1);
      BzlaSortId sort = bzla_sort_bv(bzla, idxs[0]);
      res = bzla_exp_fp_to_ubv(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_BV: {
      BZLA_CHECK_ARG_CNT("fp_to_fp_from_bv", argc, 1);
      BZLA_CHECK_IDX_CNT("fp_to_fp_from_bv", idxc, 2);
      BZLA_CHECK_ARGS_SORT(bzla, bzla_args, argc, 1, bzla_sort_is_bv);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res             = bzla_exp_fp_to_fp_from_bv(bzla, bzla_args[0], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_FP: {
      BZLA_CHECK_ARG_CNT("fp_to_fp_from_fp", argc, 2);
      BZLA_CHECK_IDX_CNT("fp_to_fp_from_fp", idxc, 2);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_FP_AT_IDX(bzla, bzla_args[1], 1);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_fp(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_INT: {
      BZLA_CHECK_ARG_CNT("fp_to_fp_from_int", argc, 1);
      BZLA_CHECK_IDX_CNT("fp_to_fp_from_int", idxc, 2);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_BV_AT_IDX(bzla, bzla_args[1], 1);
      BzlaSortId sort = bzla_sort_fp(bzla, idxs[0], idxs[1]);
      res = bzla_exp_fp_to_fp_from_int(bzla, bzla_args[0], bzla_args[1], sort);
      bzla_sort_release(bzla, sort);
    }
    break;

    case BITWUZLA_KIND_FP_TO_FP_FROM_UINT: {
      BZLA_CHECK_ARG_CNT("fp_to_fp_from_uint", argc, 1);
      BZLA_CHECK_IDX_CNT("fp_to_fp_from_uint", idxc, 2);
      BZLA_CHECK_TERM_IS_RM_AT_IDX(bzla, bzla_args[0], 0);
      BZLA_CHECK_TERM_IS_BV_AT_IDX(bzla, bzla_args[1], 1);
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
bitwuzla_mk_const(Bitwuzla *bitwuzla, BitwuzlaSort sort, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

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
                        BitwuzlaSort sort,
                        BitwuzlaTerm *value)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(value);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  BzlaNode *bzla_val = BZLA_IMPORT_BITWUZLA_TERM(value);
  assert(bzla_node_get_ext_refs(bzla_val));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_val);
  BZLA_CHECK_TERM_IS_BV(bzla, bzla_val);
  BZLA_ABORT(bzla_node_get_sort_id(bzla_val)
                 != bzla_sort_array_get_element(bzla, bzla_sort),
             "sort of 'value' does not match array element sort");
  BzlaNode *res = bzla_exp_const_array(bzla, bzla_sort, bzla_val);
  BZLA_RETURN_BITWUZLA_TERM(res);
}

BitwuzlaTerm *
bitwuzla_mk_var(Bitwuzla *bitwuzla, BitwuzlaSort sort, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
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
bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

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
bitwuzla_assume(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(term);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_BZLA(bzla, bzla_term);
  BZLA_CHECK_TERM_IS_BOOL(bzla, bzla_term);
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla_term);

  bzla_assume_exp(bzla, bzla_term);
}

bool
bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
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

  BzlaNodePtrStack unsat_assumptions;
  BZLA_INIT_STACK(bzla->mm, unsat_assumptions);
  for (uint32_t i = 0; i < BZLA_COUNT_STACK(bzla->failed_assumptions); i++)
  {
    BzlaNode *assumption = BZLA_PEEK_STACK(bzla->failed_assumptions, i);
    if (assumption == NULL) continue;
    assert(bzla_hashptr_table_get(bzla->orig_assumptions, assumption));
    if (bzla_failed_exp(bzla, assumption))
    {
      BZLA_PUSH_STACK(unsat_assumptions, assumption);
    }
    else
    {
      bzla_node_release(bzla, assumption);
    }
  }
  BZLA_PUSH_STACK(unsat_assumptions, NULL);
  BZLA_RELEASE_STACK(bzla->failed_assumptions);
  bzla->failed_assumptions = unsat_assumptions;

  return BZLA_EXPORT_BITWUZLA_TERMS(bzla->failed_assumptions.start);
}

const BitwuzlaTerm **
bitwuzla_get_unsat_core(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_INCREMENTAL(bzla);
  BZLA_CHECK_OPT_PRODUCE_UNSAT_CORES(bzla);
  BZLA_CHECK_UNSAT(bzla, "get unsat core");

  bzla_reset_unsat_core(bzla);

  for (uint32_t i = 0; i < BZLA_COUNT_STACK(bzla->assertions); i++)
  {
    BzlaNode *cur = BZLA_PEEK_STACK(bzla->assertions, i);
    if (cur == NULL) continue;

    if (bzla_failed_exp(bzla, cur))
    {
      BZLA_PUSH_STACK(bzla->unsat_core, bzla_node_copy(bzla, cur));
      bzla_node_inc_ext_ref_counter(bzla, cur);
    }
  }
  BZLA_PUSH_STACK(bzla->unsat_core, NULL);
  return BZLA_EXPORT_BITWUZLA_TERMS(bzla->unsat_core.start);
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

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  if (bzla->bzla_sat_bzla_called > 0)
  {
    BZLA_CHECK_OPT_INCREMENTAL(bzla);
  }
  BzlaSolverResult bzla_res = bzla_check_sat(bzla, -1, -1);
  if (bzla_res == BZLA_RESULT_SAT) return BITWUZLA_SAT;
  if (bzla_res == BZLA_RESULT_UNSAT) return BITWUZLA_UNSAT;
  assert(bzla_res == BZLA_RESULT_UNKNOWN);
  return BITWUZLA_UNKNOWN;
}

BitwuzlaTerm *
bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
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
  BZLA_CHECK_ARG_NOT_NULL(file);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
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
               "'aiger_ascii' or 'aiger_binary'");
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

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  int32_t bzla_res = bzla_parse(bzla,
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
  BZLA_CHECK_ARG_NOT_NULL(infile);
  BZLA_CHECK_ARG_STR_NOT_NULL_OR_EMPTY(infile_name);
  BZLA_CHECK_ARG_NOT_NULL(outfile);
  BZLA_CHECK_ARG_NOT_NULL(error_msg);
  BZLA_CHECK_ARG_NOT_NULL(parsed_status);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_ABORT(BZLA_COUNT_STACK(bzla->nodes_id_table) > 2,
             "file parsing must be done before creating expressions");
  int32_t bzla_res = 0;
  if (strcmp(format, "smt2") == 0)
  {
    bzla_res = bzla_parse_smt2(
        bzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor") == 0)
  {
    bzla_res = bzla_parse_btor(
        bzla, infile, infile_name, outfile, error_msg, parsed_status);
  }
  else if (strcmp(format, "btor2") == 0)
  {
    bzla_res = bzla_parse_btor2(
        bzla, infile, infile_name, outfile, error_msg, parsed_status);
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

uint32_t
bitwuzla_sort_bv_get_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_BV(bzla, bzla_sort);

  return bzla_sort_bv_get_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_exp_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_exp_width(bzla, bzla_sort);
}

uint32_t
bitwuzla_sort_fp_get_sig_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FP(bzla, bzla_sort);

  return bzla_sort_fp_get_sig_width(bzla, bzla_sort);
}

BitwuzlaSort
bitwuzla_sort_array_get_index(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_array_get_index(bzla, bzla_sort));
}

BitwuzlaSort
bitwuzla_sort_array_get_element(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_ARRAY(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(
      bzla_sort_array_get_element(bzla, bzla_sort));
}

BitwuzlaSort
bitwuzla_sort_fun_get_domain(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_fun_get_domain(bzla, bzla_sort));
}

BitwuzlaSort
bitwuzla_sort_fun_get_codomain(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_fun_get_codomain(bzla, bzla_sort));
}

uint32_t
bitwuzla_sort_fun_get_arity(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);
  BZLA_CHECK_SORT_IS_FUN(bzla, bzla_sort);

  return bzla_sort_fun_get_arity(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_equal(Bitwuzla *bitwuzla,
                       BitwuzlaSort sort0,
                       BitwuzlaSort sort1)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla            = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort0 = BZLA_IMPORT_BITWUZLA_SORT(sort0);
  BzlaSortId bzla_sort1 = BZLA_IMPORT_BITWUZLA_SORT(sort1);
  BZLA_CHECK_SORT(bzla, bzla_sort0);
  BZLA_CHECK_SORT(bzla, bzla_sort1);

  return bzla_sort0 == bzla_sort1;
}

bool
bitwuzla_sort_is_array(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

  return bzla_sort_is_array(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_bv(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

  return bzla_sort_is_bv(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fp(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

  return bzla_sort_is_fp(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_fun(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

  return bzla_sort_is_fun(bzla, bzla_sort);
}

bool
bitwuzla_sort_is_rm(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);

  Bzla *bzla           = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BzlaSortId bzla_sort = BZLA_IMPORT_BITWUZLA_SORT(sort);
  BZLA_CHECK_SORT(bzla, bzla_sort);

  return bzla_sort_is_rm(bzla, bzla_sort);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_get_bitwuzla(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *res = bzla_node_get_bzla(bzla_term);
  return BZLA_EXPORT_BITWUZLA(res);
}

BitwuzlaSort
bitwuzla_term_get_sort(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_node_get_sort_id(bzla_term));
}

BitwuzlaSort
bitwuzla_term_array_get_index_sort(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_array_get_index(
      bzla_node_get_bzla(bzla_term), bzla_node_get_sort_id(bzla_term)));
}

BitwuzlaSort
bitwuzla_term_array_get_element_sort(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_ARRAY(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_array_get_element(
      bzla_node_get_bzla(bzla_term), bzla_node_get_sort_id(bzla_term)));
}

BitwuzlaSort
bitwuzla_term_fun_get_domain_sort(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_fun_get_domain(
      bzla_node_get_bzla(bzla_term), bzla_node_get_sort_id(bzla_term)));
}

BitwuzlaSort
bitwuzla_term_fun_get_codomain_sort(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_FUN(bzla_term);
  /* Note: We don't need to increase the ref counter here. */
  return BZLA_EXPORT_BITWUZLA_SORT(bzla_sort_fun_get_codomain(
      bzla_node_get_bzla(bzla_term), bzla_node_get_sort_id(bzla_term)));
}

uint32_t
bitwuzla_term_bv_get_size(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_BV(bzla, bzla_term);
  return bzla_node_bv_get_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_exp_size(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_exp_width(bzla, bzla_term);
}

uint32_t
bitwuzla_term_fp_get_sig_size(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  BZLA_CHECK_TERM_IS_FP(bzla, bzla_term);
  return bzla_node_fp_get_sig_width(bzla, bzla_term);
}

const char *
bitwuzla_term_get_symbol(BitwuzlaTerm *term)
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
bitwuzla_term_is_array(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_const(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_var(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_fun(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fun(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_var(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_param(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bound_var(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  BZLA_CHECK_TERM_IS_VAR(bzla_term);
  return bzla_node_param_is_bound(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bv_value(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_fp_value(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_rm_value(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_rm_const(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

bool
bitwuzla_term_is_bv(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_bv(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_fp(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_fp(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_rm(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  Bzla *bzla = bzla_node_get_bzla(bzla_term);
  return bzla_node_is_rm(bzla, bzla_simplify_exp(bzla, bzla_term));
}

bool
bitwuzla_term_is_bv_value_zero(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_zero(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_one(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_one(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_ones(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_ones(bzla_node_get_bzla(bzla_term), bzla_term);
}

bool
bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_min_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_bv_const_max_signed(bzla_node_get_bzla(bzla_term),
                                          bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_zero(bzla_node_get_bzla(bzla_term),
                                        bzla_term);
}

bool
bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_pos_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_fp_value_nan(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_fp_const_neg_inf(bzla_node_get_bzla(bzla_term),
                                       bzla_term);
}

bool
bitwuzla_term_is_const_array(BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(term);

  BzlaNode *bzla_term = BZLA_IMPORT_BITWUZLA_TERM(term);
  assert(bzla_node_get_ext_refs(bzla_term));
  return bzla_node_is_const_array(
      bzla_simplify_exp(bzla_node_get_bzla(bzla_term), bzla_term));
}

/* parser only -------------------------------------------------------------- */

BzlaMsg *
bitwuzla_get_bzla_msg(Bitwuzla *bitwuzla)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  return bzla->msg;
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
