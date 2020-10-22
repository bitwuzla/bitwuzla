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
#include "bzlaprintmodel.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlaabort.h"
#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */

#define BZLA_IMPORT_BITWUZLA(bitwuzla) ((Bzla *) (bitwuzla))
#define BZLA_EXPORT_BITWUZLA(bzla) ((Bitwuzla *) (bzla))

#define BZLA_IMPORT_BITWUZLA_TERM(term) (((BzlaNode *) (term)))
#define BZLA_IMPORT_BITWUZLA_TERM_ARRAY(array) (((BzlaNode **) (array)))
#define BZLA_EXPORT_BITWUZLA_TERM(node) (((BitwuzlaTerm *) (node)))

#define BZLA_IMPORT_BITWUZLA_SORT(sort) (((BzlaSortId)(long) (sort)))
#define BZLA_EXPORT_BITWUZLA_SORT(sort) (((BitwuzlaSort)(long) (sort)))

#define BZLA_IMPORT_BITWUZLA_OPTION(option) (((BzlaOption)(option)))
#define BZLA_EXPORT_BITWUZLA_OPTION(option) (((BitwuzlaOption)(option)))

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

#define BZLA_CHECK_ARG_STR_NOT_EMPTY(arg) \
  BZLA_ABORT(*arg == '\0', "expected non-empty string")

#define BZLA_CHECK_OPTION(bzla, opt) \
  BZLA_ABORT(bzla_opt_is_valid(bzla, opt), "invalid option")

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

#define BZLA_CHECK_SORT_IS_BV(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_bv(bzla, sort), "expected bit-vector sort")

#define BZLA_CHECK_SORT_IS_FP(bzla, sort) \
  BZLA_ABORT(!bzla_sort_is_fp(bzla, sort), "expected floating-point sort")

#define BZLA_CHECK_SORT_IS_ARRAY(bzla, sort)                        \
  BZLA_ABORT(!bzla_sort_is_fun(bzla, sort)                          \
                 || bzla_sort_tuple_get_arity(                      \
                        bzla, bzla_sort_fun_get_domain(bzla, sort)) \
                        != 1,                                       \
             "expected array sort");

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

#define BZLA_CHECK_TERM_IS_BOOL(bzla, term)                         \
  BZLA_ABORT(!bzla_sort_is_bool(bzla, bzla_node_get_sort_id(term)), \
             "expected boolean term")

#define BZLA_CHECK_TERM_IS_BV(bzla, term) \
  BZLA_ABORT(!bzla_node_is_bv(bzla, term), "expected bit-vector term")

#define BZLA_CHECK_TERM_IS_FP(bzla, term) \
  BZLA_ABORT(!bzla_node_is_fp(bzla, term), "expected floating-point term")

#define BZLA_CHECK_TERM_IS_RM(bzla, term) \
  BZLA_ABORT(!bzla_node_is_rm(bzla, term), "expected rounding-mode term")

#define BZLA_CHECK_TERM_IS_BV_VAL(bzla, term) \
  BZLA_ABORT(!bzla_node_is_bv_const(term), "expected bit-vector value")

#define BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla, term) \
  BZLA_ABORT(bzla_node_real_addr(term)->parameterized,   \
             "term must not be parameterized");

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
                     BitwuzlaSort codomain,
                     BitwuzlaSort domain[])
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
    dom[i] = BZLA_IMPORT_BOOLECTOR_SORT(domain[i]);
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
  BZLA_CHECK_ARG_STR_NOT_EMPTY(value);

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
  BZLA_CHECK_TERM_IS_BV_VAL(bzla, sign);
  BZLA_CHECK_TERM_IS_BV_VAL(bzla, exp);
  BZLA_CHECK_TERM_IS_BV_VAL(bzla, sig);
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
bitwuzla_mk_term(Bitwuzla *bitwuzla,
                 BitwuzlaKind kind,
                 uint32_t argc,
                 BitwuzlaTerm *args[])
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
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
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla, bzla_term);

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
  BZLA_CHECK_TERM_NOT_IS_PARAMETERIZED(bzla, bzla_term);

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

BitwuzlaTerm **
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

  return (BitwuzlaTerm **) bzla->failed_assumptions.start;
}

BitwuzlaTerm **
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
  return (BitwuzlaTerm **) bzla->unsat_core.start;
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
bitwuzla_print_model(Bitwuzla *bitwuzla, char *format, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(format);
  BZLA_CHECK_ARG_NOT_NULL(file);
  BZLA_CHECK_ARG_STR_NOT_EMPTY(format);
  BZLA_ABORT(strcmp(format, "btor") && strcmp(format, "smt2"),
             "invalid model output format: %s",
             format);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_CHECK_OPT_PRODUCE_MODELS(bzla);
  BZLA_CHECK_SAT(bzla, "print model");
  bzla_print_model(bzla, format, file);
}

void
bitwuzla_dump_smt2(Bitwuzla *bitwuzla, FILE *file)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  BZLA_CHECK_ARG_NOT_NULL(file);

  Bzla *bzla = BZLA_IMPORT_BITWUZLA(bitwuzla);
  BZLA_WARN(bzla->assumptions->count > 0,
            "dumping in incremental mode only captures the current state "
            "of the input formula without assumptions");
  bzla_dumpsmt_dump(bzla, file);
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

BitwuzlaSort
bitwuzla_sort_get_domain(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

BitwuzlaSort
bitwuzla_sort_get_codomain(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

uint32_t
bitwuzla_sort_bv_get_width(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

uint32_t
bitwuzla_sort_fun_get_arity(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_equal(Bitwuzla *bitwuzla, BitwuzlaSort sort0, BitwuzlaSort s1)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_array(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_bv(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_fp(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_fun(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_sort_is_rm(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

uint32_t
bitwuzla_sort_bv_get_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

uint32_t
bitwuzla_sort_fp_get_exp_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

uint32_t
bitwuzla_sort_fp_get_sig_size(Bitwuzla *bitwuzla, BitwuzlaSort sort)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

Bitwuzla *
bitwuzla_get_bitwuzla(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

const char *
bitwuzla_get_symbol(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

void
bitwuzla_set_symbol(Bitwuzla *bitwuzla, BitwuzlaTerm *term, const char *symbol)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

BitwuzlaSort
bitwuzla_get_sort(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value_one(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value_ones(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value_min_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv_value_max_signed(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value_pos_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value_neg_zero(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value_pos_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value_neg_inf(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp_value_nan(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_rm_value(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_array(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_bv(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fp(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_fun(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_rm(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_const(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}

bool
bitwuzla_is_var(Bitwuzla *bitwuzla, BitwuzlaTerm *term)
{
  BZLA_CHECK_ARG_NOT_NULL(bitwuzla);
  // TODO
}
