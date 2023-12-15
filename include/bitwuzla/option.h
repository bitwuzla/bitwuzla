/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#if (!defined(BITWUZLA_API_USE_C_ENUMS)               \
     && !defined(BITWUZLA_API_OPTION_CPP_H_INCLUDED)) \
    || (defined(BITWUZLA_API_USE_C_ENUMS)             \
        && !defined(BITWUZLA_API_OPTION_C_H_INCLUDED))

#ifndef BITWUZLA_API_USE_C_ENUMS
namespace bitwuzla {
#define ENUM(name) class name
#define EVALUE(name) name
#else
#define ENUM(name) Bitwuzla##name
#define EVALUE(name) BITWUZLA_OPT_##name
#endif

/* -------------------------------------------------------------------------- */
/* Option                                                                     */
/* -------------------------------------------------------------------------- */

/**
 * The configuration options supported by Bitwuzla.
 *
 * Options that list string values can be configured via
 * `bitwuzla_set_option_str`. Options with integer configuration values are
 * configured via `bitwuzla_set_option`.
 *
 * For all options, the current configuration value can be queried via
 * `bitwuzla_get_option`.
 * Options with string configuration values internally represent these
 * values as enum values.
 * For these options, `bitwuzla_get_opiton` will return such an enum value.
 * Use `bitwuzla_get_option_str` to query enum options for the corresponding
 * string representation.
 */
enum ENUM(Option)
{
  /* ----------------- General Options -------------------------------------- */
  /*! **Log level.**
   *
   * Values:
   *  * An unsigned integer value. [**default**: 0]
   */
  EVALUE(LOGLEVEL),
  /*! **Model generation.**
   *
   * Values:
   *  * **1**: enable, generate model for assertions only
   *  * **2**: enable, generate model for all created terms
   *  * **0**: disable [**default**]
   *
   * @note This option cannot be enabled in combination with option
   *       `::EVALUE(PP_UNCONSTRAINED_OPTIMIZATION`.
   */
  EVALUE(PRODUCE_MODELS),
  /*! **Unsat assumptions generation.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   */
  EVALUE(PRODUCE_UNSAT_ASSUMPTIONS),
  /*! **Unsat core generation.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   */
  EVALUE(PRODUCE_UNSAT_CORES),
  /*! **Seed for random number generator.**
   *
   * Values:
   *  * An unsigned integer value. [**default**: 0]
   */
  EVALUE(SEED),
  /*! **Verbosity level.**
   *
   * Values:
   *  * An unsigned integer value <= 4. [**default**: 0]
   */
  EVALUE(VERBOSITY),

  /*! **Time limit in milliseconds per satisfiability check.**
   *
   * Values:
   *  * An unsigned integer for the time limit in milliseconds. [**default**: 0]
   */
  EVALUE(TIME_LIMIT_PER),
  /*! ** Memory limit in MB.**
   *
   * Values:
   *  * An unsigned integer for the memory limit in MB. [**default**: 0]
   */
  EVALUE(MEMORY_LIMIT),

  /* ---------------- Bitwuzla-specific Options ----------------------------- */

  /*! **Configure the bit-vector solver engine.**
   *
   * Values:
   *  * **bitblast**: The classical bit-blasting approach. [**default**]
   *  * **prop**: Propagation-based local search (sat only).
   *  * **preprop**: Sequential portfolio combination of bit-blasting and
   *                 propagation-based local search.
   */
  EVALUE(BV_SOLVER),
  /*! **Rewrite level.**
   *
   * Values:
   * * **0**: no rewriting
   * * **1**: term level rewriting
   * * **2**: term level rewriting and basic preprocessing
   * * **3**: term level rewriting and full preprocessing [**default**]
   *
   * @note Configuring the rewrite level after terms have been created
   *       is not allowed.
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(REWRITE_LEVEL),
  /*! **Configure the SAT solver engine.**
   *
   * Values:
   *  * **cadical**:
   *    [CaDiCaL](https://github.com/arminbiere/cadical) [**default**]
   *  * **cms**:
   *    [CryptoMiniSat](https://github.com/msoos/cryptominisat)
   *  * **kissat**:
   *    [Kissat](https://github.com/arminbiere/kissat)
   *  * **lingeling**:
   *    [Lingeling](https://github.com/arminbiere/lingeling)
   */
  EVALUE(SAT_SOLVER),

  /* ---------------- BV: Prop Engine Options (Expert) ---------------------- */

  /*! **Propagation-based local search solver engine:
   *    Constant bits.**
   *
   * Configure constant bit propagation (requires bit-blasting to AIG).
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_CONST_BITS),
  /*! **Propagation-based local search solver engine:
   *    Infer bounds for inequalities for value computation.**
   *
   * When enabled, infer bounds for value computation for inequalities based on
   * satisfied top level inequalities.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_INFER_INEQ_BOUNDS),
  /*! **Propagation-based local search solver engine:
   *    Number of propagations.**
   *
   * Configure the number of propagations used as a limit for the
   * propagation-based local search solver engine. No limit if 0.
   *
   * Values:
   *  * An unsigned integer value. [**default**: 0]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_NPROPS),
  /*! **Propagation-based local search solver engine:
   *    Number of updates.**
   *
   * Configure the number of model value updates used as a limit for the
   * propagation-based local search solver engine. No limit if 0.
   *
   * Values:
   *  * An unsigned integer value. [**default**: 0]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_NUPDATES),
  /*! **Propagation-based local search solver engine:
   *    Optimization for inverse value computation of inequalities over
   *    concat and sign extension operands.**
   *
   * When enabled, use optimized inverse value value computation for
   * inequalities over concats.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_OPT_LT_CONCAT_SEXT),
  /*! **Propagation-based local search solver engine:
   *    Path selection.**
   *
   * Configure mode for path selection.
   *
   * Values:
   *  * **essential**:
   *    Select path based on essential inputs. [default]
   *  * **random**:
   *    Select path randomly.
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PATH_SEL),
  /*! **Propagation-based local search solver engine:
   *    Probability for selecting random input.**
   *
   * Configure the probability with which to select a random input instead of
   * an essential input when selecting the path.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%). [**default**: 0]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_RANDOM_INPUT),
  /*! **Propagation-based local search solver engine:
   *    Probability for inverse values.**
   *
   * Configure the probability with which to choose an inverse value over a
   * consistent value when aninverse value exists.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%). [**default**: 990]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_USE_INV_VALUE),
  /*! **Propagation-based local search solver engine:
   *    Value computation for sign extension.**
   *
   * When enabled, detect sign extension operations (are rewritten on
   * construction) and use value computation for sign extension.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_SEXT),
  /*! **Propagation-based local search solver engine:
   *    Local search specific normalization.**
   *
   * When enabled, perform normalizations for local search, on the local search
   * layer (does not affect node layer).
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_NORMALIZE),

  /*! **Preprocessing**
   *
   * When enabled, applies all enabled preprocessing passes.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PREPROCESS),
  /*! **Preprocessing: Find contradicting bit-vector ands**
   *
   * When enabled, substitutes contradicting nodes of kind #BV_AND with zero.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_CONTRADICTING_ANDS),
  /*! **Preprocessing: Eliminate bit-vector extracts on bit-vector constants**
   *
   * When enabled, eliminates bit-vector extracts on constants.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   */
  EVALUE(PP_ELIM_BV_EXTRACTS),
  /*! **Preprocessing: Embedded constraint substitution**
   *
   * When enabled, substitutes assertions that occur as sub-expression in the
   * formula with their respective Boolean value.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_EMBEDDED_CONSTR),
  /*! **Preprocessing: AND flattening**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_FLATTEN_AND),
  /*! **Preprocessing: Normalization**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_NORMALIZE),
  /*! **Preprocessing: Normalization: Enable share awareness normlization**
   *
   * When enabled, this disables normalizations that may yield blow-up on the
   * bit-level.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_NORMALIZE_SHARE_AWARE),
  /*! **Preprocessing: Boolean skeleton preprocessing**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_SKELETON_PREPROC),
  /*! **Preprocessing: Variable substitution**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_VARIABLE_SUBST),
  /*! **Preprocessing: Variable substitution: Equality Normalization**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_EQ),
  /*! **Preprocessing: Variable substitution: Disequality Normalization**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_DISEQ),
  /*! **Preprocessing: Variable substitution: Bit-Vector Inequality
   * Normalization**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_BV_INEQ),

  /*! **Debug:
   *    Threshold for number of new nodes introduced for recursive call of
   *    rewrite(). **
   *
   *  Prints a warning number of newly introduced nodes is above threshold.
   *
   *  @warning This is an expert debug option.
   */
  EVALUE(DBG_RW_NODE_THRESH),
  /*! **Debug:
   *    Threshold for formula size increase after preprocessing in percent. **
   *
   *  Prints a warning if formula size increase is above threshold.
   *
   *  @warning This is an expert debug option.
   */
  EVALUE(DBG_PP_NODE_THRESH),
  /*! **Debug: Check models for each satisfiable query. **
   *
   *  @warning This is an expert debug option.
   */
  EVALUE(DBG_CHECK_MODEL),
  /*! **Debug: Check unsat core for each unsatisfiable query. **
   *
   *  @warning This is an expert debug option.
   */
  EVALUE(DBG_CHECK_UNSAT_CORE),

#ifndef DOXYGEN_SKIP
  EVALUE(NUM_OPTS),
#endif
};

#ifdef BITWUZLA_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum BitwuzlaOption BitwuzlaOption;
#endif
#endif

#ifndef BITWUZLA_API_USE_C_ENUMS
}  // namespace bitwuzla
#endif

#undef EVALUE
#undef ENUM

#endif

#ifndef BITWUZLA_API_USE_C_ENUMS
#ifndef BITWUZLA_API_OPTION_CPP_H_INCLUDED
#define BITWUZLA_API_OPTION_CPP_H_INCLUDED
#endif
#else
#ifndef BITWUZLA_API_OPTION_C_H_INCLUDED
#define BITWUZLA_API_OPTION_C_H_INCLUDED
#endif
#endif
