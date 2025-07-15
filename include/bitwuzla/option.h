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
  /*!
   * **Log level.**
   *
   * *Values:*
   *  - An unsigned integer value. [**default**: 0]
   */
  EVALUE(LOGLEVEL),
  /*!
   * **Model generation.**
   *
   * *SMT-LIB:* `:produce-models`
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PRODUCE_MODELS),
  /*!
   * **Interpolant generation.**
   *
   * *SMT-LIB:* `:produce-interpolants`
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PRODUCE_INTERPOLANTS),
  /*!
   * **Unsat assumptions generation.**
   *
   * *SMT-LIB:* `:produce-unsat-assumptions`
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PRODUCE_UNSAT_ASSUMPTIONS),
  /*!
   * **Unsat core generation.**
   *
   * *SMT-LIB:* `:produce-unsat-core`
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PRODUCE_UNSAT_CORES),
  /*!
   * **Seed for the random number generator.**
   *
   * *Values:*
   *  - **min**: 1
   *  - **max**: UINT32_MAX
   *  - **default**: 27644437
   */
  EVALUE(SEED),
  /*!
   * **Verbosity level.**
   *
   * *Values:*
   *  - An unsigned integer value <= 4. [**default**: 0]
   */
  EVALUE(VERBOSITY),

  /*!
   * **Time limit per satisfiability check in milliseconds.**
   *
   * A configuration value of 0 disables the time limit (no time limit).
   *
   * *Values:*
   *  - An unsigned 64-bit integer. [**default**: 0]
   */
  EVALUE(TIME_LIMIT_PER),
  /*!
   * **Memory limit per satisfiability check in MB.**
   *
   * A configuration value of 0 disables the memory limit (no memory limit).
   *
   * *Values:*
   *  - An unsigned 64-bit integer. [**default**: 0]
   */
  EVALUE(MEMORY_LIMIT),
  /*!
   * **Number of parallel threads.**
   *
   * *Values:*
   *  - **min**: 1
   *  - **max**: UINT64_MAX
   *  - **default**: 1
   */
  EVALUE(NTHREADS),

  /* ---------------- Bitwuzla-specific Options ----------------------------- */

  /*!
   * **Configure the bit-vector solver engine.**
   *
   * *Values:*
   * \verbatim embed:rst:leading-asterisk
   *  - **bitblast**: The classical bit-blasting approach. [**default**]
   *  - **prop:** Propagation-based local search, see :cite:`fmsd17,fmcad20`.
   *  - **preprop**: Sequential portfolio of ``bitblast`` and ``prop``.
   * \endverbatim
   *
   * @note Propagation-based local search is only able to determine
   *       satisfiability.
   */
  EVALUE(BV_SOLVER),
  /*!
   * **Rewrite level.**
   *
   * *Values:*
   *  - **0**: no rewriting
   *  - **1**: term level rewriting (only "cheap" rewrites)
   *  - **2**: term level rewriting (full) and preprocessing [**default**]
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(REWRITE_LEVEL),
  /*!
   * **Configure the SAT solver engine.**
   *
   * *Values:*
   *  - **cadical**:
   *    Use [CaDiCaL](https://github.com/arminbiere/cadical)
   *    as the backend SAT solver. [**default**]
   *  - **cms**:
   *    Use [CryptoMiniSat](https://github.com/msoos/cryptominisat)
   *    as the backend SAT solver.
   *  - **kissat**:
   *    Use [Kissat](https://github.com/arminbiere/kissat)
   *    as the backend SAT solver.
   */
  EVALUE(SAT_SOLVER),
  /*! **Print bit-vector abstraction as AIG in binary or ascii AIGER format.**
   *
   * Expects a filename (as string) as the configuration value.
   * The filename suffix determines whether binary (.aig) or ascii (.aag)
   * AIGER is used. A configuration value representing the empty string
   * disables the option.
   *
   * @note Incremental queries to the SAT solver will overwrite the file with
   *       the latest AIG.
   *
   * *Values:*
   *  - A string denoting the filename the AIGER output is written to.
   *    [**default:** ""]
   */
  EVALUE(WRITE_AIGER),
  /*!
   * **Print bit-vector abstraction as CNF in DIMACS format.**
   *
   * Expects a filename (as string) as the configuration value.
   * A configuration value representing the empty string disables the option.
   *
   * @note Incremental queries to the SAT solver will overwrite the file with
   *       the latest CNF.
   *
   * *Values:*
   *  - A string denoting the filename the DIMACS output is written to.
   *    [**default:** ""]
   */
  EVALUE(WRITE_CNF),

  /* ---------------- BV: Prop Engine Options (Expert) ---------------------- */

  /*!
   * **Propagation-based local search solver engine: Constant bits.**
   *
   * Enable/disable constant bit propagation in the propagation-based local
   * search engine (requires bit-blasting to AIG).
   *
   * \verbatim embed:rst:leading-asterisk
   * Our procedure for augmenting propagation-based local search with constant
   * bit information is described in :cite:`fmcad20`.
   * \endverbatim
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_CONST_BITS),
  /*!
   * **Propagation-based local search solver engine: Infer bounds.**
   *
   * When enabled, infer bounds for value computation for inequalities based on
   * satisfied top level inequalities.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_INFER_INEQ_BOUNDS),
  /*!
   * **Propagation-based local search solver engine: Number of propagations.**
   *
   * Configure the number of propagations used as a limit for the
   * propagation-based local search solver engine. No limit if 0.
   *
   * *Values:*
   *  - An unsigned integer value. [**default**: 0]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_NPROPS),
  /*!
   * **Propagation-based local search solver engine: Number of updates.**
   *
   * Configure the number of model value updates used as a limit for the
   * propagation-based local search solver engine. No limit if 0.
   *
   * *Values:*
   *  - An unsigned integer value. [**default**: 0]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_NUPDATES),
  /*!
   * **Propagation-based local search solver engine: Concat optimization.**
   *
   * Optimization for inverse value computation of inequalities over concat and
   * sign extension operands. When enabled, use optimized inverse value value
   * computation for inequalities over concats.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_OPT_LT_CONCAT_SEXT),
  /*!
   * **Propagation-based local search solver engine: Path selection.**
   *
   * Configure mode for path selection.
   *
   * *Values:*
   *  - **essential**:
   *    Select path based on essential inputs. [**default**]
   *  - **random**:
   *    Select path randomly.
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_PATH_SEL),
  /*!
   * **Propagation-based local search solver engine: Input probability.**
   *
   * Configure the probability for selecting random (over essential) input
   * when selecting the propagation path.
   *
   * *Values:*
   *  - An unsigned integer value <= 1000 (= 100%). [**default**: 10 (= 1%)]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_PROB_RANDOM_INPUT),
  /*!
   * **Propagation-based local search solver engine: Value probability.**
   *
   * Configure the probability for selcting an inverse value over a consistent
   * value (if an inverse value exists).
   *
   * *Values:*
   *  - An unsigned integer value <= 1000 (= 100%). [**default**: 990 (= 99%)]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_PROB_USE_INV_VALUE),
  /*!
   * **Propagation-based local search solver engine: Sign extension.**
   *
   * When enabled, treat concat nodes that represent sign extension natively as
   * sign extension.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::BV_SOLVER
   */
#else
  /*! @see BITWUZLA_OPT_BV_SOLVER
   */
#endif
  /*!
   * @warning This is an expert option to configure the `prop` bit-vector
   *          solver engine.
   */
  EVALUE(PROP_SEXT),

  /*!
   * **Abstraction module.**
   *
   * \verbatim embed:rst:leading-asterisk
   * Our bit-vector abstraction procedure is described in :cite:`cav24`.
   * \endverbatim
   *
   * *Values:*
   *  - **1**: enable
   *  - **0**: disable [**default**]
   *
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION),
  /*!
   * **Abstraction module. Minimum bit-vector term size.**
   *
   * Configure the minimum size for considered bit-vector operations to be
   * abstracted.
   *
   * *Values:*
   *  - **min**: >=3
   *  - **max**: UINT64_MAX
   *  - **default**: 32
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_BV_SIZE),
  /*!
   * **Abstraction module: Eager mode.**
   *
   * When enabled, violated refinement lemmas are added eagerly.
   *
   * *Values:*
   *  - **1**: enable
   *  - **0**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_EAGER_REFINE),
  /*!
   * **Abstraction module: Value instantiation limit.**
   *
   * Configure `n` for value instantiation limit `bit-width/<n>`. The value
   * instantiation limit defines the maximum number of value instantiation
   * lemmas to be added for an abstracted term. A configuration value of 0
   * disables adding value instantiation lemmas.
   *
   * *Values:*
   *  - An unsigned 64-bit integer. [**default:** 8]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_VALUE_LIMIT),
  /*!
   * **Abstraction module: Value instantiations only.**
   *
   * When enabled, only adds value instantiations.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_VALUE_ONLY),
  /*!
   * **Abstraction module: Abstract assertions.**
   *
   * When enabled, abstracts assertions.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_ASSERT),
  /*!
   * **Abstraction module: Assertion refinements.**
   *
   * Maximum number of assertion refinements added per check.
   *
   * *Values:*
   *  - An unsigned 64-bit integer value > 0. [**default:** 100]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_ASSERT_REFS),
  /*!
   * **Abstraction module: Use initial lemmas only.**
   *
   * Initial lemmas are those lemmas not generated through abduction.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_INITIAL_LEMMAS),
  /*!
   * **Abstraction module: Incrementally bit-blast bvmul and bvadd terms.**
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_INC_BITBLAST),
  /*!
   * **Abstraction module: Abstract bit-vector addition terms.**
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_BV_ADD),
  /*!
   * **Abstraction module: Abstract bit-vector multiplication terms.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_BV_MUL),
  /*!
   * **Abstraction module: Abstract bit-vector unsigned division terms.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_BV_UDIV),
  /*!
   * **Abstraction module: Abstract bit-vector unsigned remainder terms.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_BV_UREM),
  /*!
   * **Abstraction module: Abstract equality terms.**
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_EQUAL),
  /*!
   * **Abstraction module: Abstract ITE terms.**
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*! @see Option::ABSTRACTION
   */
#else
  /*! @see BITWUZLA_OPT_ABSTRACTION
   */
#endif
  /*!
   * @warning This is an expert option to configure the abstraction module.
   */
  EVALUE(ABSTRACTION_ITE),

  /*!
   * **Preprocessing.**
   *
   * When enabled, applies all enabled preprocessing passes.
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PREPROCESS),
  /*!
   * **Preprocessing: Find contradicting bit-vector ands.**
   */
#ifndef BITWUZLA_API_USE_C_ENUMS
  /*!
   * When enabled, substitutes contradicting nodes of kind Kind::BV_AND
   * with zero.
   */
#else
  /*!
   * When enabled, substitutes contradicting nodes of kind #BITWUZLA_KIND_BV_AND
   * with zero.
   */
#endif
  /*!
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PP_CONTRADICTING_ANDS),
  /*!
   * **Preprocessing: Eliminate bit-vector extracts on bit-vector constants.**
   *
   * When enabled, eliminates bit-vector extracts on constants.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PP_ELIM_BV_EXTRACTS),
  /*!
   * **Preprocessing: Eliminate bit-vector operators bvudiv and bvurem.**
   *
   * When enabled, eliminates bit-vector unsigned division and remainder
   * operation in terms of multiplication.
   *
   * *Values:*
   *  - **true**: enable
   *  - **false**: disable [**default**]
   */
  EVALUE(PP_ELIM_BV_UDIV),
  /*!
   * **Preprocessing: Embedded constraint substitution.**
   *
   * When enabled, substitutes assertions that occur as sub-expression in the
   * formula with their respective Boolean value.
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_EMBEDDED_CONSTR),
  /*!
   * **Preprocessing: AND flattening.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_FLATTEN_AND),
  /*!
   * **Preprocessing: Normalization.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_NORMALIZE),
  /*!
   * **Preprocessing: Boolean skeleton preprocessing.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_SKELETON_PREPROC),
  /*!
   * **Preprocessing: Variable substitution.**
   *
   * *Values:*
   *  * **true**: enable [**default**]
   *  * **false**: disable
   */
  EVALUE(PP_VARIABLE_SUBST),
  /*!
   * **Preprocessing: Variable substitution: Equality normalization.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_EQ),
  /*!
   * **Preprocessing: Variable substitution: Disequality Normalization.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_DISEQ),
  /*!
   * **Preprocessing: Variable substitution:
   *   Bit-Vector Inequality Normalization.**
   *
   * *Values:*
   *  - **true**: enable [**default**]
   *  - **false**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_BV_INEQ),

  /*!
   * **Debug: Recursive rewrite threshold.**
   *
   * Threshold for number of new nodes introduced for recursive call of
   * rewrite(). Prints a warning when number of newly introduced nodes is above
   * threshold.
   *
   * @warning This is an expert debug option.
   */
  EVALUE(DBG_RW_NODE_THRESH),
  /*!
   * **Debug: Formula size increase threshold.**
   *
   * Threshold for formula size increase after preprocessing in percent. Prints
   * a warning if formula size increase is above threshold.
   *
   * @warning This is an expert debug option.
   */
  EVALUE(DBG_PP_NODE_THRESH),
  /*!
   * **Debug: Check interpolants for each get-interpolant query.**
   *
   *  @warning This is an expert debug option.
   */
  EVALUE(DBG_CHECK_INTERPOLANT),
  /*!
   * **Debug: Check models for each satisfiable query.**
   *
   * @warning This is an expert debug option.
   */
  EVALUE(DBG_CHECK_MODEL),
  /*!
   * **Debug: Check unsat core for each unsatisfiable query.**
   *
   * @warning This is an expert debug option.
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
