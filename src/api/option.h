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
  /*! **Incremental solving.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   * @note
   * * Enabling this option turns off some optimization techniques.
   * * Enabling/disabling incremental solving after bitwuzla_check_sat()
   *   has been called is not supported.
   * * This option cannot be enabled in combination with option
   *   `::EVALUE(PP_UNCONSTRAINED_OPTIMIZATION`.
   */
  EVALUE(INCREMENTAL),
  /*! **Log level.**
   *
   * Values:
   *  * An unsigned integer value (**default**: 0).
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
   *  * An unsigned integer value (**default**: 0).
   */
  EVALUE(SEED),
  /*! **Verbosity level.**
   *
   * Values:
   *  * An unsigned integer value <= 4 (**default**: 0).
   */
  EVALUE(VERBOSITY),

  /* ---------------- Bitwuzla-specific Options ----------------------------- */

  // TODO: doc
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
   *  * **cadical** [**default**]:
   *    [CaDiCaL](https://github.com/arminbiere/cadical)
   *  * **cms**:
   *    [CryptoMiniSat](https://github.com/msoos/cryptominisat)
   *  * **gimsatul**:
   *    [Gimsatul](https://github.com/arminbiere/gimsatul)
   *  * **kissat**:
   *    [Kissat](https://github.com/arminbiere/kissat)
   *  * **lingeling**:
   *    [Lingeling](https://github.com/arminbiere/lingeling)
   */
  EVALUE(SAT_SOLVER),
  /*! **Enable SMT-COMP mode.**
   *
   * Parser only option. Only effective when an SMT2 input file is parsed.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option.
   */
  EVALUE(SMT_COMP_MODE),

  /* ---------------- BV: Prop Engine Options (Expert) ---------------------- */

  /*! **Propagation-based local search solver engine:
   *    Constant bits.**
   *
   * Configure constant bit propagation (requries bit-blasting to AIG).
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
   *  * An unsigned integer value (**default**: 0).
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
   *  * An unsigned integer value (**default**: 0).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_NUPDATES),
  /*! **Propagation-based local search solver engine:
   *    Path selection.**
   *
   * Configure mode for path selection.
   *
   * Values:
   *  * **essential** [default]:
   *    Select path based on essential inputs.
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
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 0).
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
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 990).
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

  /*! **Preprocessing: Find contradicting bit-vector ands**
   *
   * When enabled, substitutes contradicting nodes of kind #BV_AND with zero.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_CONTRADICTING_ANDS),
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
  /*! **Preprocessing: Variable substitution: Bit-Vector Unsigned Inequality
   * Normalization**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PP_VARIABLE_SUBST_NORM_BVULT),

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

/* ================ Old Options =========================================== */

#if 0
  /*! **Configure the solver engine.**
   *
   * Values:
   *  * **aigprop**:
   *    The propagation-based local search QF_BV engine that operates on the
   *    bit-blasted formula (the AIG circuit layer).
   *  * **fun** [**default**]:
   *    The default engine for all combinations of QF_AUFBVFP, uses lemmas on
   *    demand for QF_AUFBVFP, and eager bit-blasting (optionally with local
   *    searchin a sequential portfolio) for QF_BV.
   *  * **prop**:
   *    The propagation-based local search QF_BV engine.
   *  * **sls**:
   *     The stochastic local search QF_BV engine.
   *  * **quant**:
   *    The quantifier engine.
   */
  EVALUE(ENGINE),

  /*! **Use non-zero exit codes for sat and unsat results.**
   *
   * When enabled, use Bitwuzla exit codes:
   * * `::BITWUZLA_SAT`
   * * `::BITWUZLA_UNSAT`
   * * `::BITWUZLA_UNKNOWN`
   *
   * When disabled, return 0 on success (sat, unsat, unknown), and a non-zero
   * exit code otherwise.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(EXIT_CODES),

  /*! **Configure input file format.**
   *
   * If unspecified, Bitwuzla will autodetect the input file format.
   *
   * Values:
   *  * **none** [**default**]:
   *    Auto-detect input file format.
   *  * **btor**:
   *    \verbatim embed:rst:leading-asterisk
   *    BTOR format :cite:`btor`
   *    \endverbatim
   *  * **btor2**:
   *    \verbatim embed:rst:leading-asterisk
   *    BTOR2 format :cite:`btor2`
   *    \endverbatim
   *  * **smt2**:
   *    \verbatim embed:rst:leading-asterisk
   *    SMT-LIB v2 format :cite:`smtlib2`
   *    \endverbatim
   */
  EVALUE(INPUT_FORMAT),

  /*! **Configure output number format for bit-vector values.**
   *
   * If unspecified, Bitwuzla will use BTOR format.
   *
   * Values:
   *  * **aiger**:
   *    \verbatim embed:rst:leading-asterisk
   *    AIGER ascii format :cite:`aiger`
   *    \endverbatim
   *  * **aigerbin**:
   *    \verbatim embed:rst:leading-asterisk
   *    AIGER binary format :cite:`aiger`
   *    \endverbatim
   *  * **btor** [**default**]:
   *    \verbatim embed:rst:leading-asterisk
   *    BTOR format :cite:`btor`
   *    \endverbatim
   *  * **smt2**:
   *    \verbatim embed:rst:leading-asterisk
   *    SMT-LIB v2 format :cite:`smtlib2`
   *    \endverbatim
   */
  EVALUE(OUTPUT_FORMAT),

  /*! **Configure output number format for bit-vector values.**
   *
   * If unspecified, Bitwuzla will use binary representation.
   *
   * Values:
   *  * **bin** [**default**]:
   *  Binary number format.
   *  * **hex**:
   *  Hexadecimal number format.
   *  * **dec**:
   *  Decimal number format.
   */
  EVALUE(OUTPUT_NUMBER_FORMAT),

  /*! **Pretty printing.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   */
  EVALUE(PRETTY_PRINT),

  /*! **Print DIMACS.**
   *
   * Print the CNF sent to the SAT solver in DIMACS format to stdout.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   */
  EVALUE(PRINT_DIMACS),

  /* -------------- Rewriting/Preprocessing Options (Expert) --------------- */

  /*! **Ackermannization preprocessing.**
   *
   * Eager addition of Ackermann constraints for function applications.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_ACKERMANN),

  /*! **Beta reduction preprocessing.**
   *
   * Eager elimination of lambda terms via beta reduction.
   *
   * Values:
   *  * **none** [**default**]:
   *    Disable beta reduction preprocessing.
   *  * **fun**:
   *    Only beta reduce functions that do not represent array stores.
   *  * **all**:
   *    Only beta reduce all functions, including array stores.
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_BETA_REDUCE),

  /*! **Eliminate bit-vector extracts (preprocessing).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_ELIMINATE_EXTRACTS),

  /*! **Eliminate ITEs (preprocessing).**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_ELIMINATE_ITES),

  /*! **Extract lambdas (preprocessing).**
   *
   * Extraction of common array patterns as lambda terms.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_EXTRACT_LAMBDAS),

  /*! **Merge lambda terms (preprocessing).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_MERGE_LAMBDAS),

  /*! **Non-destructive term substitutions.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_NONDESTR_SUBST),

  /*! **Normalize bit-vector addition (global).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_NORMALIZE_ADD),

  /*! **Boolean skeleton preprocessing.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_SKELETON_PREPROC),

  /*! **Unconstrained optimization (preprocessing).**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_UNCONSTRAINED_OPTIMIZATION),

  /*! **Variable substitution preprocessing.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure preprocessing.
   */
  EVALUE(PP_VAR_SUBST),

  /*! **Propagate bit-vector extracts over arithmetic bit-vector operators.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_EXTRACT_ARITH),

  /*! **Normalize bit-vector operations.**
   *
   * Normalize bit-vector addition, multiplication and bit-wise and.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_NORMALIZE),

  /*! **Normalize bit-vector addition (local).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_NORMALIZE_ADD),

  /*! **Simplify constraints on construction.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_SIMPLIFY_CONSTRAINTS),

  /*! **Eliminate bit-vector SLT nodes.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_SLT),

  /*! **Sort the children of AIG nodes by id.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_SORT_AIG),

  /*! **Sort the children of adder and multiplier circuits by id.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_SORT_AIGVEC),

  /*! **Sort the children of commutative operations by id.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure rewriting.
   */
  EVALUE(RW_SORT_EXP),

  /* --------------------- Fun Engine Options (Expert) --------------------- */

  /*! **Function solver engine:
   *    Dual propagation optimization.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the fun solver engine.
   */
  EVALUE(FUN_DUAL_PROP),

  /*! **Function solver engine:
   *    Assumption order for dual propagation optimization.**
   *
   * Set order in which inputs are assumed in the dual propagation clone.
   *
   * Values:
   *  * **just** [**default**]:
   *    Order by score, highest score first.
   *  * **asc**:
   *    Order by input id, ascending.
   *  * **desc**:
   *    Order by input id, descending.
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_DUAL_PROP_QSORT),

  /*! **Function solver engine:
   *    Eager lemmas.**
   *
   * Configure mode for eager lemma generation.
   *
   * Values:
   *  * **none**:
   *    Do not generate lemmas eagerly (generate one single lemma per
   *    refinement iteration).
   *  * **conf** [**default**]:
   *    Only generate lemmas eagerly until the first conflict dependent on
   *    another conflict is found.
   *  * **all**:
   *    In each refinement iteration, generate lemmas for all conflicts.
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_EAGER_LEMMAS),

  /*! **Function solver engine:
   *    Lazy synthesis.**
   *
   * Configure lazy synthesis (to bit-level) of bit-vector expressions.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_LAZY_SYNTHESIZE),

  /*! **Function solver engine:
   *    Justification optimization.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_JUST),

  /*! **Function solver engine:
   *    Justification optimization heuristic.**
   *
   * Configure heuristic to determine path selection for justification
   * optimization.
   *
   * Values:
   *  * **applies** [**default**]:
   *    Choose branch with minimum number of applies.
   *  * **depth**:
   *    Choose branch with minimum depth.
   *  * **left**:
   *    Always choose left branch.
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_JUST_HEURISTIC),

  /*! **Function solver engine:
   *    Propagation-based local search sequential portfolio.**
   *
   * When function solver engine is enabled, configure propagation-based local
   * search solver engine as preprocessing step within sequential portfolio
   * setting.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_PREPROP),
  EVALUE(FUN_PREPROPOLD),

  /*! **Function solver engine:
   *    Stochastic local search sequential portfolio.**
   *
   * When function solver engine is enabled, configure stochastic local
   * search solver engine as preprocessing step within sequential portfolio
   * setting.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_PRESLS),

  /*! **Function solver engine:
   *    Represent store as lambda.**
   *
   * Represent array stores as lambdas.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the func solver engine.
   */
  EVALUE(FUN_STORE_LAMBDAS),

  /* --------------------- SLS Engine Options (Expert) --------------------- */

  /*! **Stochastic local search solver engine:
   *    Justification-based path selection.**
   *
   * Configure justification-based path selection for SLS engine.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_JUST),

  /*! **Stochastic local search solver engine:
   *    Group-wise moves.**
   *
   * Configure group-wise moves for SLS engine. When enabled, rather than
   * changing the assignment of one single candidate variable, all candidates
   * are set at the same time (using the same strategy).
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_GW),

  /*! **Stochastic local search solver engine:
   *    Incremental move test.**
   *
   * Configure that during best move selection, the previous best neighbor
   * for the current candidate is used for neighborhood exploration rather
   * than its current assignment.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_INC_MOVE_TEST),

  /*! **Stochastic local search solver engine:
   *    Propagation moves.**
   *
   * Configure propagation moves, chosen with a ratio of number of propagation
   * moves `::EVALUE(SLS_MOVE_PROP_NPROPS` to regular SLS moves
   * `::EVALUE(SLS_MOVE_PROP_NSLSS`.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_PROP),

  /*! **Stochastic local search solver engine:
   *    Force random walks.**
   *
   * Configure that random walks are forcibly chosen as recovery moves in case
   * of conflicts when a propagation move is performed (rather than performing
   * a regular SLS move).
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_PROP_FORCE_RW),

  /*! **Stochastic local search solver engine:
   *    Number of propagation moves.**
   *
   * Configure the number of propagation moves to be performed when propagation
   * moves are enabled. Propagation moves are chosen with a ratio of
   * `::EVALUE(SLS_MOVE_PROP_NPROPS` to
   * `::EVALUE(SLS_MOVE_PROP_NSLSS`.
   *
   * Values:
   *  * An unsigned integer value (**default**: 1)
   *
   * @see
   *   * EVALUE(SLS_MOVE_PROP
   *   * EVALUE(SLS_MOVE_PROP_NSLSS
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_PROP_NPROPS),

  /*! **Stochastic local search solver engine:
   *    Number of regular SLS moves.**
   *
   * Configure the number of regular SLS moves to be performed when propagation
   * moves are enabled. Propagation moves are chosen with a ratio of
   * `::EVALUE(SLS_MOVE_PROP_NPROPS` to
   * `::EVALUE(SLS_MOVE_PROP_NSLSS`.
   *
   * Values:
   *  * An unsigned integer value (**default**: 1)
   *
   * @see
   *   * EVALUE(SLS_MOVE_PROP
   *   * EVALUE(SLS_MOVE_PROP_NPROPS
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_PROP_NSLSS),

  /*! **Stochastic local search solver engine:
   *    Randomize all candidates.**
   *
   * Configure the randomization of all candidate variables (rather than just
   * a single randomly selected one) in case no best move has been found.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_RAND_ALL),

  /*! **Stochastic local search solver engine:
   *    Randomize bit ranges.**
   *
   * Configure the randomization of bit ranges (rather than all bits) of
   * candidate variable(s) in case no best move has been found.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_RAND_RANGE),

  /*! **Stochastic local search solver engine:
   *    Random walk.**
   *
   * Configure random walk moves, where one out of all possible neighbors is
   * randomly selected (with given probability
   * `::EVALUE(SLS_PROB_MOVE_RAND_WALK`) for a randomly selected
   * candidate variable.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   * @see
   *   * EVALUE(SLS_MOVE_PROB_RAND_WALK
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_RAND_WALK),

  /*! **Stochastic local search solver engine:
   *    Range-wise bit-flip moves.**
   *
   * Configure range-wise bit-flip moves for SLS engine. When enabled, try
   * range-wise bit-flips when selecting moves, where bits within all ranges
   * from 2 to the bit-width (starting from the LSB) are flipped at once.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_RANGE),

  /*! **Stochastic local search solver engine:
   *    Segment-wise bit-flip moves.**
   *
   * Configure range-wise bit-flip moves for SLS engine. When enabled, try
   * segment-wise bit-flips when selecting moves, where bits within segments
   * of multiples of 2 are flipped at once.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_MOVE_SEGMENT),

  /*! **Stochastic local search solver engine:
   *    Probability for random walks.**
   *
   * Configure the probability with which a random walk is chosen if random
   * walks are enabled.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 100)
   *
   * @see
   *   * EVALUE(SLS_MOVE_RAND_WALK
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_PROB_MOVE_RAND_WALK),

  /*! **Stochastic local search solver engine:
   *    Number of bit flips.**
   *
   * Configure the number of bit flips used as a limit for the SLS engine.
   *
   * Values:
   *  * An unsigned integer value, no limit if 0 (**default**: 0).
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_NFLIPS),

  /*! **Stochastic local search solver engine:
   *    Move strategy.**
   *
   * Configure the move selection strategy for the SLS engine.
   *
   * Values:
   *  * **best** [**default**]:
   *    Choose best score improving move.
   *  * **walk**:
   *    Choose random walk weighted by score.
   *  * **first**:
   *    Choose first best move (no matter if any other move is better).
   *  * **same**:
   *    Determine move as best move even if its score is not better but the
   *    same as the score of the previous best move.
   *  * **prop**:
   *    Choose propagation move (and recover with SLS move in case of conflict).
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_STRATEGY),

  /*! **Stochastic local search solver engine:
   *    Restarts.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_USE_RESTARTS),

  /*! **Stochastic local search solver engine:
   *    Bandit scheme.**
   *
   * Configure bandit scheme heuristic for selecting root constraints.
   * If disabled, root constraints are selected randomly.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the sls solver engine.
   */
  EVALUE(SLS_USE_BANDIT),

  /* -------------------- Prop Engine Options (Expert) --------------------- */

  /*! **Propagation-based local search solver engine:
   *    Value computation for xor.**
   *
   * When enabled, detect arithmetic right shift operations (are rewritten on
   * construction) and use value computation for ashr.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_ASHR),

  /*! **Propagation-based local search solver engine:
   *    Domain propagators.**
   *
   * Configure the use of domain propagators for determining constant bits
   * (instead of bit-blastin to AIG).
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_CONST_DOMAINS),

  /*! **Propagation-based local search solver engine:
   *    Entailed propagations.**
   *
   * Maintain a work queue with entailed propagations.
   * If enabled, propagations from this queue are propagated before randomly
   * choosing a yet unsatisfied path from the root.
   *
   * Values:
   *
   *  * **off** [**default**]:
   *    Disable strategy.
   *  * **all**:
   *    Propagate all entailed propagations.
   *  * **first**:
   *    Process only the first entailed propagation.
   *  * **last**:
   *    Process only the last entailed propagation.
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_ENTAILED),

  /*! **Propagation-based local search solver engine:
   *    Delta for flipping ite conditions with constant branches.**
   *
   * Configure the delta by which `::EVALUE(PROP_PROB_FLIP_COND_CONST` is
   * decreased or increased after a limit
   * `::EVALUE(PROP_FLIP_COND_CONST_NPATHSEL` is reached.
   *
   * Values:
   *  * A signed integer value (**default**: 100).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_FLIP_COND_CONST_DELTA),

  /*! **Propagation-based local search solver engine:
   *    Limit for flipping ite conditions with constant branches.**
   *
   * Configure the limit for how often the path to the condition for ite
   * operations with constant branches may be selected before
   * `::EVALUE(PROP_PROB_FLIP_COND_CONST` is decreased or increased by
   * `::EVALUE(PROP_FLIP_COND_CONST_DELTA`.
   *
   * Values:
   *  * A signed integer value (**default**: 500).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_FLIP_COND_CONST_NPATHSEL),

  /*! **Propagation-based local search solver engine:
   *    No move on conflict.**
   *
   * When enabled, no move is performed when running into a conflict during
   * value computation.
   *
   * @note This is the default behavior for the SLS engine when propagation
   *       moves are enabled, where a conflict triggers a recovery by means
   *       of a regular SLS move.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_NO_MOVE_ON_CONFLICT),

  /*! **Propagation-based local search solver engine:
   *    Probability for producing inverse rather than consistent values.**
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 0).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_FALLBACK_RANDOM_VALUE),

  /*! **Propagation-based local search solver engine:
   *    Probability for flipping one of the don't care bits for ands.**
   *
   * Configure the probability with which to keep the current assignement of
   * the operand to a bit-vector and with max one bit flipped (rather than
   * fully randomizing the assignment) when selecting an inverse or consistent
   * value.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 0).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_AND_FLIP),

  /*! **Propagation-based local search solver engine:
   *    Probability for using the current assignment with one bit flipped for
   *    equalities.**
   *
   * Configure the probability with which the current assignment of an operand
   * to a disequality is kept with just a single bit flipped (rather than fully
   * randomizing the assignment) when selecting an inverse or consistent value.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 0).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_EQ_FLIP),

  /*! **Propagation-based local search solver engine:
   *    Probability for flipping ite condition.**
   *
   * Configure the probability with which to select the path to the condition
   * (in case of an ite operation) rather than the enabled branch during down
   * propagation).
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 100).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_FLIP_COND),

  /*! **Propagation-based local search solver engine:
   *    Probability for flipping ite condition with constant branches.**
   *
   * Configure the probability with which to select the path to the condition
   * (in case of an ite operation) rather than the enabled branch during down
   * propagation) if either the 'then' or 'else' branch is constant.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 100).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_FLIP_COND_CONST),

  /*! **Propagation-based local search solver engine:
   *    Probability for flipping one of the don't care bits for extracts.**
   *
   * Configure the probability with which to flip one of the don't care bits of
   * the current assignment of the operand to a bit-vector extract (when the
   * asignment is kept) when selecting an inverse or consistent value.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 0).
   *
   * @see
   *   * EVALUE(PROP_PROB_SLICE_KEEP_DC
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_SLICE_FLIP),

  /*! **Propagation-based local search solver engine:
   *    Probability for keeping the value of don't care bits for extracts.**
   *
   * Configure the probability with which to keep the current value of don't
   * care bits of an extract operation (rather than fully randomizing them)
   * when selecting an inverse or consistent value.
   *
   * Values:
   *  * An unsigned integer value <= 1000 (= 100%) (**default**: 500).
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_PROB_SLICE_KEEP_DC),

  /*! **Propagation-based local search solver engine:
   *    Bandit scheme.**
   *
   * Configure bandit scheme heuristic for selecting root constraints.
   * If enabled, root constraint selection via bandit scheme is based on a
   * scoring scheme similar to the one used in the SLS engine.
   * If disabled, root constraints are selected randomly.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_USE_BANDIT),

  /*! **Propagation-based local search solver engine:
   *    Inverse value computation for inequalities over concats.**
   *
   * When enabled, use special inverse value computation for inequality over
   * concats.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_USE_INV_LT_CONCAT),

  /*! **Propagation-based local search solver engine:
   *    Restarts.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_USE_RESTARTS),

  /*! **Propagation-based local search solver engine:
   *    Skip if no progress.**
   *
   * When enabled, moves that make no progress, that is, that produce a target
   * value that is the seame as the current assignment of a variable, are
   * skipped.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_SKIP_NO_PROGRESS),

  /*! **Propagation-based local search solver engine:
   *    Value computation for xor.**
   *
   * When enabled, detect xor operations (are rewritten on construction) and
   * use value computation for xor.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the prop solver engine.
   */
  EVALUE(PROP_XOR),

  /* ------------------- AigProp Engine Options (Expert) ------------------- */

  /*! **AIG-level propagation-based local search solver engine:
   *    Number of propagations.**
   *
   * Configure the number of propagations used as a limit for the
   * propagation-based local search solver engine. No limit if 0.
   *
   * Values:
   *  * An unsigned integer value (**default**: 0).
   *
   *  @warning This is an expert option to configure the aigprop solver engine.
   */
  EVALUE(AIGPROP_NPROPS),

  /*! **AIG-level propagation-based local search solver engine:
   *    Bandit scheme.**
   *
   * Configure bandit scheme heuristic for selecting root constraints.
   * If enabled, root constraint selection via bandit scheme is based on a
   * scoring scheme similar to the one used in the SLS engine.
   * If disabled, root constraints are selected randomly.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the aigprop solver engine.
   */
  EVALUE(AIGPROP_USE_BANDIT),

  /*! **AIG-level propagation-based local search solver engine:
   *    Restarts.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option to configure the aigprop solver engine.
   */
  EVALUE(AIGPROP_USE_RESTARTS),

  /* ----------------- Quantifier Engine Options (Expert) -0----------------- */
  /*! **Quantifier solver engine:
   *    Skolem function synthesis.**
   *
   * Configure the generalization of Skolem functions via enumerative learning.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the quantifier solver
   *  engine.
   */
  EVALUE(QUANT_SYNTH_SK),

  /*! **Quantifier solver engine:
   *    Quantifier instantiation synthesis.**
   *
   * Configure the generalization of quantifier instantiations via enumerative
   * learning.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the quantifier solver
   *  engine.
   */
  EVALUE(QUANT_SYNTH_QI),

  /*! **Quantifier solver engine:
   *    Skolemization.**
   *
   * Use uninterpreted functions for Skolemization instead of fresh constants.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the quantifier solver
   *  engine.
   */
  EVALUE(QUANT_SKOLEM_UF),

  /*! **Quantifier solver engine:
   *    Eager Skolemization.**
   *
   * Eagerly apply Skolemization.
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the quantifier solver
   *  engine.
   */
  EVALUE(QUANT_EAGER_SKOLEM),

  /*! **Quantifier solver engine:
   *    Model-based Quantifier Instantiation.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option to configure the quantifier solver
   *  engine.
   */
  EVALUE(QUANT_MBQI),

  EVALUE(QUANT_MODE),

  /* ------------------------ Other Expert Options ------------------------- */

  /*! **Check model (debug only).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option.
   */
  EVALUE(CHECK_MODEL),

  /*! **Check result when unconstrained optimization is enabled (debug only).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option.
   */
  EVALUE(CHECK_UNCONSTRAINED),

  /*! **Check unsat assumptions (debug only).**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option.
   */
  EVALUE(CHECK_UNSAT_ASSUMPTIONS),

  /*! **Interpret sorts introduced with declare-sort as bit-vectors of given
   *    width.**
   *
   * Disabled if zero.
   *
   * Values:
   *  * An unsigned integer value (**default**: 0).
   *
   *  @warning This is an expert option.
   */
  EVALUE(DECLSORT_BV_WIDTH),

  /*! **Share partial models determined via local search with bit-blasting
   *    engine.**
   *
   * This option is only effective when local search engines are combined with
   * the bit-blasting engine in a sequential portfolio.
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option.
   */
  EVALUE(LS_SHARE_SAT),

  /*! **Interactive parsing mode.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option.
   */
  EVALUE(PARSE_INTERACTIVE),

  /*! **Use CaDiCaL's freeze/melt.**
   *
   * Values:
   *  * **1**: enable
   *  * **0**: disable [**default**]
   *
   *  @warning This is an expert option.
   */
  EVALUE(SAT_ENGINE_CADICAL_FREEZE),

  /*! **Lingeling fork mode.**
   *
   * Values:
   *  * **1**: enable [**default**]
   *  * **0**: disable
   *
   *  @warning This is an expert option.
   */
  EVALUE(SAT_ENGINE_LGL_FORK),

  /*! **Number of threads to use in the SAT solver.**
   *
   * This option is only effective for SAT solvers with support for
   * multi-threading.
   *
   * Values:
   *  * An unsigned integer value > 0 (**default**: 1).
   *
   *  @warning This is an expert option.
   */
  EVALUE(SAT_ENGINE_N_THREADS),
#endif

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
