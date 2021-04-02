/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLATYPES_H_INCLUDED
#define BZLATYPES_H_INCLUDED

typedef struct Bzla Bzla;
typedef struct BzlaNode BzlaNode;

enum BzlaSolverResult
{
  BZLA_RESULT_SAT     = 10,
  BZLA_RESULT_UNSAT   = 20,
  BZLA_RESULT_UNKNOWN = 0,
};

typedef enum BzlaSolverResult BzlaSolverResult;

/* public API types */
typedef struct BoolectorNode BoolectorNode;

typedef struct BoolectorAnonymous BoolectorAnonymous;

typedef BoolectorAnonymous* BoolectorSort;

/* --------------------------------------------------------------------- */
/* Boolector options                                                     */
/* --------------------------------------------------------------------- */

// clang-format off
enum BzlaOption
{
  /* --------------------------------------------------------------------- */
  /*!
    **General Options:**
   */
  /* --------------------------------------------------------------------- */
  /*!
    * **BZLA_OPT_MODEL_GEN**

      | Enable (``value``: 1 or 2) or disable (``value``: 0) generation of a
        model for satisfiable instances.
      | There are two modes for model generation:

      * generate model for asserted expressions only (``value``: 1)
      * generate model for all expressions (``value``: 2)
  */
  BZLA_OPT_MODEL_GEN,

  /*!
    * **BZLA_OPT_INCREMENTAL**

      | Enable (``value``: 1) incremental mode.
      | Note that incremental usage turns off some optimization techniques.
        Disabling incremental usage is currently not supported.
  */
  BZLA_OPT_INCREMENTAL,

  /*!
    * **BZLA_OPT_INPUT_FORMAT**

      | Force input file format.
      | If unspecified, Boolector automatically detects the input file format
        while parsing.

      * BZLA_INPUT_FORMAT_BTOR:
        `BTOR <http://fmv.jku.at/papers/BrummayerBiereLonsing-BPR08.pdf>`_ format
      * BZLA_INPUT_FORMAT_BTOR2:
        `BTOR2 <http://fmv.jku.at/papers/NiemetzPreinerWolfBiere-CAV18.pdf>`_ format
      * BZLA_INPUT_FORMAT_SMT2:
        `SMT-LIB v2 <http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.0-r12.09.09.pdf>`_ format
  */

  BZLA_OPT_INPUT_FORMAT,
  /*!
    * **BZLA_OPT_OUTPUT_NUMBER_FORMAT**

      | Force output number format.

      * BZLA_OUTPUT_BASE_BIN [default]:
        binary
      * BZLA_OUTPUT_BASE_HEX:
        hexa-decimal
      * BZLA_OUTPUT_BASE_DEC:
        decimal
  */
  BZLA_OPT_OUTPUT_NUMBER_FORMAT,

  /*!
    * **BZLA_OPT_OUTPUT_FORMAT**

      | Force output file format (``value``: BZLA_: -1, `SMT-LIB v1`_: 1,
        `SMT-LIB v2`_: 2).

      * BZLA_OUTPUT_FORMAT_BTOR [default]:
        `BTOR`_ format
      * BZLA_OUTPUT_FORMAT_BTOR2:
        `BTOR2`_ format
      * BZLA_OUTPUT_FORMAT_SMT2:
        `SMT-LIB v2`_ format
      * BZLA_OUTPUT_FORMAT_AIGER_ASCII:
        `Aiger ascii format <http://fmv.jku.at/papers/BiereHeljankoWieringa-FMV-TR-11-2.pdf>`_
      * BZLA_OUTPUT_FORMAT_AIGER_BINARY:
        `Aiger binary format <http://fmv.jku.at/papers/BiereHeljankoWieringa-FMV-TR-11-2.pdf>`_
  */
  BZLA_OPT_OUTPUT_FORMAT,

  /*!
    * **BZLA_OPT_ENGINE**

      | Set solver engine.

      * BZLA_ENGINE_FUN [default]:
        the default engine for all combinations of QF_AUFBV, uses lemmas on
        demand for QF_AUFBV and eager bit-blasting for QF_BV
      * BZLA_ENGINE_SLS:
        the score-based local search QF_BV engine
      * BZLA_ENGINE_PROP:
        the propagation-based local search QF_BV engine
      * BZLA_ENGINE_AIGPROP:
        the propagation-based local search QF_BV engine that operates on the
        bit-blasted formula (the AIG layer)
      * BZLA_ENGINE_QUANT:
        the quantifier engine (BV only)
  */
  BZLA_OPT_ENGINE,

  /*!
    * **BZLA_OPT_SAT_ENGINE**

      | Set sat solver engine.
      | Available option values and default values depend on the sat solvers
        configured.

      * BZLA_SAT_ENGINE_CADICAL:
        `CaDiCaL <https://fmv.jku.at/cadical>`_
      * BZLA_SAT_ENGINE_CMS:
        `CryptoMiniSat <https://github.com/msoos/cryptominisat>`_
      * BZLA_SAT_ENGINE_KISSAT:
        `Kissat <https://github.com/arminbiere/kissat>`_
      * BZLA_SAT_ENGINE_LINGELING:
        `Lingeling <https://fmv.jku.at/lingeling>`_
      * BZLA_SAT_ENGINE_MINISAT:
        `MiniSat <https://github.com/niklasso/minisat>`_
      * BZLA_SAT_ENGINE_PICOSAT:
        `PicoSAT <http://fmv.jku.at/picosat/>`_
  */
  BZLA_OPT_SAT_ENGINE,

  /*!
    * **BZLA_OPT_AUTO_CLEANUP**

      Enable (``value``:1) or disable (``value``:0) auto cleanup of all
      references held on exit.
    */
  BZLA_OPT_AUTO_CLEANUP,

  /*!
    * **BZLA_OPT_PRETTY_PRINT**

      Enable (``value``: 1) or disable (``value``: 0) pretty printing when
      dumping.
  */
  BZLA_OPT_PRETTY_PRINT,

  /*!
    * **BZLA_OPT_EXIT_CODES**

      | Enable (``value``:1) or disable (``value``:0) the use of Boolector exit
        codes (BOOLECTOR_SAT, BOOLECTOR_UNSAT, BOOLECTOR_UNKNOWN - see
        :ref:`macros`).
      | If disabled, on exit Boolector returns 0 if success (sat or unsat), and
        1 in any other case.
  */
  BZLA_OPT_EXIT_CODES,

  /*!
    * **BZLA_OPT_SEED**

      | Set seed for Boolector's internal random number generator.
      | Boolector uses 0 by default.
  */
  BZLA_OPT_SEED,

  /*
    * **BZLA_OPT_VERBOSITY**

      Set the level of verbosity.
  */
  BZLA_OPT_VERBOSITY,

  /*
    * **BZLA_OPT_LOGLEVEL**

      Set the log level.
  */
  BZLA_OPT_LOGLEVEL,

  /* --------------------------------------------------------------------- */
  /*!
    **Simplifier Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BZLA_OPT_REWRITE_LEVEL**

      | Set the rewrite level (``value``: 0-3) of the rewriting engine.
      | Boolector uses rewrite level 3 by default, rewrite levels are
        classified as follows:

      * 0: no rewriting
      * 1: term level rewriting
      * 2: more simplification techniques
      * 3: full rewriting/simplification

      | Do not alter the rewrite level of the rewriting engine after creating
        expressions.
  */
  BZLA_OPT_REWRITE_LEVEL,

  /*!
    * **BZLA_OPT_SKELETON_PREPROC**

      Enable (``value``: 1) or disable (``value``: 0) skeleton  preprocessing
      during simplification.
  */
  BZLA_OPT_SKELETON_PREPROC,

  /*!
    * **BZLA_OPT_ACKERMANN**

      Enable (``value``: 1) or disable (``value``: 0) the eager addition of
      Ackermann constraints for function applications.
  */
  BZLA_OPT_ACKERMANN,

  /*!
    * **BZLA_OPT_BETA_REDUCE**

      Enable (``value``: 1) or disable (``value``: 0) the eager elimination of
      lambda expressions via beta reduction.
  */
  BZLA_OPT_BETA_REDUCE,

  /*!
    * **BZLA_OPT_ELIMINATE_ITES**

      Enable (``value``: 1) or disable (``value``: 0) ITE elimination.
  */
  BZLA_OPT_ELIMINATE_ITES,

  /*!
    * **BZLA_OPT_ELIMINATE_SLICES**

      Enable (``value``: 1) or disable (``value``: 0) slice elimination on bit
      vector variables.
  */
  BZLA_OPT_ELIMINATE_SLICES,

  /*!
    * **BZLA_OPT_VAR_SUBST**

      Enable (``value``: 1) or disable (``value``: 0) variable substitution
      during simplification.
  */
  BZLA_OPT_VAR_SUBST,

  /*!
    * **BZLA_OPT_UCOPT**

      Enable (``value``: 1) or disable (``value``: 0) unconstrained
      optimization.
  */
  BZLA_OPT_UCOPT,

  /*!
    * **BZLA_OPT_MERGE_LAMBDAS**

      Enable (``value``: 1) or disable (``value``: 0) merging of lambda
      expressions.
  */
  BZLA_OPT_MERGE_LAMBDAS,

  /*!
    * **BZLA_OPT_EXTRACT_LAMBDAS**

      Enable (``value``: 1) or disable (``value``: 0) extraction of common
      array patterns as lambda terms.
  */
  BZLA_OPT_EXTRACT_LAMBDAS,

  /*!
    * **BZLA_OPT_NORMALIZE**

      Enable (``value``: 1) or disable (``value``: 0) normalization of
      addition, multiplication and bit-wise and.
  */
  BZLA_OPT_NORMALIZE,

  /*!
    * **BZLA_OPT_NORMALIZE_ADD**

      Enable (``value``: 1) or disable (``value``: 0) normalization of
      addition.
  */
  BZLA_OPT_NORMALIZE_ADD,

  /* --------------------------------------------------------------------- */
  /*!
    **Fun Engine Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BZLA_OPT_FUN_PREPROP**

      Enable (``value``: 1) or disable (``value``: 0) prop engine as
      preprocessing step within sequential portfolio setting.
   */
  BZLA_OPT_FUN_PREPROP,

  /*!
    * **BZLA_OPT_FUN_PRESLS**

      Enable (``value``: 1) or disable (``value``: 0) sls engine as
      preprocessing step within sequential portfolio setting.
   */
  BZLA_OPT_FUN_PRESLS,

  /*!
    * **BZLA_OPT_FUN_DUAL_PROP**

      Enable (``value``: 1) or disable (``value``: 0) dual propagation
      optimization.
  */
  BZLA_OPT_FUN_DUAL_PROP,

  /*!
    * **BZLA_OPT_FUN_DUAL_PROP_QSORT**

      | Set order in which inputs are assumed in dual propagation clone.

      * BZLA_DP_QSORT_JUST [default]:
        order by score, highest score first
      * BZLA_DP_QSORT_ASC:
        order by input id, ascending
      * BZLA_DP_QSORT_DESC:
        order by input id, descending
  */
  BZLA_OPT_FUN_DUAL_PROP_QSORT,

  /*!
    * **BZLA_OPT_FUN_JUST**

      Enable (``value``: 1) or disable (``value``: 0) justification
      optimization.
  */
  BZLA_OPT_FUN_JUST,

  /*!
    * **BZLA_OPT_FUN_JUST_HEURISTIC**

      | Set heuristic that determines path selection for justification
        optimization.

      * BZLA_JUST_HEUR_BRANCH_MIN_APP [default]:
        choose branch with minimum number of applies
      * BZLA_JUST_HEUR_BRANCH_MIN_DEP:
        choose branch with minimum depth
      * BZLA_JUST_HEUR_LEFT:
        always choose left branch
  */
  BZLA_OPT_FUN_JUST_HEURISTIC,

  /*!
    * **BZLA_OPT_FUN_LAZY_SYNTHESIZE**

      Enable (``value``: 1) or disable (``value``: 0) lazy synthesis of bit
      vector expressions.
  */
  BZLA_OPT_FUN_LAZY_SYNTHESIZE,

  /*!
    * **BZLA_OPT_FUN_EAGER_LEMMAS**

      | Select mode for eager lemma generation.

      * BZLA_FUN_EAGER_LEMMAS_NONE:
        do not generate lemmas eagerly (generate one single lemma per
        refinement iteration)
      * BZLA_FUN_EAGER_LEMMAS_CONF:
        only generate lemmas eagerly until the first conflict dependent on
        another conflict is found
      * BZLA_FUN_EAGER_LEMMAS_ALL:
        in each refinement iteration, generate lemmas for all conflicts
  */
  BZLA_OPT_FUN_EAGER_LEMMAS,

  BZLA_OPT_FUN_STORE_LAMBDAS,

  /*!
    * **BZLA_OPT_PRINT_DIMACS**

      Enable (``value``: 1) or disable (``value``: 0) DIMACS printer.

      When enabled Boolector will record the CNF sent to the SAT solver and
      prints it to stdout.
   */
  BZLA_OPT_PRINT_DIMACS,


  /* --------------------------------------------------------------------- */
  /*!
    **SLS Engine Options:**
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BZLA_OPT_SLS_NFIPS**
      Set the number of bit flips used as a limit for the sls engine. Disabled
      if 0.
   */
  BZLA_OPT_SLS_NFLIPS,

  /*!
    * **BZLA_OPT_SLS_STRATEGY**

      | Select move strategy for SLS engine.

      * BZLA_SLS_STRAT_BEST_MOVE:
        always choose best score improving move
      * BZLA_SLS_STRAT_RAND_WALK:
        always choose random walk weighted by score
      * BZLA_SLS_STRAT_FIRST_BEST_MOVE [default]:
        always choose first best move (no matter if any other move is better)
      * BZLA_SLS_STRAT_BEST_SAME_MOVE:
        determine move as best move even if its score is not better but the
        same as the score of the previous best move
      * BZLA_SLS_STRAT_ALWAYS_PROP:
        always choose propagation move (and recover with SLS move in case of
        conflict)
  */
  BZLA_OPT_SLS_STRATEGY,

  /*!
    * **BZLA_OPT_SLS_JUST**

      Enable (``value``: 1) or disable (``value``: 0) justification based path
      selection during candidate selection.
  */
  BZLA_OPT_SLS_JUST,

  /*!
    * **BZLA_OPT_SLS_MOVE_GW**

      Enable (``value``: 1) or disable (``value``: 0) group-wise moves, where
      rather than changing the assignment of one single candidate variable, all
      candidate variables are set at the same time (using the same strategy).
  */
  BZLA_OPT_SLS_MOVE_GW,

  /*!
    * **BZLA_OPT_SLS_MOVE_RANGE**

      Enable (``value``: 1) or disable (``value``: 0) range-wise bit-flip
      moves, where the bits within all ranges from 2 to the bit width (starting
      from the LSB) are flipped at once.
  */
  BZLA_OPT_SLS_MOVE_RANGE,

  /*!
    * **BZLA_OPT_SLS_MOVE_SEGMENT**

      Enable (``value``: 1) or disable (``value``: 0) segment-wise bit-flip
      moves, where the bits within segments of multiples of 2 are flipped at
      once.
  */
  BZLA_OPT_SLS_MOVE_SEGMENT,

  /*!
    * **BZLA_OPT_SLS_MOVE_RAND_WALK**

      Enable (``value``: 1) or disable (``value``: 0) random walk moves, where
      one out of all possible neighbors is randomly selected (with given
      probability, see BZLA_OPT_SLS_PROB_MOVE_RAND_WALK) for a randomly
      selected candidate variable.
  */
  BZLA_OPT_SLS_MOVE_RAND_WALK,

  /*!
    * **BZLA_OPT_SLS_PROB_MOVE_RAND_WALK**

      Set the probability with which a random walk is chosen if random walks
      are enabled (see BZLA_OPT_SLS_MOVE_RAND_WALK).
  */
  BZLA_OPT_SLS_PROB_MOVE_RAND_WALK,

  /*!
    * **BZLA_OPT_SLS_MOVE_RAND_ALL**

      Enable (``value``: 1) or disable (``value``: 0) the randomization of all
      candidate variables (rather than a single randomly selected candidate
      variable) in case no best move has been found.
  */
  BZLA_OPT_SLS_MOVE_RAND_ALL,

  /*!
    * **BZLA_OPT_SLS_MOVE_RAND_RANGE**

      Enable (``value``: 1) or disable (``value``: 0) the randomization of bit
      ranges (rather than all bits) of a candidate variable(s) to be randomized
      in case no best move has been found.
  */
  BZLA_OPT_SLS_MOVE_RAND_RANGE,

  /*!
    * **BZLA_OPT_SLS_MOVE_PROP**

      Enable (``value``: 1) or disable (``value``: 0) propagation moves (chosen
      with a given ratio of number of propagation moves to number of regular
      SLS moves, see BZLA_OPT_SLS_MOVE_PROP_N_PROP and
      BZLA_OPT_SLS_MOVE_PROP_N_SLS).
  */
  BZLA_OPT_SLS_MOVE_PROP,

  /*!
    * **BZLA_OPT_SLS_MOVE_PROP_N_PROP**

      Set the number of propagation moves to be performed when propagation
      moves are enabled (propagation moves are chosen with a ratio of
      propagation moves to regular SLS moves, see BZLA_OPT_SLS_MOVE_PROP and
      BZLA_OPT_SLS_MOVE_PROP_N_SLS).
  */
  BZLA_OPT_SLS_MOVE_PROP_N_PROP,

  /*!
    * **BZLA_OPT_SLS_MOVE_PROP_N_SLS**

      Set the number of regular SLS moves to be performed when propagation
      moves are enabled (propagation moves are chosen with a ratio of
      propagation moves to regular SLS moves, see BZLA_OPT_SLS_MOVE_PROP and
      BZLA_OPT_SLS_MOVE_PROP_N_PROP).
  */
  BZLA_OPT_SLS_MOVE_PROP_N_SLS,

  /*!
    * **BZLA_OPT_SLS_MOVE_PROP_FORCE_RW**

      Enable (``value``: 1) or disable (``value``: 0) that random walks are
      forcibly chosen as recovery moves in case of conflicts when a propagation
      move is performed (rather than performing a regular SLS move).
  */
  BZLA_OPT_SLS_MOVE_PROP_FORCE_RW,

  /*!
    * **BZLA_OPT_SLS_MOVE_INC_MOVE_TEST**

      Enable (``value``: 1) or disable (``value``: 0) that during best move
      selection, if the current candidate variable with a previous neighbor
      yields the currently best score, this neighbor assignment is used as a
      base for further neighborhood exploration (rather than its current
      assignment).
  */
  BZLA_OPT_SLS_MOVE_INC_MOVE_TEST,

  /*!
    * **BZLA_OPT_SLS_MOVE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BZLA_OPT_SLS_USE_RESTARTS,

  /*!
    * **BZLA_OPT_SLS_MOVE_RESTARTS**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If disabled, candidate root constraints are selected randomly.
  */
  BZLA_OPT_SLS_USE_BANDIT,

  /* --------------------------------------------------------------------- */
  /*!
    **Prop Engine Options**:
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BZLA_OPT_PROP_NPROPS**

      Set the number of propagation (steps) used as a limit for the propagation
      engine. Disabled if 0.
   */
  BZLA_OPT_PROP_NPROPS,

  /*!
    * **BZLA_OPT_PROP_NUPDATES**

      Set the number of model value updates used as a limit for the propagation
      engine. Disabled if 0.
   */
  BZLA_OPT_PROP_NUPDATES,

  /*!
    * **BZLA_OPT_PROP_ENTAILED**

      Maintain a work queue with entailed propagations.
      If enabled, propagations from this queue are propagated before randomly
      choosing a yet unsatisfied path from the root.

      This feature is disabled (BZLA_PROP_ENTAILED_OFF) by default.

      * BZLA_PROP_ENTAILED_OFF: do not use strategy (default)
      * BZLA_PROP_ENTAILED_ALL: propagate all entailed propagations
      * BZLA_PROP_ENTAILED_FIRST: process only the first entailed propagation
      * BZLA_PROP_ENTAILED_LAST: process only the last entailed propagation
  */
  BZLA_OPT_PROP_ENTAILED,

  /*!
    * **BZLA_OPT_PROP_CONST_BITS**

      Enable (``value``: 1) or disable (``value``: 0) constant bit propagation
      (requires bit-blasting to AIG).
    */
  BZLA_OPT_PROP_CONST_BITS,

  /*!
    * **BZLA_OPT_PROP_CONST_DOMAINS**

      Enable (``value``: 1) or disable (``value``: 0) domain propagators for
      determining constant bits .
    */
  BZLA_OPT_PROP_CONST_DOMAINS,

#if 0
  /*!
    * **BZLA_OPT_PROP_DOMAINS**

      Enable (``value``: 1) or disable (``value``: 0) propagating inverse
      values with domain propagators.
    */
  BZLA_OPT_PROP_DOMAINS,
#endif

  /*!
    * **BZLA_OPT_PROP_USE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BZLA_OPT_PROP_USE_RESTARTS,

  /*!
    * **BZLA_OPT_PROP_USE_BANDIT**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If enabled, root constraint selection via bandit scheme is based on a
        scoring scheme similar to the one employed in the SLS engine.
      | If disabled, candidate root constraints are selected randomly.
  */
  BZLA_OPT_PROP_USE_BANDIT,

  /*!
    * **BZLA_OPT_PROP_PATH_SEL**

      Select mode for path selection.

      * BZLA_PROP_PATH_SEL_ESSENTIAL [default]:
        select path based on essential inputs
      * BZLA_PROP_PATH_SEL_RANDOM:
        select path based on random inputs
  */
  BZLA_OPT_PROP_PATH_SEL,

  /*!
    * **BZLA_OPT_PROP_PROB_USE_INV_VALUE**

     Set probabiality with which to choose inverse values over consistent
     values.
  */
  BZLA_OPT_PROP_PROB_USE_INV_VALUE,

  /*!
    * **BZLA_OPT_PROP_PROB_FLIP_COND**

     Set probability with which to select the path to the condition (in case of
     an if-then-else operation) rather than the enabled branch during down
     propagation.
  */
  BZLA_OPT_PROP_PROB_FLIP_COND,

  /*!
    * **BZLA_OPT_PROP_PROB_FLIP_COND_CONST**

     Set probbiality with which to select the path to the condition (in case of
     an if-then-else operation) rather than the enabled branch during down
     propagation if either of the 'then' or 'else' branch is constant.
  */
  BZLA_OPT_PROP_PROB_FLIP_COND_CONST,

  /*!
    * **BZLA_OPT_PROP_FLIP_COND_CONST_DELTA**

     Set delta by which BZLA_OPT_PROP_PROB_FLIP_COND_CONST is decreased or
     increased after a limit BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL is reached.
  */
  BZLA_OPT_PROP_FLIP_COND_CONST_DELTA,

  /*!
    * **BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL**

     Set the limit for how often the path to the condition (in case of an
     if-then-else operation) may be selected before
     BZLA_OPT_PROP_PROB_FLIP_COND_CONST is decreased or increased by
     BZLA_OPT_PROP_PROB_FLIP_COND_CONST_DELTA.
  */
  BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,

  /*!
    * **BZLA_OPT_PROP_PROB_SLICE_KEEP_DC**

      Set probability with which to keep the current value of the don't care
      bits of a slice operation (rather than fully randomizing all of them)
      when selecting an inverse or consistent value.
   */
  BZLA_OPT_PROP_PROB_SLICE_KEEP_DC,

  /*!
    * **BZLA_OPT_PROP_PROB_SLICE_FLIP**

     Set probability with which to use the current assignment of the operand of
     a slice operation with one of the don't care bits flipped (rather than
     fully randomizing all of them, both for inverse and consistent value
     selection) if their current assignment is not kept (see
     BZLA_OPT_PROP_PROB_SLICE_KEEP_DC).
  */
  BZLA_OPT_PROP_PROB_SLICE_FLIP,

  /*!
    * **BZLA_OPT_PROP_PROB_EQ_FLIP**

     Set probability with which the current assignment of the selected node
     with one of its bits flipped (rather than a fully randomized bit-vector)
     is down-propagated in case of a disequality (both for inverse and
     consistent value selection).
  */
  BZLA_OPT_PROP_PROB_EQ_FLIP,

  /*!
    * **BZLA_OPT_PROP_PROB_AND_FLIP**

     Set probability with which the current assignment of the don't care bits
     of the selected node with max. one of its bits flipped (rather than fully
     randomizing all of them) in case of an and operation (for both inverse and
     consistent value selection).

  */
  BZLA_OPT_PROP_PROB_AND_FLIP,

  /*!
    * **BZLA_OPT_PROP_PROB_RANDOM_INPUT**

     Set probability with which a random input is chosen instead of an an
     essential input.
  */
  BZLA_OPT_PROP_PROB_RANDOM_INPUT,

  /*!
    * **BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT**

      | Do not perform a propagation move when running into a conflict during
        inverse computation.
      | (This is the default behavior for the SLS engine when propagation moves
        are enabled, where a conflict triggers a recovery by means of a regular
        SLS move.)
    */
  BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,

  /*!
    * **BZLA_OPT_PROP_SKIP_NO_PROGRESS**

     Skip moves if target value is the same as current model.
    */
  BZLA_OPT_PROP_SKIP_NO_PROGRESS,

  /*!
    * **BZLA_OPT_PROP_USE_INV_LT_CONCAT**

     Use special inverse value functions for ult/slt over concats.
    */
  BZLA_OPT_PROP_USE_INV_LT_CONCAT,

  /*!
    * **BZLA_OPT_PROP_INFER_TOP_LEVEL_BOUNDS**

     Infer bounds for inequalities based on satisfied top level inequalities.
    */
  BZLA_OPT_PROP_INFER_INEQ_BOUNDS,

  /*!
    * **BZLA_OPT_PROP_SEXT**

      Use sign_extend inverse value computation.
    */
  BZLA_OPT_PROP_SEXT,

  /*!
    * **BZLA_OPT_PROP_XOR**

      Use xor inverse value computation.
    */
  BZLA_OPT_PROP_XOR,

  /*!
    * **BZLA_OPT_PROP_SRA**

      Use xor inverse value computation.
    */
  BZLA_OPT_PROP_SRA,


  /* --------------------------------------------------------------------- */
  /*!
    **AIGProp Engine Options**:
   */
  /* --------------------------------------------------------------------- */

  /*!
    * **BZLA_OPT_AIGPROP_USE_RESTARTS**

      Enable (``value``: 1) or disable (``value``: 0) restarts.
  */
  BZLA_OPT_AIGPROP_USE_RESTARTS,

  /*!
    * **BZLA_OPT_AIGPROP_USE_RESTARTS**

      | Enable (``value``: 1) or disable (``value``: 0) heuristic (bandit
        scheme) for selecting root constraints.
      | If enabled, root constraint selection via bandit scheme is based on a
        scoring scheme similar to the one employed in the SLS engine.
      | If disabled, candidate root constraints are selected randomly.
  */
  BZLA_OPT_AIGPROP_USE_BANDIT,

  /*!
    * **BZLA_OPT_AIGPROP_NPROPS**

      Set the number of propagation (steps) used as a limit for the (bit-level)
      propagation engine. Disabled if 0.
   */
  BZLA_OPT_AIGPROP_NPROPS,

  /* QUANT engine ------------------------------------------------------- */
  /*!
    * **BZLA_OPT_QUANT_SYNTH**

     Select synthesis mode for Skolem functions.

     * BZLA_QUANT_SYNTH_NONE:
       do not synthesize skolem functions (use model values for instantiation)
     * BZLA_QUANT_SYNTH_EL:
       use enumerative learning to synthesize skolem functions
     * BZLA_QUANT_SYNTH_ELMC:
       use enumerative learning modulo the predicates in the cone of influence
       of the existential variables to synthesize skolem functions
     * BZLA_QUANT_SYNTH_EL_ELMC:
       chain BZLA_QUANT_SYNTH_EL and BZLA_QUANT_SYNTH_ELMC approaches to
       synthesize skolem functions
     * BZLA_QUANT_SYNTH_ELMR:
       use enumerative learning modulo the given root constraints to synthesize
       skolem functions
  */
  BZLA_OPT_QUANT_SYNTH,

  /*!
    * **BZLA_OPT_QUANT_DUAL_SOLVER**

      Enable (``value``: 1) or disable (``value``: 0) solving the dual
      (negated) version of the quantified bit-vector formula.
   */
  BZLA_OPT_QUANT_DUAL_SOLVER,

  /*!
    * **BZLA_OPT_QUANT_SYNTH_LIMIT**

      Set the limit of enumerated expressions for the enumerative learning
      synthesis algorithm.
   */
  BZLA_OPT_QUANT_SYNTH_LIMIT,

  /*!
    * **BZLA_OPT_SYNTH_QI**

      Enable (``value``: 1) or disable (``value``: 0) generalization of
      quantifier instantiations via enumerative learning.
   */
  BZLA_OPT_QUANT_SYNTH_QI,

  /*!
    * **BZLA_OPT_QUANT_DER**

      Enable (``value``: 1) or disable (``value``: 0) destructive equality
      resolution simplification.
   */
  BZLA_OPT_QUANT_DER,

  /*!
    * **BZLA_OPT_QUANT_CER**

      Enable (``value``: 1) or disable (``value``: 0) constructive equality
      resolution simplification.
   */
  BZLA_OPT_QUANT_CER,

  /*!
    * **BZLA_OPT_QUANT_MINISCOPE**

      Enable (``value``: 1) or disable (``value``: 0) miniscoping.
   */
  BZLA_OPT_QUANT_MINISCOPE,

  /* internal options --------------------------------------------------- */

  BZLA_OPT_SORT_EXP,
  BZLA_OPT_SORT_AIG,
  BZLA_OPT_SORT_AIGVEC,
  BZLA_OPT_AUTO_CLEANUP_INTERNAL,
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

  /* this MUST be the last entry! */
  BZLA_OPT_NUM_OPTS,
};
// clang-format on

typedef enum BzlaOption BzlaOption;

/* --------------------------------------------------------------------- */
/* Boolector option values                                               */
/* --------------------------------------------------------------------- */

/* Note: enums with NONE values should start with NONE = 0. If there is no NONE
 * value the enum range should start with 1. This allows us to determine if an
 * option is set by checking if it is > 0. */

enum BzlaOptSatEngine
{
  BZLA_SAT_ENGINE_LINGELING,
  BZLA_SAT_ENGINE_PICOSAT,
  BZLA_SAT_ENGINE_KISSAT,
  BZLA_SAT_ENGINE_MINISAT,
  BZLA_SAT_ENGINE_CADICAL,
  BZLA_SAT_ENGINE_CMS,
};
typedef enum BzlaOptSatEngine BzlaOptSatEngine;

enum BzlaOptEngine
{
  BZLA_ENGINE_FUN = 1,
  BZLA_ENGINE_SLS,
  BZLA_ENGINE_PROP,
  BZLA_ENGINE_AIGPROP,
  BZLA_ENGINE_QUANT,
};
typedef enum BzlaOptEngine BzlaOptEngine;

enum BzlaOptInputFormat
{
  BZLA_INPUT_FORMAT_NONE,
  BZLA_INPUT_FORMAT_BTOR,
  BZLA_INPUT_FORMAT_BTOR2,
  BZLA_INPUT_FORMAT_SMT2,
};
typedef enum BzlaOptInputFormat BzlaOptInputFormat;

enum BzlaOptOutputBase
{
  BZLA_OUTPUT_BASE_BIN = 1,
  BZLA_OUTPUT_BASE_HEX,
  BZLA_OUTPUT_BASE_DEC,
};
typedef enum BzlaOptOutputBase BzlaOptOutputBase;

enum BzlaOptOutputFormat
{
  BZLA_OUTPUT_FORMAT_NONE,
  BZLA_OUTPUT_FORMAT_BTOR = 1,
  //  BZLA_OUTPUT_FORMAT_BTOR2,
  BZLA_OUTPUT_FORMAT_SMT2,
  BZLA_OUTPUT_FORMAT_AIGER_ASCII,
  BZLA_OUTPUT_FORMAT_AIGER_BINARY,
};
typedef enum BzlaOptOutputFormat BzlaOptOutputFormat;

enum BzlaOptDPQsort
{
  BZLA_DP_QSORT_JUST = 1,
  BZLA_DP_QSORT_ASC,
  BZLA_DP_QSORT_DESC,
};
typedef enum BzlaOptDPQsort BzlaOptDPQsort;

enum BzlaOptJustHeur
{
  BZLA_JUST_HEUR_BRANCH_LEFT = 1,
  BZLA_JUST_HEUR_BRANCH_MIN_APP,
  BZLA_JUST_HEUR_BRANCH_MIN_DEP,
};
typedef enum BzlaOptJustHeur BzlaOptJustHeur;

enum BzlaOptSLSStrat
{
  BZLA_SLS_STRAT_BEST_MOVE = 1,
  BZLA_SLS_STRAT_RAND_WALK,
  BZLA_SLS_STRAT_FIRST_BEST_MOVE,
  BZLA_SLS_STRAT_BEST_SAME_MOVE,
  BZLA_SLS_STRAT_ALWAYS_PROP,
};
typedef enum BzlaOptSLSStrat BzlaOptSLSStrat;

enum BzlaOptPropPathSel
{
  BZLA_PROP_PATH_SEL_ESSENTIAL = 1,
  BZLA_PROP_PATH_SEL_RANDOM,
};
typedef enum BzlaOptPropPathSel BzlaOptPropPathSel;

enum BzlaOptPropEntailed
{
  BZLA_PROP_ENTAILED_MIN,
  BZLA_PROP_ENTAILED_OFF,
  BZLA_PROP_ENTAILED_ALL,
  BZLA_PROP_ENTAILED_FIRST,
  BZLA_PROP_ENTAILED_LAST,
  BZLA_PROP_ENTAILED_MAX,
};
typedef enum BzlaOptPropEntailed BzlaOptPropEntailed;

enum BzlaOptQuantSynth
{
  BZLA_QUANT_SYNTH_NONE,
  BZLA_QUANT_SYNTH_EL,
  BZLA_QUANT_SYNTH_ELMC,
  BZLA_QUANT_SYNTH_EL_ELMC,
  BZLA_QUANT_SYNTH_ELMR,
};
typedef enum BzlaOptQuantSynth BzlaOptQuantSynt;

enum BzlaOptFunEagerLemmas
{
  BZLA_FUN_EAGER_LEMMAS_NONE,
  BZLA_FUN_EAGER_LEMMAS_CONF,
  BZLA_FUN_EAGER_LEMMAS_ALL,
};
typedef enum BzlaOptFunEagerLemmas BzlaOptFunEagerLemmas;

enum BzlaOptIncrementalSMT1
{
  BZLA_INCREMENTAL_SMT1_BASIC = 1,
  BZLA_INCREMENTAL_SMT1_CONTINUE,
};
typedef enum BzlaOptIncrementalSMT1 BzlaOptIncrementalSMT1;

enum BzlaOptBetaReduceMode
{
  BZLA_BETA_REDUCE_NONE,
  BZLA_BETA_REDUCE_FUN,
  BZLA_BETA_REDUCE_ALL,
};
typedef enum BzlaOptBetaReduceMode BzlaOptBetaReduceMode;

enum BzlaRoundingMode
{
  BZLA_RM_RNA = 0,
  BZLA_RM_RNE = 1,
  BZLA_RM_RTN = 2,
  BZLA_RM_RTP = 3,
  BZLA_RM_RTZ = 4,
  BZLA_RM_MAX,
};
typedef enum BzlaRoundingMode BzlaRoundingMode;

/* --------------------------------------------------------------------- */

/* Callback function to be executed on abort, primarily intended to be used for
 * plugging in exception handling. */
struct BzlaAbortCallback
{
  void (*abort_fun)(const char* msg);
  void* cb_fun; /* abort callback function */
};
typedef struct BzlaAbortCallback BzlaAbortCallback;

extern BzlaAbortCallback bzla_abort_callback;

#endif
