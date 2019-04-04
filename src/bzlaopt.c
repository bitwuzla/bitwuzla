/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2019 Aina Niemetz.
 *  Copyright (C) 2014-2020 Mathias Preiner.
 *  Copyright (C) 2015 Armin Biere.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlaopt.h"

#include <limits.h>

#include "boolector.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlaparse.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlarng.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

const char *const g_bzla_se_name[BZLA_SAT_ENGINE_MAX + 1] = {
    [BZLA_SAT_ENGINE_LINGELING] = "Lingeling",
    [BZLA_SAT_ENGINE_PICOSAT]   = "PicoSAT",
    [BZLA_SAT_ENGINE_MINISAT]   = "MiniSat",
    [BZLA_SAT_ENGINE_CADICAL]   = "CaDiCaL",
    [BZLA_SAT_ENGINE_CMS]       = "CryptoMiniSat",
};

/*------------------------------------------------------------------------*/

static void
init_opt(Bzla *bzla,
         BzlaOption opt,
         bool internal,
         bool isflag,
         char *lng,
         char *shrt,
         uint32_t val,
         uint32_t min,
         uint32_t max,
         char *desc)
{
  assert(bzla);
  assert(opt >= 0 && opt < BZLA_OPT_NUM_OPTS);
  assert(lng);
  assert(max <= UINT32_MAX);
  assert(min <= val);
  assert(val <= max);

  uint32_t v;
  char *valstr;

  assert(!bzla_hashptr_table_get(bzla->str2opt, lng));

  bzla->options[opt].internal = internal;
  bzla->options[opt].isflag   = isflag;
  bzla->options[opt].shrt     = shrt;
  bzla->options[opt].lng      = lng;
  bzla->options[opt].val      = val;
  bzla->options[opt].dflt     = val;
  bzla->options[opt].min      = min;
  bzla->options[opt].max      = max;
  bzla->options[opt].desc     = desc;

  bzla_hashptr_table_add(bzla->str2opt, lng)->data.as_int = opt;

  if ((valstr = bzla_util_getenv_value(bzla->mm, lng)))
  {
    v = atoi(valstr);
    if (v < min)
      v = min;
    else if (v > max)
      v = max;
    if (v == val) return;
    /* we need to trace options set via ENV vars */
    if (!internal)
      boolector_set_opt(bzla, opt, v);
    else
      bzla_opt_set(bzla, opt, v);
  }
}

static void
add_opt_help(
    BzlaMemMgr *mm, BzlaPtrHashTable *opts, char *key, int32_t value, char *msg)
{
  assert(opts);

  BzlaOptHelp *hdata;

  BZLA_NEW(mm, hdata);
  hdata->val = value;
  hdata->msg = msg;

  bzla_hashptr_table_add(opts, key)->data.as_ptr = hdata;
}

static int
strcmpoptval(const char *a, const char *b)
{
  size_t len_a = strlen(a);
  size_t len_b = strlen(b);
  if (len_a < len_b) return -1;
  if (len_a > len_b) return 1;
  return strncmp(a, b, len_a);
}

void
bzla_opt_init_opts(Bzla *bzla)
{
  assert(bzla);

  BzlaPtrHashTable *opts;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  BZLA_CNEWN(mm, bzla->options, BZLA_OPT_NUM_OPTS);
  bzla->str2opt = bzla_hashptr_table_new(
      mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);

  init_opt(bzla,
           BZLA_OPT_MODEL_GEN,
           false,
           true,
           "model-gen",
           "m",
           0,
           0,
           2,
           "print model for satisfiable instances");
  init_opt(bzla,
           BZLA_OPT_INCREMENTAL,
           false,
           true,
           "incremental",
           "i",
           0,
           0,
           1,
           "incremental usage");
  init_opt(bzla,
           BZLA_OPT_INCREMENTAL_SMT1,
           false,
           false,
           "incremental-smt1",
           "I",
           BZLA_INCREMENTAL_SMT1_DFLT,
           BZLA_INCREMENTAL_SMT1_MIN,
           BZLA_INCREMENTAL_SMT1_MAX,
           "incremental mode for SMT1");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "basic",
               BZLA_INCREMENTAL_SMT1_BASIC,
               "stop after first satisfiable formula");
  add_opt_help(mm,
               opts,
               "continue",
               BZLA_INCREMENTAL_SMT1_CONTINUE,
               "solve all formulas");
  bzla->options[BZLA_OPT_INCREMENTAL_SMT1].options = opts;

  init_opt(bzla,
           BZLA_OPT_INPUT_FORMAT,
           false,
           false,
           "input-format",
           0,
           BZLA_INPUT_FORMAT_DFLT,
           BZLA_INPUT_FORMAT_MIN,
           BZLA_INPUT_FORMAT_MAX,
           "input file format");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(
      mm, opts, "none", BZLA_INPUT_FORMAT_NONE, "auto-detect input format");
  add_opt_help(
      mm, opts, "btor", BZLA_INPUT_FORMAT_BTOR, "force BTOR input format");
  add_opt_help(
      mm, opts, "btor2", BZLA_INPUT_FORMAT_BTOR2, "force BTOR2 input format");
  add_opt_help(mm,
               opts,
               "smt1",
               BZLA_INPUT_FORMAT_SMT1,
               "force SMT-LIB v1 input format");
  add_opt_help(mm,
               opts,
               "smt2",
               BZLA_INPUT_FORMAT_SMT2,
               "force SMT-LIB v2 input format");
  bzla->options[BZLA_OPT_INPUT_FORMAT].options = opts;

  init_opt(bzla,
           BZLA_OPT_OUTPUT_NUMBER_FORMAT,
           false,
           false,
           "output-number-format",
           0,
           BZLA_OUTPUT_BASE_DFLT,
           BZLA_OUTPUT_BASE_MIN,
           BZLA_OUTPUT_BASE_MAX,
           "output number format");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "bin",
               BZLA_OUTPUT_BASE_BIN,
               "print bit-vector values in binary format");
  add_opt_help(mm,
               opts,
               "hex",
               BZLA_OUTPUT_BASE_HEX,
               "print bit-vector values in hexa-decimal format");
  add_opt_help(mm,
               opts,
               "dec",
               BZLA_OUTPUT_BASE_DEC,
               "print bit-vector values in decimal format");
  bzla->options[BZLA_OPT_OUTPUT_NUMBER_FORMAT].options = opts;

  init_opt(bzla,
           BZLA_OPT_OUTPUT_FORMAT,
           false,
           false,
           "output-format",
           0,
           BZLA_OUTPUT_FORMAT_DFLT,
           BZLA_OUTPUT_FORMAT_MIN,
           BZLA_OUTPUT_FORMAT_MAX,
           "output file format");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "btor",
               BZLA_OUTPUT_FORMAT_BTOR,
               "use BTOR as output file format");
  // add_opt_help (mm,
  //              opts,
  //              "btor2",
  //              BZLA_OUTPUT_FORMAT_BTOR2,
  //              "use BTOR2 as output file format");
  add_opt_help(mm,
               opts,
               "smt2",
               BZLA_OUTPUT_FORMAT_SMT2,
               "use SMT2 as output file format");
  add_opt_help(mm,
               opts,
               "aiger",
               BZLA_OUTPUT_FORMAT_AIGER_ASCII,
               "use the AIGER ascii format as output file format");
  add_opt_help(mm,
               opts,
               "aigerbin",
               BZLA_OUTPUT_FORMAT_AIGER_BINARY,
               "use the AIGER binary format as output file format");
  bzla->options[BZLA_OPT_OUTPUT_FORMAT].options = opts;

  init_opt(bzla,
           BZLA_OPT_ENGINE,
           false,
           false,
           "engine",
           "E",
           BZLA_ENGINE_DFLT,
           BZLA_ENGINE_MIN,
           BZLA_ENGINE_MAX,
           "enable specific engine");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "aigprop",
               BZLA_ENGINE_AIGPROP,
               "use the propagation-based local search engine (QF_BV only)");
  add_opt_help(mm,
               opts,
               "fun",
               BZLA_ENGINE_FUN,
               "use the default engine (supports any combination of QF_AUFBV "
               "+ lambdas, uses eager bit-blasting for QF_BV)");
  add_opt_help(mm,
               opts,
               "prop",
               BZLA_ENGINE_PROP,
               "use the propagation-based local search engine (QF_BV only)");
  add_opt_help(mm,
               opts,
               "sls",
               BZLA_ENGINE_SLS,
               "use the score-based local search engine (QF_BV only)");
  add_opt_help(mm,
               opts,
               "quant",
               BZLA_ENGINE_QUANT,
               "use the quantifier engine (BV only)");
  bzla->options[BZLA_OPT_ENGINE].options = opts;

  init_opt(bzla,
           BZLA_OPT_SAT_ENGINE,
           false,
           false,
           "sat-engine",
           "SE",
           BZLA_SAT_ENGINE_DFLT,
           BZLA_SAT_ENGINE_MIN,
           BZLA_SAT_ENGINE_MAX,
           "enable specific SAT solver");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "cadical",
               BZLA_SAT_ENGINE_CADICAL,
               "use cadical as back end SAT solver");
  add_opt_help(mm,
               opts,
               "cms",
               BZLA_SAT_ENGINE_CMS,
               "use cryptominisat as back end SAT solver");
  add_opt_help(mm,
               opts,
               "lingeling",
               BZLA_SAT_ENGINE_LINGELING,
               "use lingeling as back end SAT solver");
  add_opt_help(mm,
               opts,
               "minisat",
               BZLA_SAT_ENGINE_MINISAT,
               "use minisat as back end SAT solver");
  add_opt_help(mm,
               opts,
               "picosat",
               BZLA_SAT_ENGINE_PICOSAT,
               "use picosat as back end SAT solver");
  bzla->options[BZLA_OPT_SAT_ENGINE].options = opts;

  init_opt(bzla,
           BZLA_OPT_AUTO_CLEANUP,
           false,
           true,
           "auto-cleanup",
           "ac",
           0,
           0,
           1,
           "auto cleanup on exit");
  init_opt(bzla,
           BZLA_OPT_PRETTY_PRINT,
           false,
           true,
           "pretty-print",
           "p",
           1,
           0,
           1,
           "pretty print when dumping");
  init_opt(bzla,
           BZLA_OPT_EXIT_CODES,
           false,
           true,
           "exit-codes",
           "e",
           1,
           0,
           1,
           "use exit codes for sat/unsat");
  init_opt(bzla,
           BZLA_OPT_SEED,
           false,
           false,
           "seed",
           "s",
           0,
           0,
           UINT32_MAX,
           "random number generator seed");
  init_opt(bzla,
           BZLA_OPT_VERBOSITY,
           false,
           true,
           "verbosity",
           "v",
           0,
           0,
           BZLA_VERBOSITY_MAX,
           "increase verbosity");
  init_opt(bzla,
           BZLA_OPT_LOGLEVEL,
           false,
           true,
           "loglevel",
           "l",
           0,
           0,
           UINT32_MAX,
           "increase loglevel");

  /* simplifier --------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_REWRITE_LEVEL,
           false,
           false,
           "rewrite-level",
           "rwl",
           3,
           0,
           3,
           "rewrite level");
  init_opt(bzla,
           BZLA_OPT_SKELETON_PREPROC,
           false,
           true,
           "skeleton-preproc",
           "sp",
           1,
           0,
           1,
           "propositional skeleton preprocessing");
  init_opt(bzla,
           BZLA_OPT_ACKERMANN,
           false,
           true,
           "ackermannize",
           "ack",
           0,
           0,
           1,
           "add ackermann constraints");
  init_opt(bzla,
           BZLA_OPT_BETA_REDUCE,
           false,
           false,
           "beta-reduce",
           "br",
           BZLA_BETA_REDUCE_DFLT,
           BZLA_BETA_REDUCE_MIN,
           BZLA_BETA_REDUCE_MAX,
           "eagerly eliminate lambda expressions");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm, opts, "none", BZLA_BETA_REDUCE_NONE, "do not beta-reduce");
  add_opt_help(
      mm, opts, "fun", BZLA_BETA_REDUCE_FUN, "only beta-reduce functions");
  add_opt_help(mm,
               opts,
               "all",
               BZLA_BETA_REDUCE_ALL,
               "beta-reduce functions and array-writes");
  bzla->options[BZLA_OPT_BETA_REDUCE].options = opts;

  init_opt(bzla,
           BZLA_OPT_ELIMINATE_SLICES,
           false,
           true,
           "eliminate-slices",
           "es",
           1,
           0,
           1,
           "eliminate slices on variables");
  init_opt(bzla,
           BZLA_OPT_VAR_SUBST,
           false,
           true,
           "var-subst",
           "vs",
           1,
           0,
           1,
           "variable substitution");
  init_opt(bzla,
           BZLA_OPT_UCOPT,
           false,
           true,
           "ucopt",
           "uc",
           0,
           0,
           1,
           "unconstrained optimization");
  init_opt(bzla,
           BZLA_OPT_MERGE_LAMBDAS,
           false,
           true,
           "merge-lambdas",
           "ml",
           1,
           0,
           1,
           "merge lambda chains");
  init_opt(bzla,
           BZLA_OPT_EXTRACT_LAMBDAS,
           false,
           true,
           "extract-lambdas",
           "xl",
           1,
           0,
           1,
           "extract lambda terms");
  init_opt(bzla,
           BZLA_OPT_NORMALIZE_ADD,
           false,
           true,
           "normalize-add",
           "nadd",
           1,
           0,
           1,
           "normalize addition operators");
  init_opt(bzla,
           BZLA_OPT_NORMALIZE,
           false,
           true,
           "normalize",
           "norm",
           1,
           0,
           1,
           "normalize add/mul/and operators");

  /* FUN engine ---------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_FUN_PREPROP,
           false,
           true,
           "fun-preprop",
           0,
           0,
           0,
           1,
           "run prop engine as preprocessing within a sequential portfolio "
           "(QF_BV only)");
  init_opt(bzla,
           BZLA_OPT_FUN_PRESLS,
           false,
           true,
           "fun-presls",
           0,
           0,
           0,
           1,
           "run sls engine as preprocessing within a sequential portfolio "
           "(QF_BV only)");
  init_opt(bzla,
           BZLA_OPT_FUN_DUAL_PROP,
           false,
           true,
           "fun-dual-prop",
           "fun-dp",
           0,
           0,
           1,
           "dual propagation optimization");

  init_opt(bzla,
           BZLA_OPT_FUN_DUAL_PROP_QSORT,
           false,
           false,
           "fun-dual-prop-qsort",
           0,
           BZLA_DP_QSORT_DFLT,
           BZLA_DP_QSORT_MIN,
           BZLA_DP_QSORT_MAX,
           "order in which to assume inputs in dual solver");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "just",
               BZLA_DP_QSORT_JUST,
               "use justification-based heuristic to determine order");
  add_opt_help(
      mm, opts, "asc", BZLA_DP_QSORT_ASC, "use ascending (node id) order");
  add_opt_help(
      mm, opts, "desc", BZLA_DP_QSORT_DESC, "use descending (node id) order");
  bzla->options[BZLA_OPT_FUN_DUAL_PROP_QSORT].options = opts;

  init_opt(bzla,
           BZLA_OPT_FUN_JUST,
           false,
           true,
           "fun-just",
           "fun-ju",
           0,
           0,
           1,
           "justification optimization");

  init_opt(bzla,
           BZLA_OPT_FUN_JUST_HEURISTIC,
           false,
           false,
           "fun-just-heuristic",
           0,
           BZLA_JUST_HEUR_DFLT,
           BZLA_JUST_HEUR_MIN,
           BZLA_JUST_HEUR_MAX,
           "justification heuristic");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "left",
               BZLA_JUST_HEUR_BRANCH_LEFT,
               "if there is a choice, choose left branch");
  add_opt_help(mm,
               opts,
               "applies",
               BZLA_JUST_HEUR_BRANCH_MIN_APP,
               "if there is a choice, "
               "choose branch with the minimum number of applies");
  add_opt_help(mm,
               opts,
               "depth",
               BZLA_JUST_HEUR_BRANCH_MIN_DEP,
               "if there is a choice, "
               "choose branch with minimum depth");
  bzla->options[BZLA_OPT_FUN_JUST_HEURISTIC].options = opts;

  init_opt(bzla,
           BZLA_OPT_FUN_LAZY_SYNTHESIZE,
           false,
           true,
           "fun-lazy-synthesize",
           "fun-ls",
           0,
           0,
           1,
           "lazily synthesize expressions");

  init_opt(bzla,
           BZLA_OPT_FUN_EAGER_LEMMAS,
           false,
           false,
           "fun-eager-lemmas",
           "fun-el",
           BZLA_FUN_EAGER_LEMMAS_DFLT,
           BZLA_FUN_EAGER_LEMMAS_MIN,
           BZLA_FUN_EAGER_LEMMAS_MAX,
           "eager lemma generation");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "none",
               BZLA_FUN_EAGER_LEMMAS_NONE,
               "do not generate lemmas eagerly");
  add_opt_help(mm,
               opts,
               "conf",
               BZLA_FUN_EAGER_LEMMAS_CONF,
               "only generate lemmas eagerly until the first conflict "
               "dependent on another conflict is found");
  add_opt_help(mm,
               opts,
               "all",
               BZLA_FUN_EAGER_LEMMAS_ALL,
               "generate lemmas for all conflicts");
  bzla->options[BZLA_OPT_FUN_EAGER_LEMMAS].options = opts;

  init_opt(bzla,
           BZLA_OPT_FUN_STORE_LAMBDAS,
           false,
           true,
           "fun-store-lambdas",
           "fun-sl",
           0,
           0,
           1,
           "represent array store as lambda");

  init_opt(
      bzla,
      BZLA_OPT_PRINT_DIMACS,
      false,
      true,
      "dump-dimacs",
      "dd",
      0,
      0,
      1,
      "Print CNF formula sent to SAT solver in DIMACS format and terminate.");

  /* SLS engine ---------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_SLS_NFLIPS,
           false,
           false,
           "sls-nflips",
           0,
           0,
           0,
           UINT32_MAX,
           "number of bit-flips used as a limit for sls engine");

  init_opt(bzla,
           BZLA_OPT_SLS_STRATEGY,
           false,
           false,
           "sls-strategy",
           0,
           BZLA_SLS_STRAT_DFLT,
           BZLA_SLS_STRAT_MIN,
           BZLA_SLS_STRAT_MAX,
           "move strategy for sls");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "best",
               BZLA_SLS_STRAT_BEST_MOVE,
               "always choose best score improving move");
  add_opt_help(mm,
               opts,
               "walk",
               BZLA_SLS_STRAT_RAND_WALK,
               "always choose random walk weighted by score");
  add_opt_help(mm,
               opts,
               "first",
               BZLA_SLS_STRAT_FIRST_BEST_MOVE,
               "always choose first best move (no matter if any other move "
               "is better");
  add_opt_help(mm,
               opts,
               "same",
               BZLA_SLS_STRAT_BEST_SAME_MOVE,
               "choose move as best move even if its score is greater or "
               "equal (rather than strictly greater) than the score of the "
               "previous best move");
  add_opt_help(mm,
               opts,
               "prop",
               BZLA_SLS_STRAT_ALWAYS_PROP,
               "always choose propagation move (and recover with SLS move in "
               "case of conflict)");
  bzla->options[BZLA_OPT_SLS_STRATEGY].options = opts;

  init_opt(bzla,
           BZLA_OPT_SLS_JUST,
           false,
           true,
           "sls-just",
           0,
           0,
           0,
           1,
           "justification optimization");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_GW,
           false,
           true,
           "sls-move-gw",
           0,
           0,
           0,
           1,
           "select move by altering not only one "
           "but all candidate variables at once");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_RANGE,
           false,
           true,
           "sls-move-range",
           0,
           0,
           0,
           1,
           "try range-wise flips when selecting moves");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_SEGMENT,
           false,
           true,
           "sls-move-segment",
           0,
           0,
           0,
           1,
           "try segment-wise flips when selecting moves");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_RAND_WALK,
           false,
           true,
           "sls-move-rand-walk",
           0,
           0,
           0,
           1,
           "do a random walk (with given probability)");
  init_opt(bzla,
           BZLA_OPT_SLS_PROB_MOVE_RAND_WALK,
           false,
           false,
           "sls-prob-move-rand-walk",
           0,
           100,
           0,
           BZLA_PROB_MAX,
           "probability for choosing random walks "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_RAND_ALL,
           false,
           true,
           "sls-move-rand-all",
           0,
           0,
           0,
           1,
           "randomize all candidate variables (instead of only one) "
           "if no neighbor with better score is found");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_RAND_RANGE,
           false,
           true,
           "sls-move-rand-range",
           0,
           0,
           0,
           1,
           "randomize a range of bits of a randomly chosen candidate "
           "variable if neighbor with better score is found");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_PROP,
           false,
           true,
           "sls-move-prop",
           0,
           0,
           0,
           1,
           "enable propagation moves (with given ratio of propagation "
           "to regular moves)");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_PROP_N_PROP,
           false,
           false,
           "sls-move-prop-n-prop",
           0,
           1,
           0,
           UINT32_MAX,
           "number of prop moves (moves are performed as <n>:m prop "
           "to sls moves");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_PROP_N_SLS,
           false,
           false,
           "sls-move-prop-n-sls",
           0,
           1,
           0,
           UINT32_MAX,
           "number of sls moves (moves are performed as m:<n> prop "
           "to sls moves");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
           false,
           true,
           "sls-move-prop-force-rw",
           0,
           0,
           0,
           1,
           "force random walk if propagation move fails");
  init_opt(bzla,
           BZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
           false,
           true,
           "sls-move-inc-move-test",
           0,
           0,
           0,
           1,
           "use prev. neighbor with better score as base for "
           "next move test");
  init_opt(bzla,
           BZLA_OPT_SLS_USE_RESTARTS,
           false,
           true,
           "sls-use-restarts",
           0,
           1,
           0,
           1,
           "use restarts");
  init_opt(bzla,
           BZLA_OPT_SLS_USE_BANDIT,
           false,
           true,
           "sls-use-bandit",
           0,
           1,
           0,
           1,
           "use bandit scheme for constraint selection");

  /* PROP engine ---------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_PROP_NPROPS,
           false,
           false,
           "prop-nprops",
           0,
           0,
           0,
           UINT32_MAX,
           "number of propagation steps used as a limit for prop engine");
  init_opt(bzla,
           BZLA_OPT_PROP_ENTAILED,
           false,
           false,
           "prop:entailed",
           0,
           BZLA_PROP_ENTAILED_DFLT,
           BZLA_PROP_ENTAILED_MIN,
           BZLA_PROP_ENTAILED_MAX,
           "maintain and prioritize entailed propagations");
  init_opt(bzla,
           BZLA_OPT_PROP_CONST_BITS,
           false,
           true,
           "prop:const-bits",
           0,
           0,
           0,
           1,
           "use constant bits propagation");
  init_opt(bzla,
           BZLA_OPT_PROP_DOMAINS,
           false,
           true,
           "prop:domains",
           0,
           0,
           0,
           1,
           "use domain propagators for inverse value computation");
  init_opt(bzla,
           BZLA_OPT_PROP_USE_RESTARTS,
           false,
           true,
           "prop-use-restarts",
           0,
           0,
           0,
           1,
           "use restarts");
  init_opt(bzla,
           BZLA_OPT_PROP_USE_BANDIT,
           false,
           true,
           "prop-use-bandit",
           0,
           0,
           0,
           1,
           "use bandit scheme for constraint selection");

  init_opt(bzla,
           BZLA_OPT_PROP_PATH_SEL,
           false,
           false,
           "prop-path-sel",
           0,
           BZLA_PROP_PATH_SEL_DFLT,
           BZLA_PROP_PATH_SEL_MIN,
           BZLA_PROP_PATH_SEL_MAX,
           "path selection mode");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "controlling",
               BZLA_PROP_PATH_SEL_CONTROLLING,
               "select path based on controlling inputs");
  add_opt_help(mm,
               opts,
               "essential",
               BZLA_PROP_PATH_SEL_ESSENTIAL,
               "select path based on essential inputs");
  add_opt_help(mm,
               opts,
               "random",
               BZLA_PROP_PATH_SEL_RANDOM,
               "select path based on random inputs");
  bzla->options[BZLA_OPT_PROP_PATH_SEL].options = opts;

  init_opt(bzla,
           BZLA_OPT_PROP_PROB_USE_INV_VALUE,
           false,
           false,
           "prop-prob-use-inv-value",
           0,
           990,
           0,
           BZLA_PROB_MAX,
           "probability for producing inverse rather than consistent values "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_FLIP_COND,
           false,
           false,
           "prop-prob-flip-cond",
           0,
           100,
           0,
           BZLA_PROB_MAX,
           "probability for choosing to flip the condition (rather than "
           "choosing the enabled path) for ITE during path selection "
           "for prop moves (interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_FLIP_COND_CONST,
           false,
           false,
           "prop-prob-flip-cond-const",
           0,
           100,
           0,
           BZLA_PROB_MAX,
           "probability for choosing to flip the condition (rather than "
           "choosing the enabled path) for ITE during path selection "
           "for prop moves if either of the 'then' or 'else' branches "
           "is constant (interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
           false,
           false,
           "prop-flip-cond-const-npathsel",
           0,
           500,
           0,
           INT32_MAX,
           "limit for how often to flip the condition (rather than choosing "
           "the enabled branch) for ITE during path selection before "
           "decreasing or increasing the probability for flipping the "
           "condition if either the 'then' or 'else' branch is constant");
  init_opt(bzla,
           BZLA_OPT_PROP_FLIP_COND_CONST_DELTA,
           false,
           false,
           "prop-flip-cond-const-delta",
           0,
           100,
           0,
           INT32_MAX,
           "delta by which the limit for how often to flip the condition "
           "(rather than choosing the enabled branch) for ITE during path "
           "is decreased or increased");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_SLICE_KEEP_DC,
           false,
           false,
           "prop-prob-slice-keep-dc",
           0,
           500,
           0,
           BZLA_PROB_MAX,
           "probability for keeping the current value of the don't care "
           "bits of the operand of a slice operation "
           "(rather than fully randomizing all of them, "
           "for both inverse and consistent value selection) "
           "if their current value is not kept "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_CONC_FLIP,
           false,
           false,
           "prop-prob-conc-flip",
           0,
           900,
           0,
           BZLA_PROB_MAX,
           "probability for using slice of current assignment with max. "
           "one of its bits flipped (rather than using slice of down "
           "propagated assignment) as result of consistent value selction "
           "for concats (interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_SLICE_FLIP,
           false,
           false,
           "prop-prob-slice-flip",
           0,
           0,
           0,
           BZLA_PROB_MAX,
           "probability for using the current assignment of the operand "
           "of a slice operation with max. one of its bits flipped "
           "(rather than fully randomizing all of them) as a result of "
           "inverse/consistent value selection "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_EQ_FLIP,
           false,
           false,
           "prop-prob-eq-flip",
           0,
           0,
           0,
           BZLA_PROB_MAX,
           "probability for using the current assignment of the selected "
           "node with one of its bits flipped (rather than using a fully "
           "randomized node) in case of inequalities "
           "(for both inverse and consistent value selection) "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_PROB_AND_FLIP,
           false,
           false,
           "prop-prob-and-flip",
           0,
           0,
           0,
           BZLA_PROB_MAX,
           "probability for using the current assignment of the don't care "
           "bits of the selected node with max. one of its bits flipped "
           "(rather fully randomizing all of them) in case of an and operation "
           "(for both inverse and consistent value selection) "
           "(interpreted as <n>/1000)");
  init_opt(bzla,
           BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT,
           false,
           true,
           "prop-no-move-on-conflict",
           0,
           0,
           0,
           1,
           "do not perform a propagation move when encountering a conflict"
           "during inverse computation");

  /* AIGPROP engine ------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_AIGPROP_USE_RESTARTS,
           false,
           true,
           "aigprop-use-restarts",
           0,
           0,
           0,
           1,
           "use restarts");
  init_opt(bzla,
           BZLA_OPT_AIGPROP_USE_BANDIT,
           false,
           true,
           "aigprop-use-bandit",
           0,
           0,
           0,
           1,
           "use bandit scheme for constraint selection");
  init_opt(bzla,
           BZLA_OPT_AIGPROP_NPROPS,
           false,
           false,
           "aigprop:nprops",
           0,
           0,
           0,
           UINT32_MAX,
           "number of propagation steps used as a limit for aigprop engine");

  /* QUANT engine ----------------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_QUANT_DER,
           false,
           true,
           "quant-der",
           0,
           1,
           0,
           1,
           "apply destructive equality resolution");
  init_opt(bzla,
           BZLA_OPT_QUANT_CER,
           false,
           true,
           "quant-cer",
           0,
           1,
           0,
           1,
           "apply constructive equality resolution");
  init_opt(bzla,
           BZLA_OPT_QUANT_MINISCOPE,
           false,
           true,
           "quant-ms",
           0,
           1,
           0,
           1,
           "apply miniscoping");

  init_opt(bzla,
           BZLA_OPT_QUANT_SYNTH,
           false,
           true,
           "quant-synth",
           0,
           BZLA_QUANT_SYNTH_DFLT,
           BZLA_QUANT_SYNTH_MIN,
           BZLA_QUANT_SYNTH_MAX,
           "synthesis mode for Skolem functions");
  opts = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_hash_str, (BzlaCmpPtr) strcmpoptval);
  add_opt_help(mm,
               opts,
               "none",
               BZLA_QUANT_SYNTH_NONE,
               "do not synthesize skolem functions (use model values for "
               "instantiation)");
  add_opt_help(mm,
               opts,
               "el",
               BZLA_QUANT_SYNTH_EL,
               "use enumerative learning to synthesize skolem functions");
  add_opt_help(mm,
               opts,
               "elmc",
               BZLA_QUANT_SYNTH_ELMC,
               "use enumerative learning modulo the predicates in the cone of"
               "influence of the existential variables to synthesize skolem "
               "functions");
  add_opt_help(mm,
               opts,
               "elelmc",
               BZLA_QUANT_SYNTH_EL_ELMC,
               "chain 'el' and 'elmc' approaches to synthesize skolem "
               "functions");
  add_opt_help(mm,
               opts,
               "elmr",
               BZLA_QUANT_SYNTH_ELMR,
               "use enumerative learning modulo the given root constraints "
               "to synthesize skolem functions");
  bzla->options[BZLA_OPT_QUANT_SYNTH].options = opts;

  init_opt(bzla,
           BZLA_OPT_QUANT_DUAL_SOLVER,
           false,
           true,
           "quant-dual",
           0,
           1,
           0,
           1,
           "dual solver");
  init_opt(bzla,
           BZLA_OPT_QUANT_SYNTH_LIMIT,
           false,
           false,
           "quant-synthlimit",
           0,
           10000,
           0,
           UINT32_MAX,
           "number of checks for synthesizing terms");
  init_opt(bzla,
           BZLA_OPT_QUANT_SYNTH_ITE_COMPLETE,
           false,
           true,
           "quant-synthcomplete",
           0,
           1,
           0,
           1,
           "make base case of concrete model constant instead of undef.");
  init_opt(bzla,
           BZLA_OPT_QUANT_SYNTH_QI,
           false,
           true,
           "quant-synthqi",
           0,
           1,
           0,
           1,
           "synthesize quantifier instantiations from counterexamples");

  /* internal options ---------------------------------------------------- */
  init_opt(bzla,
           BZLA_OPT_SORT_EXP,
           true,
           true,
           "sort-exp",
           0,
           1,
           0,
           1,
           "sort commutative expression nodes");
  init_opt(bzla,
           BZLA_OPT_SORT_AIG,
           true,
           true,
           "sort-aig",
           0,
           1,
           0,
           1,
           "sort AIG nodes");
  init_opt(bzla,
           BZLA_OPT_SORT_AIGVEC,
           true,
           true,
           "sort-aigvec",
           0,
           1,
           0,
           1,
           "sort AIG vectors");
  init_opt(bzla,
           BZLA_OPT_AUTO_CLEANUP_INTERNAL,
           true,
           true,
           "auto-cleanup-internal",
           0,
           0,
           0,
           1,
           0);
  init_opt(bzla,
           BZLA_OPT_SIMPLIFY_CONSTRAINTS,
           true,
           true,
           "simplify-constraints",
           0,
           1,
           0,
           1,
           0);
  init_opt(bzla,
           BZLA_OPT_CHK_FAILED_ASSUMPTIONS,
           true,
           true,
           "chk-failed-assumptions",
           0,
           1,
           0,
           1,
           0);
  init_opt(bzla, BZLA_OPT_CHK_MODEL, true, true, "chk-model", 0, 1, 0, 1, 0);
  init_opt(bzla,
           BZLA_OPT_CHK_UNCONSTRAINED,
           true,
           true,
           "chk-unconstrained",
           0,
           1,
           0,
           1,
           0);
  init_opt(bzla,
           BZLA_OPT_PARSE_INTERACTIVE,
           true,
           true,
           "parse-interactive",
           0,
           1,
           0,
           1,
           "interactive parse mode");
  init_opt(bzla,
           BZLA_OPT_SAT_ENGINE_LGL_FORK,
           true,
           true,
           "sat-engine-lgl-fork",
           0,
           1,
           0,
           1,
           "fork lingeling");
  init_opt(bzla,
           BZLA_OPT_SAT_ENGINE_CADICAL_FREEZE,
           true,
           true,
           "sat-engine-cadical-freeze",
           0,
           0,
           0,
           1,
           "use CaDiCaL's freeze/melt API");
  init_opt(bzla,
           BZLA_OPT_SAT_ENGINE_N_THREADS,
           true,
           true,
           "sat-engine-n-threads",
           0,
           1,
           1,
           UINT32_MAX,
           "number of threads to use in the SAT solver");
  init_opt(bzla,
           BZLA_OPT_SIMP_NORMAMLIZE_ADDERS,
           true,
           true,
           "simp-norm-adds",
           0,
           0,
           0,
           1,
           "enable global adder normalization");
  init_opt(bzla,
           BZLA_OPT_DECLSORT_BV_WIDTH,
           true,
           false,
           "declsort-bv-width",
           0,
           0,
           0,
           UINT32_MAX,
           "interpret sorts introduced with declare-sort as bit-vectors of "
           "given width");
  init_opt(bzla,
           BZLA_OPT_QUANT_FIXSYNTH,
           true,
           true,
           "quant-fixsynth",
           0,
           1,
           0,
           1,
           "update current model w.r.t. synthesized skolem function");
  init_opt(bzla,
           BZLA_OPT_RW_ZERO_LOWER_SLICE,
           true,
           true,
           "rw-zero-lower-slice",
           0,
           0,
           0,
           1,
           "enable zero_lower_slice rewrite");
  init_opt(bzla,
           BZLA_OPT_NONDESTR_SUBST,
           true,
           true,
           "nondestr-subst",
           0,
           0,
           0,
           1,
           "enable non-destructive term substitutions");
}

void
clone_data_as_opt_help_ptr(BzlaMemMgr *mm,
                           const void *map,
                           BzlaHashTableData *data,
                           BzlaHashTableData *cloned_data)
{
  assert(data);
  assert(cloned_data);
  (void) map;

  BzlaOptHelp *cloned_hdata;

  BZLA_NEW(mm, cloned_hdata);
  cloned_hdata->val   = ((BzlaOptHelp *) data->as_ptr)->val;
  cloned_hdata->msg   = ((BzlaOptHelp *) data->as_ptr)->msg;
  cloned_data->as_ptr = cloned_hdata;
}

void
bzla_opt_clone_opts(Bzla *bzla, Bzla *clone)
{
  assert(bzla);

  BzlaOption o;

  if (bzla->options)
  {
    BZLA_CNEWN(clone->mm, clone->options, BZLA_OPT_NUM_OPTS);
    for (o = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, o);
         o = bzla_opt_next(bzla, o))
    {
      memcpy(&clone->options[o], &bzla->options[o], sizeof(BzlaOpt));
      if (bzla->options[o].valstr)
        clone->options[o].valstr =
            bzla_mem_strdup(clone->mm, bzla->options[o].valstr);
      if (bzla->options[o].options)
        clone->options[o].options =
            bzla_hashptr_table_clone(clone->mm,
                                     bzla->options[o].options,
                                     bzla_clone_key_as_static_str,
                                     clone_data_as_opt_help_ptr,
                                     0,
                                     0);
    }
  }
  if (bzla->str2opt)
  {
    clone->str2opt = bzla_hashptr_table_clone(clone->mm,
                                              bzla->str2opt,
                                              bzla_clone_key_as_static_str,
                                              bzla_clone_data_as_int,
                                              0,
                                              0);
  }
}

void
bzla_opt_delete_opts(Bzla *bzla)
{
  assert(bzla);

  BzlaOption o;
  BzlaPtrHashTableIterator it;

  if (bzla->options)
  {
    for (o = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, o);
         o = bzla_opt_next(bzla, o))
    {
      if (bzla->options[o].valstr)
      {
        bzla_mem_freestr(bzla->mm, bzla->options[o].valstr);
        bzla->options[o].valstr = 0;
      }
      if (bzla->options[o].options)
      {
        bzla_iter_hashptr_init(&it, bzla->options[o].options);
        while (bzla_iter_hashptr_has_next(&it))
          BZLA_DELETE(bzla->mm,
                      (BzlaOptHelp *) bzla_iter_hashptr_next_data(&it)->as_ptr);
        bzla_hashptr_table_delete(bzla->options[o].options);
      }
    }
    BZLA_DELETEN(bzla->mm, bzla->options, BZLA_OPT_NUM_OPTS);
    bzla->options = 0;
  }
  if (bzla->str2opt)
  {
    bzla_hashptr_table_delete(bzla->str2opt);
    bzla->str2opt = 0;
  }
}

bool
bzla_opt_is_valid(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  (void) bzla;
  return opt < BZLA_OPT_NUM_OPTS;
}

uint32_t
bzla_opt_get(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return bzla->options[opt].val;
}

uint32_t
bzla_opt_get_min(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return bzla->options[opt].min;
}

uint32_t
bzla_opt_get_max(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return bzla->options[opt].max;
}

uint32_t
bzla_opt_get_dflt(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return bzla->options[opt].dflt;
}

const char *
bzla_opt_get_lng(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  if (opt == BZLA_OPT_NUM_OPTS) return BZLA_OPT_NUM_OPTS_STR;
  if (!bzla_opt_is_valid(bzla, opt)) return BZLA_OPT_INVALID_OPT_STR;
  return (const char *) bzla->options[opt].lng;
}

const char *
bzla_opt_get_shrt(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return (const char *) bzla->options[opt].shrt;
}

const char *
bzla_opt_get_desc(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return (const char *) bzla->options[opt].desc;
}

const char *
bzla_opt_get_valstr(const Bzla *bzla, const BzlaOption opt)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  return (const char *) bzla->options[opt].valstr;
}

void
bzla_opt_set(Bzla *bzla, const BzlaOption opt, uint32_t val)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));

  BzlaOpt *o;
  uint32_t oldval;

  o      = &bzla->options[opt];
  oldval = o->val;

  if (opt == BZLA_OPT_SEED)
  {
    bzla_rng_init(&bzla->rng, val);
  }
  else if (opt == BZLA_OPT_ENGINE)
  {
    if (val == BZLA_ENGINE_SLS)
      bzla_opt_set(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT, 1);
    else if (val == BZLA_ENGINE_PROP)
      bzla_opt_set(bzla, BZLA_OPT_PROP_NO_MOVE_ON_CONFLICT, 0);
  }
  else if (opt == BZLA_OPT_MODEL_GEN)
  {
    if (!val && bzla_opt_get(bzla, opt)) bzla_model_delete(bzla);
    if (val && bzla_opt_get(bzla, BZLA_OPT_UCOPT))
    {
      bzla_opt_set(bzla, BZLA_OPT_UCOPT, 0);
      BZLA_MSG(bzla->msg,
               1,
               "Disabling unconstrained optimization since model generation "
               "is enabled");
    }
    assert(!val || !bzla_opt_get(bzla, BZLA_OPT_UCOPT));
  }
  else if (opt == BZLA_OPT_UCOPT)
  {
    if (val && bzla_opt_get(bzla, BZLA_OPT_MODEL_GEN))
    {
      BZLA_MSG(bzla->msg,
               1,
               "Disabling unconstrained optimization since model generation "
               "is enabled");
      val = 0;
    }
    assert(!val || !bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
  }
  else if (opt == BZLA_OPT_SAT_ENGINE)
  {
    if (false
#ifndef BZLA_USE_LINGELING
        || val == BZLA_SAT_ENGINE_LINGELING
#endif
#ifndef BZLA_USE_CADICAL
        || val == BZLA_SAT_ENGINE_CADICAL
#endif
#ifndef BZLA_USE_MINISAT
        || val == BZLA_SAT_ENGINE_MINISAT
#endif
#ifndef BZLA_USE_PICOSAT
        || val == BZLA_SAT_ENGINE_PICOSAT
#endif
#ifndef BZLA_USE_CMS
        || val == BZLA_SAT_ENGINE_CMS
#endif
    )
    {
      val = oldval;
      BZLA_MSG(bzla->msg,
               1,
               "SAT solver %s not compiled in, using %s",
               g_bzla_se_name[val],
               g_bzla_se_name[oldval]);
    }
  }
#ifndef BZLA_USE_LINGELING
  else if (opt == BZLA_OPT_SAT_ENGINE_LGL_FORK)
  {
    val = oldval;
    BZLA_MSG(bzla->msg,
             1,
             "SAT solver Lingeling not compiled in, will not set option "
             "to clone/fork Lingeling");
  }
#endif
#ifndef NDEBUG
  else if (opt == BZLA_OPT_INCREMENTAL)
  {
    assert(bzla->bzla_sat_bzla_called == 0);
  }
  else if (opt == BZLA_OPT_FUN_DUAL_PROP)
  {
    assert(!val || !bzla_opt_get(bzla, BZLA_OPT_FUN_JUST));
  }
  else if (opt == BZLA_OPT_FUN_JUST)
  {
    assert(!val || !bzla_opt_get(bzla, BZLA_OPT_FUN_DUAL_PROP));
  }
  else if (opt == BZLA_OPT_REWRITE_LEVEL)
  {
    assert(val <= 3);
    assert(oldval <= 3);

    /* If the rewrite level changes we need to reset the rewrite cache. */
    if (val != oldval && bzla->rw_cache)
    {
      bzla_rw_cache_reset(bzla->rw_cache);
    }
  }
#endif

  if (val > o->max) val = o->max;
  if (val < o->min) val = o->min;
  o->val = val;
}

void
bzla_opt_set_str(Bzla *bzla, const BzlaOption opt, const char *str)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, opt));
  assert(opt == BZLA_OPT_SAT_ENGINE);

  bzla->options[opt].valstr = bzla_mem_strdup(bzla->mm, str);
}

BzlaOption
bzla_opt_first(Bzla *bzla)
{
  assert(bzla);
  (void) bzla;
  return (BzlaOption) 0;
}

BzlaOption
bzla_opt_next(Bzla *bzla, BzlaOption cur)
{
  assert(bzla);
  assert(bzla_opt_is_valid(bzla, cur));
  (void) bzla;
  return (BzlaOption) cur + 1;
}

#ifndef NBZLALOG
void
bzla_opt_log_opts(Bzla *bzla)
{
  assert(bzla);

  BzlaOption opt;

  for (opt = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, opt);
       opt = bzla_opt_next(bzla, opt))
    BZLALOG(3,
            "set option '%s' to %u",
            bzla_opt_get_lng(bzla, opt),
            bzla_opt_get(bzla, opt));
}
#endif
