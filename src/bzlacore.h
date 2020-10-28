/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLACORE_H_INCLUDED
#define BZLACORE_H_INCLUDED

#include <stdbool.h>

#include "bzlaass.h"
#include "bzlamsg.h"
#include "bzlanode.h"
#include "bzlaopt.h"
#include "bzlarwcache.h"
#include "bzlasat.h"
#include "bzlaslv.h"
#include "bzlasort.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlamem.h"
#include "utils/bzlarng.h"

/*------------------------------------------------------------------------*/

#ifndef BZLA_USE_LINGELING
#define BZLA_DO_NOT_PROCESS_SKELETON
#endif

/*------------------------------------------------------------------------*/

struct BzlaNodeUniqueTable
{
  uint32_t size;
  uint32_t num_elements;
  BzlaNode **chains;
};

typedef struct BzlaNodeUniqueTable BzlaNodeUniqueTable;

struct BzlaCallbacks
{
  struct
  {
    /* the function to use for (checking) termination
     * (we need to distinguish between callbacks from C and Python) */
    int32_t (*termfun)(void *);

    void *fun;   /* termination callback function */
    void *state; /* termination callback function arguments */
  } term;
};

typedef struct BzlaCallbacks BzlaCallbacks;

struct BzlaConstraintStats
{
  uint32_t varsubst;
  uint32_t embedded;
  uint32_t unsynthesized;
  uint32_t synthesized;
};

typedef struct BzlaConstraintStats BzlaConstraintStats;

struct Bzla
{
  void *bitwuzla;

  BzlaMemMgr *mm;
  BzlaSolver *slv;
  BzlaSolver *qslv;
  BzlaCallbacks cbs;

  BzlaBVAssList *bv_assignments;
  BzlaFunAssList *fun_assignments;

  BzlaNodePtrStack nodes_id_table;
  BzlaNodeUniqueTable nodes_unique_table;
  BzlaSortUniqueTable sorts_unique_table;

  BzlaAIGVecMgr *avmgr;

  void *word_blaster;

  BzlaPtrHashTable *symbols;
  BzlaPtrHashTable *node2symbol;

  BzlaPtrHashTable *inputs;
  BzlaPtrHashTable *bv_vars;
  BzlaPtrHashTable *ufs;
  BzlaPtrHashTable *lambdas;
  BzlaPtrHashTable *quantifiers;
  BzlaPtrHashTable *feqs;
  BzlaPtrHashTable *parameterized;

  BzlaPtrHashTable *substitutions;

  BzlaNode *true_exp;

  BzlaIntHashTable *bv_model;
  BzlaIntHashTable *fun_model;
  BzlaNodePtrStack functions_with_model;
  BzlaNodePtrStack outputs; /* used to synthesize BTOR2 outputs */

  uint32_t rec_rw_calls; /* calls for recursive rewriting */
  uint32_t valid_assignments;
  BzlaRwCache *rw_cache;

  int32_t vis_idx; /* file index for visualizing expressions */

  bool inconsistent;
  bool found_constraint_false;

  uint32_t external_refs;        /* external references (library mode) */
  uint32_t bzla_sat_bzla_called; /* how often is bzla_check_sat been called */
  BzlaSolverResult last_sat_result; /* status of last SAT call (SAT/UNSAT) */

  BzlaPtrHashTable *varsubst_constraints;
  BzlaPtrHashTable *embedded_constraints;
  BzlaPtrHashTable *unsynthesized_constraints;
  BzlaPtrHashTable *synthesized_constraints;

  /* maintains simplified assumptions, these are the assumptions that are
   * actually bit-blasted and assumed to the SAT solver */
  BzlaPtrHashTable *assumptions;
  /* maintains the non-simplified (original) assumptions */
  BzlaPtrHashTable *orig_assumptions;

  /* maintain assertions for different contexts push/pop */
  BzlaNodePtrStack assertions;
  /* caches the assertions on stack 'assertions' */
  BzlaIntHashTable *assertions_cache;
  /* saves the number of assertions on each push */
  BzlaUIntStack assertions_trail;
  /* Number of push/pop calls (used for unique symbol prefixes) */
  uint32_t num_push_pop;

#ifndef NDEBUG
  Bzla *clone; /* shadow clone (debugging only) */
#endif

  FILE *apitrace;
  int8_t close_apitrace;

  BzlaOpt *options;
  BzlaPtrHashTable *str2opt;

  BzlaMsg *msg;
  BzlaRNG *rng;

  struct
  {
    uint32_t cur, max;
  } ops[BZLA_NUM_OPS_NODE];

  struct
  {
    uint32_t max_rec_rw_calls;  /* maximum number of recursive rewrite calls */
    uint32_t var_substitutions; /* number substituted vars */
    uint32_t uf_substitutions;  /* num substituted uninterpreted functions */
    uint32_t ec_substitutions;  /* embedded constraint substitutions */
    uint32_t linear_equations;  /* number of linear equations */
    uint32_t gaussian_eliminations; /* number of gaussian eliminations */
    uint32_t eliminated_slices;     /* number of eliminated slices */
    uint32_t skeleton_constraints;  /* number of skeleton constraints */
    uint32_t adds_normalized;       /* number of add chains normalizations */
    uint32_t ands_normalized;       /* number of and chains normalizations */
    uint32_t muls_normalized;       /* number of mul chains normalizations */
    uint32_t ackermann_constraints;
    uint_least64_t prop_apply_lambda; /* number of static props over lambdas */
    uint_least64_t prop_apply_update; /* number of static props over updates */
    uint32_t bv_uc_props;
    uint32_t fun_uc_props;
    uint32_t param_uc_props;
    uint_least64_t lambdas_merged;
    BzlaConstraintStats constraints;
    BzlaConstraintStats oldconstraints;
    uint_least64_t expressions;
    uint_least64_t clone_calls;
    size_t node_bytes_alloc;
    uint_least64_t beta_reduce_calls;
    uint_least64_t betap_reduce_calls;
#ifndef NDEBUG
    BzlaPtrHashTable *rw_rules_applied;
#endif
    uint_least64_t rewrite_synth;
  } stats;

  struct
  {
    double sat;
    double simplify;
    double subst;
    double subst_rebuild;
    double elimapplies;
    double elimites;
    double embedded;
    double slicing;
    double skel;
    double propagate;
    double beta;
    double betap;
    double failed;
    double cloning;
    double synth_exp;
    double model_gen;
    double ucopt;
    double merge;
    double extract;
    double ack;
    double rewrite;
    double occurrence;
  } time;
};

/* Creates new bitwuzla instance. */
Bzla *bzla_new(void);

/* Deletes bitwuzla. */
void bzla_delete(Bzla *bzla);

/* Gets version. */
const char *bzla_version(const Bzla *bzla);

/* Gets id. */
const char *bzla_git_id(const Bzla *bzla);

/* Set termination callback. */
void bzla_set_term(Bzla *bzla, int32_t (*fun)(void *), void *state);

/* Get termination callback state. */
void *bzla_get_term_state(Bzla *bzla);

/* Determine if bitwuzla has been terminated via termination callback. */
int32_t bzla_terminate(Bzla *bzla);

/* Set verbosity message prefix. */
void bzla_set_msg_prefix(Bzla *bzla, const char *prefix);

/* Prints statistics. */
void bzla_print_stats(Bzla *bzla);

/* Reset time statistics. */
void bzla_reset_time(Bzla *bzla);

/* Reset other statistics. */
void bzla_reset_stats(Bzla *bzla);

/* Adds top level constraint. */
void bzla_assert_exp(Bzla *bzla, BzlaNode *exp);

/* Adds assumption. */
void bzla_assume_exp(Bzla *bzla, BzlaNode *exp);

/* Determines if expression has been previously assumed. */
bool bzla_is_assumption_exp(Bzla *bzla, BzlaNode *exp);

/* Determines if assumption is a failed assumption. */
bool bzla_failed_exp(Bzla *bzla, BzlaNode *exp);

/* Adds assumptions as assertions and resets the assumptions. */
void bzla_fixate_assumptions(Bzla *bzla);

/* Resets assumptions */
void bzla_reset_assumptions(Bzla *bzla);

/* Solves instance, but with lemmas on demand limit 'lod_limit' and conflict
 * limit for the underlying SAT solver 'sat_limit'. */
int32_t bzla_check_sat(Bzla *bzla, int32_t lod_limit, int32_t sat_limit);

BzlaSATMgr *bzla_get_sat_mgr(const Bzla *bzla);
BzlaAIGMgr *bzla_get_aig_mgr(const Bzla *bzla);

void bzla_push(Bzla *bzla, uint32_t level);

void bzla_pop(Bzla *bzla, uint32_t level);

/*------------------------------------------------------------------------*/

/* Check whether the sorts of given arguments match the signature of the
 * function. If sorts are correct -1 is returned, otherwise the position of
 * the invalid argument is returned. */
int32_t bzla_fun_sort_check(Bzla *bzla,
                            BzlaNode *args[],
                            uint32_t argc,
                            BzlaNode *fun);

/* Synthesizes expression of arbitrary length to an AIG vector. Adds string
 * back annotation to the hash table, if the hash table is a non zero ptr.
 * The strings in 'data.asStr' are owned by the caller.  The hash table
 * is a map from AIG variables to strings.
 */
BzlaAIGVec *bzla_exp_to_aigvec(Bzla *bzla,
                               BzlaNode *exp,
                               BzlaPtrHashTable *table);

/* Checks for existing substitutions, finds most simplified expression and
 * shortens path to it */
BzlaNode *bzla_simplify_exp(Bzla *bzla, BzlaNode *exp);

void bzla_synthesize_exp(Bzla *bzla,
                         BzlaNode *exp,
                         BzlaPtrHashTable *backannotation);

/* Finds most simplified expression and shortens path to it */
BzlaNode *bzla_node_get_simplified(Bzla *bzla, BzlaNode *exp);

void bzla_release_all_ext_refs(Bzla *bzla);

void bzla_init_substitutions(Bzla *);
void bzla_delete_substitutions(Bzla *);
void bzla_insert_substitution(Bzla *, BzlaNode *, BzlaNode *, bool);
BzlaNode *bzla_find_substitution(Bzla *, BzlaNode *);

// TODO (ma): make these functions public until we have a common framework for
//            calling sat simplify etc.
void bzla_reset_incremental_usage(Bzla *bzla);
void bzla_add_again_assumptions(Bzla *bzla);
void bzla_process_unsynthesized_constraints(Bzla *bzla);
void bzla_insert_unsynthesized_constraint(Bzla *bzla, BzlaNode *constraint);
void bzla_set_simplified_exp(Bzla *bzla, BzlaNode *exp, BzlaNode *simplified);
void bzla_delete_varsubst_constraints(Bzla *bzla);
#endif
