/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2015 Armin Biere.
 *  Copyright (C) 2012-2020 Aina Niemetz.
 *  Copyright (C) 2012-2017 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLANODE_H_INCLUDED
#define BZLANODE_H_INCLUDED

#include "bzlaaigvec.h"
#include "bzlabv.h"
#include "bzlasort.h"
#include "bzlatypes.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlaqueue.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

BZLA_DECLARE_STACK(BzlaNodePtr, BzlaNode *);
BZLA_DECLARE_STACK(BzlaNodePtrPtr, BzlaNode **);
BZLA_DECLARE_QUEUE(BzlaNodePtr, BzlaNode *);

/*------------------------------------------------------------------------*/

/* NOTE: DO NOT REORDER THE INDICES.  CERTAIN MACROS DEPEND ON ORDER.
 *
 * Some code also depends the order of this enum, in particular that
 * BZLA_INVALID_NODE is the first entry.
 * It also relies on that BZLA_PROXY_NODE is BZLA_NUM_OPS_NODE - 1.
 *
 * FURTHER NOTE:
 * binary nodes: [BZLA_BV_AND_NODE, ..., BZLA_LAMBDA_NODE]
 * ternary nodes: [BZLA_BCOND_NODE]
 * commutative nodes: [BZLA_BV_AND_NODE, ..., BZLA_BV_MUL_NODE]
 */
enum BzlaNodeKind
{
  BZLA_INVALID_NODE = 0, /* for debugging purposes only */
  /* -------------------------------------------------------------------- */
  BZLA_BV_CONST_NODE,
  BZLA_FP_CONST_NODE,
  BZLA_RM_CONST_NODE,
  BZLA_VAR_NODE,
  BZLA_PARAM_NODE, /* parameter for lambda expressions */
  /* ------------------------------ unary -------------------------------- */
  BZLA_BV_SLICE_NODE,
  BZLA_FP_ABS_NODE,
  BZLA_FP_ISINF_NODE,
  BZLA_FP_ISNAN_NODE,
  BZLA_FP_ISNEG_NODE,
  BZLA_FP_ISNORM_NODE,
  BZLA_FP_ISPOS_NODE,
  BZLA_FP_ISSUBNORM_NODE,
  BZLA_FP_ISZERO_NODE,
  BZLA_FP_NEG_NODE,
  /* ------------------------------- binary ------------------------------ */
  BZLA_BV_AND_NODE,
  BZLA_BV_EQ_NODE,  /* equality on bit vectors */
  BZLA_FUN_EQ_NODE, /* equality on arrays */
  BZLA_BV_ADD_NODE,
  BZLA_BV_MUL_NODE,
  BZLA_BV_ULT_NODE,
  BZLA_BV_SLL_NODE,
  BZLA_BV_SLT_NODE,
  BZLA_BV_SRL_NODE,
  BZLA_BV_UDIV_NODE,
  BZLA_BV_UREM_NODE,
  BZLA_BV_CONCAT_NODE,
  BZLA_FP_EQ_NODE,
  BZLA_FP_GEQ_NODE,
  BZLA_FP_GT_NODE,
  BZLA_FP_LEQ_NODE,
  BZLA_FP_LT_NODE,
  BZLA_FP_MIN_NODE,
  BZLA_FP_MAX_NODE,
  BZLA_FP_SQRT_NODE,
  BZLA_FP_REM_NODE,
  BZLA_FP_RTI_NODE,
  BZLA_APPLY_NODE,
  BZLA_FORALL_NODE,
  BZLA_EXISTS_NODE,
  BZLA_LAMBDA_NODE, /* lambda expression */
  /* ----------------------------- ternary ------------------------------ */
  BZLA_COND_NODE,
  BZLA_FP_ADD_NODE,
  BZLA_FP_SUB_NODE,
  BZLA_FP_MUL_NODE,
  BZLA_FP_DIV_NODE,
  BZLA_ARGS_NODE,
  BZLA_UPDATE_NODE,
  /* ----------------------------- quaternary --------------------------- */
  BZLA_FP_FMA_NODE,
  /* -------------------------------------------------------------------- */
  BZLA_UF_NODE,
  /* -------------!!! DO NOT ADD ANYTHING BELOW THIS LINE !!!------------ */
  BZLA_PROXY_NODE, /* simplified expression without children */
  BZLA_NUM_OPS_NODE

  // !!! NOTE: do not change this without changing 'g_bzla_op2string' too !!!
};

typedef enum BzlaNodeKind BzlaNodeKind;

extern const char *const g_bzla_op2str[BZLA_NUM_OPS_NODE];

/*------------------------------------------------------------------------*/

#define BZLA_NODE_STRUCT                                                   \
  struct                                                                   \
  {                                                                        \
    BzlaNodeKind kind : 6;        /* kind of expression */                 \
    uint8_t constraint : 1;       /* top level constraint ? */             \
    uint8_t erased : 1;           /* for debugging purposes */             \
    uint8_t disconnected : 1;     /* for debugging purposes */             \
    uint8_t unique : 1;           /* in unique table? */                   \
    uint8_t parameterized : 1;    /* param as sub expression ? */          \
    uint8_t lambda_below : 1;     /* lambda as sub expression ? */         \
    uint8_t quantifier_below : 1; /* quantifier as sub expression ? */     \
    uint8_t apply_below : 1;      /* apply as sub expression ? */          \
    uint8_t propagated : 1;       /* is set during propagation */          \
    uint8_t is_array : 1;         /* function represents array ? */        \
    uint8_t rebuild : 1;          /* indicates whether rebuild is required \
                                     during substitution */                \
    uint8_t arity : 2;            /* arity of operator (at most 3) */      \
    uint8_t bytes;                /* allocated bytes */                    \
    int32_t id;                   /* unique expression id */               \
    uint32_t refs;                /* reference counter (incl. ext_refs) */ \
    uint32_t ext_refs;            /* external references counter */        \
    uint32_t parents;             /* number of parents */                  \
    BzlaSortId sort_id;           /* sort id */                            \
    union                                                                  \
    {                                                                      \
      BzlaAIGVec *av;        /* synthesized AIG vector */                  \
      BzlaPtrHashTable *rho; /* for finding array conflicts */             \
    };                                                                     \
    BzlaNode *next;         /* next in unique table */                     \
    BzlaNode *simplified;   /* simplified expression */                    \
    Bzla *bzla;             /* bitwuzla instance */                        \
    BzlaNode *first_parent; /* head of parent list */                      \
    BzlaNode *last_parent;  /* tail of parent list */                      \
  }

#define BZLA_BV_ADDITIONAL_NODE_STRUCT                             \
  struct                                                           \
  {                                                                \
    BzlaNode *e[3];           /* expression children */            \
    BzlaNode *prev_parent[3]; /* prev in parent list of child i */ \
    BzlaNode *next_parent[3]; /* next in parent list of child i */ \
  }

#define BZLA_FP_ADDITIONAL_NODE_STRUCT                             \
  struct                                                           \
  {                                                                \
    BzlaNode *e[4];           /* expression children */            \
    BzlaNode *prev_parent[4]; /* prev in parent list of child i */ \
    BzlaNode *next_parent[4]; /* next in parent list of child i */ \
  }

/*------------------------------------------------------------------------*/

struct BzlaBVVarNode
{
  BZLA_NODE_STRUCT;
};
typedef struct BzlaBVVarNode BzlaBVVarNode;

struct BzlaUFNode
{
  BZLA_NODE_STRUCT;
};
typedef struct BzlaUFNode BzlaUFNode;

struct BzlaBVConstNode
{
  BZLA_NODE_STRUCT;
  BzlaBitVector *bits;
  BzlaBitVector *invbits;
};
typedef struct BzlaBVConstNode BzlaBVConstNode;

struct BzlaBVSliceNode
{
  BZLA_NODE_STRUCT;
  BZLA_BV_ADDITIONAL_NODE_STRUCT;
  uint32_t upper;
  uint32_t lower;
};
typedef struct BzlaBVSliceNode BzlaBVSliceNode;

struct BzlaBVNode
{
  BZLA_NODE_STRUCT;
  BZLA_BV_ADDITIONAL_NODE_STRUCT;
};
typedef struct BzlaBVNode BzlaBVNode;

/*------------------------------------------------------------------------*/

struct BzlaNode
{
  BZLA_NODE_STRUCT;
  BZLA_BV_ADDITIONAL_NODE_STRUCT;
};

/*------------------------------------------------------------------------*/

struct BzlaFPConstNode
{
  BZLA_NODE_STRUCT;
  BzlaBitVector *exponent;
  BzlaBitVector *significand;
};
typedef struct BzlaFPConstNode BzlaFPConstNode;

struct BzlaFPNode
{
  BZLA_NODE_STRUCT;
  BZLA_FP_ADDITIONAL_NODE_STRUCT;
};
typedef struct BzlaFPNode BzlaFPNode;

/*------------------------------------------------------------------------*/

#define BZLA_BINDER_STRUCT                                   \
  struct                                                     \
  {                                                          \
    BZLA_NODE_STRUCT;                                        \
    BZLA_BV_ADDITIONAL_NODE_STRUCT;                          \
    BzlaNode *body; /* short-cut for curried binder terms */ \
  }

struct BzlaBinderNode
{
  BZLA_BINDER_STRUCT;
};
typedef struct BzlaBinderNode BzlaBinderNode;

struct BzlaLambdaNode
{
  BZLA_BINDER_STRUCT;
  BzlaPtrHashTable *static_rho;
};
typedef struct BzlaLambdaNode BzlaLambdaNode;

struct BzlaParamNode
{
  BZLA_NODE_STRUCT;
  BzlaNode *binder; /* exp that binds the param (lambda, forall, exists) */
  BzlaNode *assigned_exp;
};
typedef struct BzlaParamNode BzlaParamNode;

struct BzlaArgsNode
{
  BZLA_NODE_STRUCT;
  BZLA_BV_ADDITIONAL_NODE_STRUCT;
};
typedef struct BzlaArgsNode BzlaArgsNode;

/*------------------------------------------------------------------------*/

static inline BzlaNode *
bzla_node_set_tag(BzlaNode *node, uintptr_t tag)
{
  assert(tag <= 3);
  return (BzlaNode *) (tag | (uintptr_t) node);
}

static inline BzlaNode *
bzla_node_invert(const BzlaNode *node)
{
  return (BzlaNode *) ((uintptr_t) 1 ^ (uintptr_t) node);
}

static inline BzlaNode *
bzla_node_cond_invert(const BzlaNode *cond, const BzlaNode *node)
{
  return (BzlaNode *) (((uintptr_t) cond & (uintptr_t) 1) ^ (uintptr_t) node);
}

static inline bool
bzla_node_is_inverted(const BzlaNode *node)
{
  return ((uintptr_t) 1 & (uintptr_t) node) != 0;
}

static inline BzlaNode *
bzla_node_real_addr(const BzlaNode *node)
{
  return (BzlaNode *) (~(uintptr_t) 3 & (uintptr_t) node);
}

static inline bool
bzla_node_is_regular(const BzlaNode *node)
{
  return ((uintptr_t) 3 & (uintptr_t) node) == 0;
}

static inline bool
bzla_node_is_synth(const BzlaNode *node)
{
  return bzla_node_real_addr(node)->av != 0;
}

/*------------------------------------------------------------------------*/

static inline bool
bzla_node_is_unary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_SLICE_NODE && kind <= BZLA_FP_NEG_NODE;
}

static inline bool
bzla_node_is_binary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_AND_NODE && kind <= BZLA_LAMBDA_NODE;
}

static inline bool
bzla_node_is_binary_commutative_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_AND_NODE && kind <= BZLA_BV_MUL_NODE;
}

static inline bool
bzla_node_is_ternary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_COND_NODE && kind <= BZLA_UPDATE_NODE;
}

static inline bool
bzla_node_is_unary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_unary_kind(bzla_node_real_addr(exp)->kind);
}

static inline bool
bzla_node_is_binary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_binary_kind(bzla_node_real_addr(exp)->kind);
}

static inline bool
bzla_node_is_binary_commutative(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_binary_commutative_kind(bzla_node_real_addr(exp)->kind);
}

static inline bool
bzla_node_is_ternary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_ternary_kind(bzla_node_real_addr(exp)->kind);
}

static inline bool
bzla_node_is_invalid(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_INVALID_NODE;
}

static inline bool
bzla_node_is_proxy(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_PROXY_NODE;
}

static inline bool
bzla_node_is_bv_const(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_sort_is_bv(exp->bzla, exp->sort_id)
         && exp->kind == BZLA_BV_CONST_NODE;
}

static inline bool
bzla_node_is_bv_var(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_sort_is_bv(exp->bzla, exp->sort_id) && exp->kind == BZLA_VAR_NODE;
}

static inline bool
bzla_node_is_bv_eq(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_EQ_NODE;
}

static inline bool
bzla_node_is_fun_eq(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FUN_EQ_NODE;
}

static inline bool
bzla_node_is_bv_and(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_AND_NODE;
}

static inline bool
bzla_node_is_bv_ult(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_ULT_NODE;
}

static inline bool
bzla_node_is_bv_slt(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SLT_NODE;
}

static inline bool
bzla_node_is_bv_add(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_ADD_NODE;
}

static inline bool
bzla_node_is_bv_mul(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_MUL_NODE;
}

static inline bool
bzla_node_is_bv_udiv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_UDIV_NODE;
}

static inline bool
bzla_node_is_bv_urem(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_UREM_NODE;
}

static inline bool
bzla_node_is_bv_slice(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SLICE_NODE;
}

static inline bool
bzla_node_is_bv_concat(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_CONCAT_NODE;
}

static inline bool
bzla_node_is_cond(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_COND_NODE;
}

bool bzla_node_is_bv_cond(const BzlaNode *exp);
bool bzla_node_is_fun_cond(const BzlaNode *exp);

static inline bool
bzla_node_is_uf(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_UF_NODE;
}

static inline bool
bzla_node_is_array(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->is_array == 1;
}

static inline bool
bzla_node_is_const_array(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_array(exp) && exp->kind == BZLA_LAMBDA_NODE
         && !bzla_node_real_addr(exp->e[1])->parameterized;
}

static inline bool
bzla_node_is_forall(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FORALL_NODE;
}

static inline bool
bzla_node_is_exists(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_EXISTS_NODE;
}

static inline bool
bzla_node_is_quantifier(const BzlaNode *exp)
{
  return bzla_node_is_forall(exp) || bzla_node_is_exists(exp);
}

static inline bool
bzla_node_is_lambda(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_LAMBDA_NODE;
}

static inline bool
bzla_node_is_binder(const BzlaNode *exp)
{
  return bzla_node_is_quantifier(exp) || bzla_node_is_lambda(exp);
}

static inline bool
bzla_node_is_update(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_UPDATE_NODE;
}

static inline bool
bzla_node_is_fun(const BzlaNode *exp)
{
  return bzla_node_is_lambda(exp) || bzla_node_is_uf(exp)
         || bzla_node_is_fun_cond(exp) || bzla_node_is_update(exp);
}

static inline bool
bzla_node_is_uf_array(const BzlaNode *exp)
{
  return bzla_node_is_uf(exp)
         && ((BzlaUFNode *) bzla_node_real_addr(exp))->is_array;
}

static inline bool
bzla_node_is_param(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_PARAM_NODE;
}

static inline bool
bzla_node_is_args(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_ARGS_NODE;
}

static inline bool
bzla_node_is_apply(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_APPLY_NODE;
}

static inline bool
bzla_node_is_array_or_bv_eq(const BzlaNode *exp)
{
  return bzla_node_is_fun_eq(exp) || bzla_node_is_bv_eq(exp);
}

static inline bool
bzla_node_is_bv_sll(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SLL_NODE;
}

static inline bool
bzla_node_is_bv_srl(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SRL_NODE;
}

/*------------------------------------------------------------------------*/

bool bzla_node_is_bv_const_zero(Bzla *bzla, BzlaNode *exp);
bool bzla_node_is_bv_const_one(Bzla *bzla, BzlaNode *exp);
bool bzla_node_is_bv_const_ones(Bzla *bzla, BzlaNode *exp);

bool bzla_node_is_bv_const_min_signed(Bzla *bzla, BzlaNode *exp);
bool bzla_node_is_bv_const_max_signed(Bzla *bzla, BzlaNode *exp);

bool bzla_node_bv_is_neg(Bzla *bzla, BzlaNode *exp, BzlaNode **res);

/*------------------------------------------------------------------------*/

/* Get the id of an expression (negative if exp is inverted). */
static inline int32_t
bzla_node_get_id(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_inverted(exp) ? -bzla_node_real_addr(exp)->id : exp->id;
}

static inline int32_t
bzla_node_get_tag(const BzlaNode *exp)
{
  return (int32_t)((uintptr_t) 3 & (uintptr_t) exp);
}

/*========================================================================*/

/* Copies expression (increments reference counter). */
BzlaNode *bzla_node_copy(Bzla *bzla, BzlaNode *exp);

/* Releases expression (decrements reference counter). */
void bzla_node_release(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/* Get the id of the sort of the given node.
 * Do not release the returned sort. */
static inline BzlaSortId
bzla_node_get_sort_id(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->sort_id;
}

/* Set the sort id of the given node. */
static inline void
bzla_node_set_sort_id(BzlaNode *exp, BzlaSortId id)
{
  assert(exp);
  bzla_node_real_addr(exp)->sort_id = id;
}

/*------------------------------------------------------------------------*/

void bzla_node_inc_ext_ref_counter(Bzla *bzla, BzlaNode *e);

void bzla_node_dec_ext_ref_counter(Bzla *bzla, BzlaNode *e);

/*------------------------------------------------------------------------*/

/* Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified */
void bzla_node_set_to_proxy(Bzla *bzla, BzlaNode *exp);

static inline bool
bzla_node_is_simplified(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->simplified != 0;
}

/*------------------------------------------------------------------------*/

/* Set parsed id (BTOR format only, needed for model output). */
void bzla_node_set_bzla_id(Bzla *bzla, BzlaNode *exp, int32_t id);

/* Get parsed id (BTOR format only, needed for model output). */
int32_t bzla_node_get_bzla_id(BzlaNode *exp);

/* Get the exp (belonging to instance 'bzla') that matches given id.
 * Note: The main difference to 'bzla_node_match_by_id' is that this function
 *       does NOT increase the reference counter, and passing and 'id' < 0
 *       will return an inverted node */
BzlaNode *bzla_node_get_by_id(Bzla *bzla, int32_t id);

/* Retrieve the exp (belonging to instance 'bzla') that matches given id.
 * Note: increases ref counter of returned match!
 * Note: 'id' must be greater 0
 *       -> will not return a conditionally inverted node */
BzlaNode *bzla_node_match_by_id(Bzla *bzla, int32_t id);

/*------------------------------------------------------------------------*/

/* Gets the symbol of an expression. */
char *bzla_node_get_symbol(Bzla *bzla, const BzlaNode *exp);

/* Sets the symbol of an expression. */
void bzla_node_set_symbol(Bzla *bzla, BzlaNode *exp, const char *symbol);

/* Get the exp (belonging to instance 'bzla') that matches given symbol.
 * Note: does NOT increase the ref counter */
BzlaNode *bzla_node_get_by_symbol(Bzla *bzla, const char *sym);

/* Retrieve the exp (belonging to instance 'bzla') that matches given symbol.
 * Note: increases ref counter of returned match! */
BzlaNode *bzla_node_match_by_symbol(Bzla *bzla, const char *sym);

/*------------------------------------------------------------------------*/

/* Retrieve the exp (belonging to instance 'bzla') that matches given
 * expression by id. This is intended to be used for handling expressions
 * of a cloned instance (in a clone and its parent, expressions
 * with the same id correspond to each other, i.e. initially, the cloned
 * expression is an identical copy of the parent expression).
 * (Note: increases ref counter of return match!) */
BzlaNode *bzla_node_match(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/* Compares two expression pairs by ID */
int32_t bzla_node_compare_by_id(const BzlaNode *exp0, const BzlaNode *exp1);
/* Compare function for expressions (by ID) to be used for qsort */
int32_t bzla_node_compare_by_id_qsort_desc(const void *p, const void *q);
int32_t bzla_node_compare_by_id_qsort_asc(const void *p, const void *q);

/* Hashes expression by ID */
uint32_t bzla_node_hash_by_id(const BzlaNode *exp);

/*------------------------------------------------------------------------*/

/* Get the bit width of a bit vector expression */
uint32_t bzla_node_bv_get_width(Bzla *bzla, const BzlaNode *exp);
/* Get the bit width of the array elements / function return value. */
uint32_t bzla_node_fun_get_width(Bzla *bzla, const BzlaNode *exp);
/* Get the index width of an array expression */
uint32_t bzla_node_array_get_index_width(Bzla *bzla, const BzlaNode *e_array);

/*------------------------------------------------------------------------*/

BzlaBitVector *bzla_node_bv_const_get_bits(BzlaNode *exp);
BzlaBitVector *bzla_node_bv_const_get_invbits(BzlaNode *exp);
void bzla_node_bv_const_set_bits(BzlaNode *exp, BzlaBitVector *bits);
void bzla_node_bv_const_set_invbits(BzlaNode *exp, BzlaBitVector *bits);

/*------------------------------------------------------------------------*/

/* Gets the number of arguments of lambda expression 'exp'. */
uint32_t bzla_node_fun_get_arity(Bzla *bzla, BzlaNode *exp);

/* Gets the number of arguments of an argument expression 'exp'. */
uint32_t bzla_node_args_get_arity(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

BzlaNode *bzla_node_binder_get_body(BzlaNode *binder);
void bzla_node_binder_set_body(BzlaNode *binder, BzlaNode *body);

/*------------------------------------------------------------------------*/

BzlaPtrHashTable *bzla_node_lambda_get_static_rho(BzlaNode *lambda);

void bzla_node_lambda_set_static_rho(BzlaNode *lambda,
                                     BzlaPtrHashTable *static_rho);

BzlaPtrHashTable *bzla_node_lambda_copy_static_rho(Bzla *bzla,
                                                   BzlaNode *lambda);

void bzla_node_lambda_delete_static_rho(Bzla *bzla, BzlaNode *lambda);

/*------------------------------------------------------------------------*/

uint32_t bzla_node_bv_slice_get_upper(const BzlaNode *slice);
uint32_t bzla_node_bv_slice_get_lower(const BzlaNode *slice);

/*------------------------------------------------------------------------*/

BzlaNode *bzla_node_param_get_binder(BzlaNode *param);

void bzla_node_param_set_binder(BzlaNode *param, BzlaNode *lambda);

bool bzla_node_param_is_bound(BzlaNode *param);

bool bzla_node_param_is_exists_var(BzlaNode *param);

bool bzla_node_param_is_forall_var(BzlaNode *param);

BzlaNode *bzla_node_param_get_assigned_exp(BzlaNode *param);

BzlaNode *bzla_node_param_set_assigned_exp(BzlaNode *param, BzlaNode *exp);

/*------------------------------------------------------------------------*/

BzlaNode *bzla_node_create_bv_const(Bzla *bzla, const BzlaBitVector *bits);

BzlaNode *bzla_node_create_var(Bzla *bzla, BzlaSortId sort, const char *symbol);

BzlaNode *bzla_node_create_uf(Bzla *bzla, BzlaSortId sort, const char *symbol);

BzlaNode *bzla_node_create_param(Bzla *bzla,
                                 BzlaSortId sort,
                                 const char *symbol);

BzlaNode *bzla_node_create_bv_slice(Bzla *bzla,
                                    BzlaNode *exp,
                                    uint32_t upper,
                                    uint32_t lower);

BzlaNode *bzla_node_create_bv_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_bv_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

BzlaNode *bzla_node_create_cond(Bzla *bzla,
                                BzlaNode *e_cond,
                                BzlaNode *e_if,
                                BzlaNode *e_else);

BzlaNode *bzla_node_create_args(Bzla *bzla, BzlaNode *args[], uint32_t argc);

BzlaNode *bzla_node_create_apply(Bzla *bzla, BzlaNode *fun, BzlaNode *args);

BzlaNode *bzla_node_create_lambda(Bzla *bzla, BzlaNode *param, BzlaNode *body);

BzlaNode *bzla_node_create_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body);

BzlaNode *bzla_node_create_quantifier(Bzla *bzla,
                                      BzlaNodeKind kind,
                                      BzlaNode *param,
                                      BzlaNode *body);

BzlaNode *bzla_node_create_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body);

BzlaNode *bzla_node_create_update(Bzla *bzla,
                                  BzlaNode *fun,
                                  BzlaNode *args,
                                  BzlaNode *value);

/*========================================================================*/

struct BzlaNodePair
{
  BzlaNode *node1;
  BzlaNode *node2;
};

typedef struct BzlaNodePair BzlaNodePair;

BzlaNodePair *bzla_node_pair_new(Bzla *, BzlaNode *, BzlaNode *);

void bzla_node_pair_delete(Bzla *, BzlaNodePair *);

uint32_t bzla_node_pair_hash(const BzlaNodePair *);

int32_t bzla_node_pair_compare(const BzlaNodePair *, const BzlaNodePair *);

#endif
