/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLANODE_H_INCLUDED
#define BZLANODE_H_INCLUDED

#include "bzlaaigvec.h"
#include "bzlabv.h"
#include "bzlafp.h"
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
  BZLA_FP_IS_INF_NODE,
  BZLA_FP_IS_NAN_NODE,
  BZLA_FP_IS_NEG_NODE,
  BZLA_FP_IS_NORM_NODE,
  BZLA_FP_IS_POS_NODE,
  BZLA_FP_IS_SUBNORM_NODE,
  BZLA_FP_IS_ZERO_NODE,
  BZLA_FP_NEG_NODE,
  BZLA_FP_TO_FP_BV_NODE,
  /* ------------------------------- binary ------------------------------ */
  BZLA_BV_AND_NODE,
  BZLA_BV_EQ_NODE, /* equality over bit vectors */
  BZLA_BV_ADD_NODE,
  BZLA_BV_MUL_NODE,
  BZLA_BV_ULT_NODE,
  BZLA_BV_SLL_NODE,
  BZLA_BV_SLT_NODE,
  BZLA_BV_SRL_NODE,
  BZLA_BV_UDIV_NODE,
  BZLA_BV_UREM_NODE,
  BZLA_BV_CONCAT_NODE,
  BZLA_FP_EQ_NODE, /* (regular) equality over floating-points */
  BZLA_FP_LTE_NODE,
  BZLA_FP_LT_NODE,
  BZLA_FP_MIN_NODE,
  BZLA_FP_MAX_NODE,
  BZLA_FP_SQRT_NODE,
  BZLA_FP_REM_NODE,
  BZLA_FP_RTI_NODE,
  BZLA_FP_TO_SBV_NODE,
  BZLA_FP_TO_UBV_NODE,
  BZLA_FP_TO_FP_FP_NODE,
  BZLA_FP_TO_FP_SBV_NODE,
  BZLA_FP_TO_FP_UBV_NODE,
  BZLA_RM_EQ_NODE,  /* equality over rounding modes */
  BZLA_FUN_EQ_NODE, /* equality over uf/arrays */
  BZLA_APPLY_NODE,
  BZLA_FORALL_NODE,
  BZLA_EXISTS_NODE,
  BZLA_LAMBDA_NODE, /* lambda expression */
  /* ----------------------------- ternary ------------------------------ */
  BZLA_COND_NODE,
  BZLA_FP_ADD_NODE,
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
    uint8_t arity : 3;            /* arity of operator (at most 3) */      \
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

#define BZLA_NODE_MAX_CHILDREN 4

#define BZLA_ADDITIONAL_NODE_STRUCT                                          \
  struct                                                                     \
  {                                                                          \
    BzlaNode *e[BZLA_NODE_MAX_CHILDREN];           /* expression children */ \
    BzlaNode *prev_parent[BZLA_NODE_MAX_CHILDREN]; /* prev in parent list of \
                                                      child i */             \
    BzlaNode *next_parent[BZLA_NODE_MAX_CHILDREN]; /* next in parent list of \
                                                      child i */             \
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
  BZLA_ADDITIONAL_NODE_STRUCT;
  uint32_t upper;
  uint32_t lower;
};
typedef struct BzlaBVSliceNode BzlaBVSliceNode;

/*------------------------------------------------------------------------*/

struct BzlaNode
{
  BZLA_NODE_STRUCT;
  BZLA_ADDITIONAL_NODE_STRUCT;
};

/*------------------------------------------------------------------------*/

struct BzlaRMConstNode
{
  BZLA_NODE_STRUCT;
  BzlaRoundingMode rm;
};
typedef struct BzlaRMConstNode BzlaRMConstNode;

/*------------------------------------------------------------------------*/

struct BzlaFPConstNode
{
  BZLA_NODE_STRUCT;
  void *fp;
};
typedef struct BzlaFPConstNode BzlaFPConstNode;

/*------------------------------------------------------------------------*/

#define BZLA_BINDER_STRUCT                                   \
  struct                                                     \
  {                                                          \
    BZLA_NODE_STRUCT;                                        \
    BZLA_ADDITIONAL_NODE_STRUCT;                             \
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
  BZLA_ADDITIONAL_NODE_STRUCT;
};
typedef struct BzlaArgsNode BzlaArgsNode;

/*------------------------------------------------------------------------*/

/** Return true if given node is a bit-vector node. */
bool bzla_node_is_bv(Bzla *bzla, const BzlaNode *exp);
/** Return true if given node is a rounding mode node. */
bool bzla_node_is_rm(Bzla *bzla, const BzlaNode *exp);
/** Return true if given node is a floating-point node. */
bool bzla_node_is_fp(Bzla *bzla, const BzlaNode *exp);
/** Return true if given node needs to be word-blasted. */
bool bzla_node_fp_needs_word_blast(Bzla *bzla, const BzlaNode *exp);

/*------------------------------------------------------------------------*/

/**
 * Tag parent 'node' (to be linked in 'first_parent', 'last_parent',
 * 'prev_parent[tag]' and 'next_parent[tag] of the child node) with
 * its index to identify its position in the 'parents' array of the child node.
 */
static inline BzlaNode *
bzla_node_set_tag(BzlaNode *node, uintptr_t tag)
{
  assert(tag <= 3);
  return (BzlaNode *) (tag | (uintptr_t) node);
}

/** Invert node. 'Inverted nodes' are node pointers with LSB=1. */
static inline BzlaNode *
bzla_node_invert(const BzlaNode *node)
{
  return (BzlaNode *) ((uintptr_t) 1 ^ (uintptr_t) node);
}

/** Invert node if the LSB of 'cond' is 1. */
static inline BzlaNode *
bzla_node_cond_invert(const BzlaNode *cond, const BzlaNode *node)
{
  return (BzlaNode *) (((uintptr_t) cond & (uintptr_t) 1) ^ (uintptr_t) node);
}

/** Return true if given node is inverted. */
static inline bool
bzla_node_is_inverted(const BzlaNode *node)
{
  return ((uintptr_t) 1 & (uintptr_t) node) != 0;
}

/**
 * Get real (untagged) pointer of given node.
 *
 * Node pointers can be tagged as inverted (any) or with the index position in
 * the parents array (if they are accessed via 'first_parent', 'last_parent',
 * 'prev_parent[]', 'next_parent[]').
 */
static inline BzlaNode *
bzla_node_real_addr(const BzlaNode *node)
{
  return (BzlaNode *) (~(uintptr_t) 3 & (uintptr_t) node);
}

/** Return true if given node is untagged. */
static inline bool
bzla_node_is_regular(const BzlaNode *node)
{
  return ((uintptr_t) 3 & (uintptr_t) node) == 0;
}

/** Return true if given node is synthesized to AIG layer. */
static inline bool
bzla_node_is_synth(const BzlaNode *node)
{
  return bzla_node_real_addr(node)->av != 0;
}

/** Return number of external references. */
static inline uint32_t
bzla_node_get_ext_refs(const BzlaNode *node)
{
  return bzla_node_real_addr(node)->ext_refs;
}

/** Return associated bzla instance. */
static inline Bzla *
bzla_node_get_bzla(const BzlaNode *node)
{
  return bzla_node_real_addr(node)->bzla;
}

/*------------------------------------------------------------------------*/

/** Return true if given kind is a unary kind (arity == 1). */
static inline bool
bzla_node_is_unary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_SLICE_NODE && kind <= BZLA_FP_NEG_NODE;
}

/** Return true if given kind is a binary kind (arity == 2). */
static inline bool
bzla_node_is_binary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_AND_NODE && kind <= BZLA_LAMBDA_NODE;
}

/**
 * Return true if given kind is a binary commutative bit-vector kind (arity ==
 * 2).
 */
static inline bool
bzla_node_is_binary_commutative_bv_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_BV_AND_NODE && kind <= BZLA_BV_MUL_NODE;
}

/**
 * Return true if given kind is a binary commutative floating-point kind
 * (arity == 2).
 */
static inline bool
bzla_node_is_binary_commutative_fp_kind(BzlaNodeKind kind)
{
  return kind == BZLA_FP_ADD_NODE || kind == BZLA_FP_MUL_NODE;
}

/** Return true if given kind is a ternary kind (arity == 3). */
static inline bool
bzla_node_is_ternary_kind(BzlaNodeKind kind)
{
  return kind >= BZLA_COND_NODE && kind <= BZLA_UPDATE_NODE;
}

/**
 * Return true if given node is a floating-point to_fp kind.
 */
static inline bool
bzla_node_is_fp_to_fp_kind(BzlaNodeKind kind)
{
  return kind == BZLA_FP_TO_FP_FP_NODE || kind == BZLA_FP_TO_FP_BV_NODE
         || kind == BZLA_FP_TO_FP_SBV_NODE || kind == BZLA_FP_TO_FP_UBV_NODE;
}

/** Return true if given node kind is indexed. */
static inline bool
bzla_node_is_indexed_kind(BzlaNodeKind kind)
{
  return kind == BZLA_BV_SLICE_NODE || kind == BZLA_FP_TO_UBV_NODE
         || kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_FP_FP_NODE
         || kind == BZLA_FP_TO_FP_BV_NODE || kind == BZLA_FP_TO_FP_SBV_NODE
         || kind == BZLA_FP_TO_FP_UBV_NODE;
}

/*------------------------------------------------------------------------*/

/** Return true if given node is of unary kind (arity == 1). */
static inline bool
bzla_node_is_unary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_unary_kind(bzla_node_real_addr(exp)->kind);
}

/** Return true if given node is of binary kind (arity == 2). */
static inline bool
bzla_node_is_binary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_binary_kind(bzla_node_real_addr(exp)->kind);
}

/** Return true if given node is of binary commutative kind (arity == 2). */
static inline bool
bzla_node_is_binary_commutative(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_binary_commutative_bv_kind(
      bzla_node_real_addr(exp)->kind);
}

/** Return true if given node is of ternary kind (arity == 3). */
static inline bool
bzla_node_is_ternary(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_ternary_kind(bzla_node_real_addr(exp)->kind);
}

/** Return true if given node is invalid. */
static inline bool
bzla_node_is_invalid(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_INVALID_NODE;
}

/** Return true if given node is proxy node. */
static inline bool
bzla_node_is_proxy(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_PROXY_NODE;
}

/** Return true if given node is indexed. */
static inline bool
bzla_node_is_indexed(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_indexed_kind(bzla_node_real_addr(exp)->kind);
}

/*------------------------------------------------------------------------*/

/** Return true if given node is a bit-vector constant node. */
static inline bool
bzla_node_is_bv_const(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_bv(exp->bzla, exp) && exp->kind == BZLA_BV_CONST_NODE;
}

/** Return true if given node is a rounding mode constant node. */
static inline bool
bzla_node_is_rm_const(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_rm(exp->bzla, exp) && exp->kind == BZLA_RM_CONST_NODE;
}

/** Return true if given node is a floating-point constant node. */
static inline bool
bzla_node_is_fp_const(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_fp(exp->bzla, exp) && exp->kind == BZLA_FP_CONST_NODE;
}

/*------------------------------------------------------------------------*/

/**
 * Return true if given node is a bit-vector variable (first-order constant).
 */
static inline bool
bzla_node_is_var(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return exp->kind == BZLA_VAR_NODE;
}

/**
 * Return true if given node is a bit-vector variable (first-order constant).
 */
static inline bool
bzla_node_is_bv_var(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_bv(exp->bzla, exp) && exp->kind == BZLA_VAR_NODE;
}

/**
 * Return true if given node is a rounding mode variable (first-order
 * constant).
 */
static inline bool
bzla_node_is_rm_var(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_rm(exp->bzla, exp) && exp->kind == BZLA_VAR_NODE;
}

/**
 * Return true if given node is a floating-point variable (first-order
 * constant).
 */
static inline bool
bzla_node_is_fp_var(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_fp(exp->bzla, exp) && exp->kind == BZLA_VAR_NODE;
}

/*------------------------------------------------------------------------*/

/** Return true if given node is a bit-vector equality. */
static inline bool
bzla_node_is_bv_eq(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_EQ_NODE;
}

/** Return true if given node is a function equality. */
static inline bool
bzla_node_is_fun_eq(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FUN_EQ_NODE;
}

/*------------------------------------------------------------------------*/

/** Return true if given node is a bvneg node. */
bool bzla_node_bv_is_neg(Bzla *bzla, BzlaNode *exp, BzlaNode **res);

/** Return true if given node is a bit-vector bvand node. */
static inline bool
bzla_node_is_bv_and(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_AND_NODE;
}

/** Return true if given node is a bit-vector bvult node. */
static inline bool
bzla_node_is_bv_ult(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_ULT_NODE;
}

/** Return true if given node is a bit-vector bvadd node. */
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

/** Return true if given node is a bit-vector bvmul node. */
static inline bool
bzla_node_is_bv_mul(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_MUL_NODE;
}

/** Return true if given node is a bit-vector bvudiv node. */
static inline bool
bzla_node_is_bv_udiv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_UDIV_NODE;
}

/** Return true if given node is a bit-vector bvurem node. */
static inline bool
bzla_node_is_bv_urem(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_UREM_NODE;
}

/** Return true if given node is a bit-vector slice node. */
static inline bool
bzla_node_is_bv_slice(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SLICE_NODE;
}

/** Return true if given node is a bit-vector concat node. */
static inline bool
bzla_node_is_bv_concat(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_BV_CONCAT_NODE;
}

/** Return true if given node is a bit-vector logical shift left node. */
static inline bool
bzla_node_is_bv_sll(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SLL_NODE;
}

/** Return true if given node is a bit-vector logical shift right node. */
static inline bool
bzla_node_is_bv_srl(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->kind == BZLA_BV_SRL_NODE;
}

/*------------------------------------------------------------------------*/

/** Return true if given node is a floating-point fp.abs node. */
static inline bool
bzla_node_is_fp_abs(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_ABS_NODE;
}

/** Return true if given node is a floating-point fp.neg node. */
static inline bool
bzla_node_is_fp_neg(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_NEG_NODE;
}

/** Return true if given node is a floating-point fp.fp.isNormal node. */
static inline bool
bzla_node_is_fp_is_normal(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_NORM_NODE;
}

/** Return true if given node is a floating-point fp.fp.isSubnormal node. */
static inline bool
bzla_node_is_fp_is_subnormal(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_SUBNORM_NODE;
}

/** Return true if given node is a floating-point fp.fp.isZero node. */
static inline bool
bzla_node_is_fp_is_zero(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_ZERO_NODE;
}

/** Return true if given node is a floating-point fp.fp.isInfinite node. */
static inline bool
bzla_node_is_fp_is_inf(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_INF_NODE;
}

/** Return true if given node is a floating-point fp.fp.isNaN node. */
static inline bool
bzla_node_is_fp_is_nan(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_NAN_NODE;
}

/** Return true if given node is a floating-point fp.fp.isNegative node. */
static inline bool
bzla_node_is_fp_is_neg(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_NEG_NODE;
}

/** Return true if given node is a floating-point fp.fp.isPositive node. */
static inline bool
bzla_node_is_fp_is_pos(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_IS_POS_NODE;
}

/** Return true if given node is a floating-point fp.leq node. */
static inline bool
bzla_node_is_fp_lte(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_LTE_NODE;
}

/** Return true if given node is a floating-point fp.lt node. */
static inline bool
bzla_node_is_fp_lt(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_LT_NODE;
}

/** Return true if given node is a floating-point fp.min node. */
static inline bool
bzla_node_is_fp_min(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_MIN_NODE;
}

/** Return true if given node is a floating-point fp.max node. */
static inline bool
bzla_node_is_fp_max(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_MAX_NODE;
}

/** Return true if given node is a floating-point fp.rem node. */
static inline bool
bzla_node_is_fp_rem(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_REM_NODE;
}

/** Return true if given node is a floating-point fp.sqrt node. */
static inline bool
bzla_node_is_fp_sqrt(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_SQRT_NODE;
}

/** Return true if given node is a floating-point fp.roundToIntegral node. */
static inline bool
bzla_node_is_fp_rti(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_RTI_NODE;
}

/** Return true if given node is a floating-point fp.add node. */
static inline bool
bzla_node_is_fp_add(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_ADD_NODE;
}

/** Return true if given node is a floating-point fp.mul node. */
static inline bool
bzla_node_is_fp_mul(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_MUL_NODE;
}

/** Return true if given node is a floating-point fp.div node. */
static inline bool
bzla_node_is_fp_div(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_DIV_NODE;
}

/** Return true if given node is a floating-point fp.fma node. */
static inline bool
bzla_node_is_fp_fma(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_FMA_NODE;
}

/** Return true if given node is a floating-point fp.to_sbv node. */
static inline bool
bzla_node_is_fp_to_sbv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_SBV_NODE;
}

/** Return true if given node is a floating-point fp.to_ubv node. */
static inline bool
bzla_node_is_fp_to_ubv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_UBV_NODE;
}

/** Return true if given node is a floating-point to_fp from IEEE bv node. */
static inline bool
bzla_node_is_fp_to_fp_from_bv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_FP_BV_NODE;
}

/** Return true if given node is a floating-point to_fp from fp node. */
static inline bool
bzla_node_is_fp_to_fp_from_fp(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_FP_FP_NODE;
}

/**
 * Return true if given node is a floating-point to_fp from machine int
 * (signed bit-vector) node.
 */
static inline bool
bzla_node_is_fp_to_fp_from_sbv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_FP_SBV_NODE;
}

/**
 * Return true if given node is a floating-point to_fp from unsigned machine int
 * (unsigned bit-vector) node.
 */
static inline bool
bzla_node_is_fp_to_fp_from_ubv(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FP_TO_FP_UBV_NODE;
}

/*------------------------------------------------------------------------*/

/** Return true if given node is an if-then-else node. */
static inline bool
bzla_node_is_cond(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_COND_NODE;
}

/** Return true if given node is an if-then-else node over bit-vector nodes. */
bool bzla_node_is_bv_cond(const BzlaNode *exp);

/** Return true if given node is an if-then-else node over function nodes. */
bool bzla_node_is_fun_cond(const BzlaNode *exp);

/** Return true if given node is an uninterpreted function node. */
static inline bool
bzla_node_is_uf(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_UF_NODE;
}

/** Return true if given node is an array node. */
static inline bool
bzla_node_is_array(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->is_array == 1;
}

/** Return true if given node is a constant array node. */
static inline bool
bzla_node_is_const_array(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_array(exp) && exp->kind == BZLA_LAMBDA_NODE
         && !bzla_node_real_addr(exp->e[1])->parameterized;
}

/** Return true if given node is a forall node. */
static inline bool
bzla_node_is_forall(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_FORALL_NODE;
}

/** Return true if given node is a exists node. */
static inline bool
bzla_node_is_exists(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_EXISTS_NODE;
}

/** Return true if given node is a quantifier (forall or exists) node. */
static inline bool
bzla_node_is_quantifier(const BzlaNode *exp)
{
  return bzla_node_is_forall(exp) || bzla_node_is_exists(exp);
}

/** Return true if given node is a lambda node. */
static inline bool
bzla_node_is_lambda(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_LAMBDA_NODE;
}

/** Return true if given node is a binder node (quantifier or lambda node). */
static inline bool
bzla_node_is_binder(const BzlaNode *exp)
{
  return bzla_node_is_quantifier(exp) || bzla_node_is_lambda(exp);
}

/** Return true if given node is an update (generalized write) node. */
static inline bool
bzla_node_is_update(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_UPDATE_NODE;
}

/** Return true if given node is a function node. */
static inline bool
bzla_node_is_fun(const BzlaNode *exp)
{
  return bzla_node_is_lambda(exp) || bzla_node_is_uf(exp)
         || bzla_node_is_fun_cond(exp) || bzla_node_is_update(exp);
}

/**
 * Return true if given node is an array variable (an uninterpreted function
 * that represents an array).
 */
static inline bool
bzla_node_is_uf_array(const BzlaNode *exp)
{
  return bzla_node_is_uf(exp)
         && ((BzlaUFNode *) bzla_node_real_addr(exp))->is_array;
}

/** Return true if given node is a parameter (i.e., a bound variable). */
static inline bool
bzla_node_is_param(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_PARAM_NODE;
}

/**
 * Return true if given node is an arguments (to a function application or
 * update) node.
 */
static inline bool
bzla_node_is_args(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_ARGS_NODE;
}

/** Return true if given node is a function application node. */
static inline bool
bzla_node_is_apply(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->kind == BZLA_APPLY_NODE;
}

/** Return true if given node is an equality over rounding modes. */
static inline bool
bzla_node_is_rm_eq(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return exp->kind == BZLA_RM_EQ_NODE;
}

/** Return true if given node is an equality over floating-points. */
static inline bool
bzla_node_is_fp_eq(const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);
  return exp->kind == BZLA_FP_EQ_NODE;
}

/** Return true if given node is an equality node. */
static inline bool
bzla_node_is_eq(const BzlaNode *exp)
{
  return bzla_node_is_fun_eq(exp) || bzla_node_is_bv_eq(exp)
         || bzla_node_is_fp_eq(exp) || bzla_node_is_rm_eq(exp);
}

/*------------------------------------------------------------------------*/

/** Return true if given node is a bit-vector constant representing zero. */
bool bzla_node_is_bv_const_zero(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a bit-vector constant representing one. */
bool bzla_node_is_bv_const_one(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a bit-vector constant representing all ones. */
bool bzla_node_is_bv_const_ones(Bzla *bzla, BzlaNode *exp);

/**
 * Return true if given node is a bit-vector constant representing the minimum
 * signed value.
 */
bool bzla_node_is_bv_const_min_signed(Bzla *bzla, BzlaNode *exp);

/**
 * Return true if given node is a bit-vector constant representing the maximum
 * signed value.
 */
bool bzla_node_is_bv_const_max_signed(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Return true if given node is a floating-point constant representing +0. */
bool bzla_node_is_fp_const_pos_zero(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a floating-point constant representing -0. */
bool bzla_node_is_fp_const_neg_zero(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a floating-point constant representing +oo. */
bool bzla_node_is_fp_const_pos_inf(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a floating-point constant representing -oo. */
bool bzla_node_is_fp_const_neg_inf(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a floating-point constant representing NaN. */
bool bzla_node_is_fp_const_nan(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Return true if given node is a rounding mode constant representing RNA. */
bool bzla_node_is_rm_const_rna(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a rounding mode constant representing RNE. */
bool bzla_node_is_rm_const_rne(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a rounding mode constant representing RTN. */
bool bzla_node_is_rm_const_rtn(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a rounding mode constant representing RTP. */
bool bzla_node_is_rm_const_rtp(Bzla *bzla, BzlaNode *exp);
/** Return true if given node is a rounding mode constant representing RTZ. */
bool bzla_node_is_rm_const_rtz(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Get the id of a given node (negative if inverted). */
static inline int32_t
bzla_node_get_id(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_is_inverted(exp) ? -bzla_node_real_addr(exp)->id : exp->id;
}

/** Get the tag of a node pointer. */
static inline int32_t
bzla_node_get_tag(const BzlaNode *exp)
{
  return (int32_t)((uintptr_t) 3 & (uintptr_t) exp);
}

/** Get the node kind. */
static inline BzlaNodeKind
bzla_node_get_kind(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->kind;
}

/*========================================================================*/

/** Copies expression (increments reference counter). */
BzlaNode *bzla_node_copy(Bzla *bzla, BzlaNode *exp);

/** Releases expression (decrements reference counter). */
void bzla_node_release(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/**
 * Get the id of the sort of the given node.
 * Do not release the returned sort.
 */
static inline BzlaSortId
bzla_node_get_sort_id(const BzlaNode *exp)
{
  assert(exp);
  return bzla_node_real_addr(exp)->sort_id;
}

/** Set the sort id of the given node.  */
static inline void
bzla_node_set_sort_id(BzlaNode *exp, BzlaSortId id)
{
  assert(exp);
  bzla_node_real_addr(exp)->sort_id = id;
}

/*------------------------------------------------------------------------*/

/** Increase the reference counter for external references of given node. */
void bzla_node_inc_ext_ref_counter(Bzla *bzla, BzlaNode *e);

/** Decrease the reference counter for external references of given node. */
void bzla_node_dec_ext_ref_counter(Bzla *bzla, BzlaNode *e);

/*------------------------------------------------------------------------*/

/**
 * Convert 'exp' to a proxy expression.
 * NOTE: 'exp' must be already simplified
 */
void bzla_node_set_to_proxy(Bzla *bzla, BzlaNode *exp);

/**
 * Return true if given node is simplified (i.e., the 'simplified' pointer
 * is set.
 */
static inline bool
bzla_node_is_simplified(const BzlaNode *exp)
{
  return bzla_node_real_addr(exp)->simplified != 0;
}

/*------------------------------------------------------------------------*/

/** Set parsed id (BTOR format only, needed for model output). */
void bzla_node_set_bzla_id(Bzla *bzla, BzlaNode *exp, int32_t id);

/** Get parsed id (BTOR format only, needed for model output). */
int32_t bzla_node_get_bzla_id(BzlaNode *exp);

/**
 * Get the exp (belonging to instance 'bzla') that matches given id.
 * Note: The main difference to 'bzla_node_match_by_id' is that this function
 *       does NOT increase the reference counter, and passing and 'id' < 0
 *       will return an inverted node
 */
BzlaNode *bzla_node_get_by_id(Bzla *bzla, int32_t id);

/**
 * Retrieve the exp (belonging to instance 'bzla') that matches given id.
 * Note: increases ref counter of returned match!
 * Note: 'id' must be greater 0
 *       -> will not return a conditionally inverted node
 */
BzlaNode *bzla_node_match_by_id(Bzla *bzla, int32_t id);

/*------------------------------------------------------------------------*/

/** Gets the symbol of an expression. */
char *bzla_node_get_symbol(Bzla *bzla, const BzlaNode *exp);

/** Sets the symbol of an expression. */
void bzla_node_set_symbol(Bzla *bzla, BzlaNode *exp, const char *symbol);

/*------------------------------------------------------------------------*/

/**
 * Retrieve the exp (belonging to instance 'bzla') that matches given
 * expression by id. This is intended to be used for handling expressions
 * of a cloned instance (in a clone and its parent, expressions
 * with the same id correspond to each other, i.e. initially, the cloned
 * expression is an identical copy of the parent expression).
 * (Note: increases ref counter of return match!)
 */
BzlaNode *bzla_node_match(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Compares two expression pairs by ID */
int32_t bzla_node_compare_by_id(const BzlaNode *exp0, const BzlaNode *exp1);
/** Compare function for expressions (by ID) to be used for qsort */
int32_t bzla_node_compare_by_id_qsort_desc(const void *p, const void *q);
int32_t bzla_node_compare_by_id_qsort_asc(const void *p, const void *q);

/** Hashes expression by ID */
uint32_t bzla_node_hash_by_id(const BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Get the bit width of a bit-vector expression. */
uint32_t bzla_node_bv_get_width(Bzla *bzla, const BzlaNode *exp);
/** Get the bit width of the exponent of a floating-point expression. */
uint32_t bzla_node_fp_get_exp_width(Bzla *bzla, const BzlaNode *exp);
/** Get the bit width of the significand of a floating-point expression. */
uint32_t bzla_node_fp_get_sig_width(Bzla *bzla, const BzlaNode *exp);

/*------------------------------------------------------------------------*/

/**
 * Get the bit-vector representation of a bit-vector constant node.
 *
 * Bit-vector constants are normalized to LSB = 0. As a consequence, bit-vector
 * constant nodes can be inverted. This function returns the *real* bit-vector
 * representation of a bit-vector constant node, i.e., if it is inverted, it
 * returns the correctly inverted bit-vector representation. For example,
 * bit-vector constant '001' is represented as an inverted node 'n' that
 * represents '110', i.e., bzla_node_is_inverted(n) = true and n->bits = '110'.
 * This function will return '001' for 'n'.
 *
 * Note: The returned BzlaBitVector does not have to be freed.
 */
BzlaBitVector *bzla_node_bv_const_get_bits(BzlaNode *exp);

/**
 * Get a pointer to 'bits' of a bit-vector constant node.
 * This function is meant to only be used for manipulating this pointer.
 */
BzlaBitVector *bzla_node_bv_const_get_bits_ptr(BzlaNode *exp);

/**
 * Get a pointer to 'invbits' of a bit-vector constant node.
 * This function is meant to only be used for manipulating this pointer.
 */
BzlaBitVector *bzla_node_bv_const_get_invbits_ptr(BzlaNode *exp);

/** Set the bit-vector representation of a bit-vector constant node. */
void bzla_node_bv_const_set_bits(BzlaNode *exp, BzlaBitVector *bits);
/** Set the inverted bit-vector representation of a bit-vector constant node. */
void bzla_node_bv_const_set_invbits(BzlaNode *exp, BzlaBitVector *bits);

/*------------------------------------------------------------------------*/

/** Get the rounding mode representation of a rounding mode constant node.  */
BzlaRoundingMode bzla_node_rm_const_get_rm(const BzlaNode *exp);

/*------------------------------------------------------------------------*/

void bzla_node_fp_const_set_fp(BzlaNode *exp, BzlaFloatingPoint *fp);
/**
 * Get the floating-point representation of a floating-point constant node.
 * Note: The returned BzlaFloatingPoint does not have to be freed.
 */
BzlaFloatingPoint *bzla_node_fp_const_get_fp(BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Get the number of arguments of lambda expression 'exp'. */
uint32_t bzla_node_fun_get_arity(Bzla *bzla, BzlaNode *exp);

/** Get the number of arguments of an argument expression 'exp'. */
uint32_t bzla_node_args_get_arity(Bzla *bzla, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Get the body of a binder (lambda or quantifier) expression. */
BzlaNode *bzla_node_binder_get_body(BzlaNode *binder);
/** Set the body of a binder expression. */
void bzla_node_binder_set_body(BzlaNode *binder, BzlaNode *body);

/*------------------------------------------------------------------------*/

/** Get the static rho table of a lambda node. */
BzlaPtrHashTable *bzla_node_lambda_get_static_rho(BzlaNode *lambda);

/** Set static rho table of a lambda node. */
void bzla_node_lambda_set_static_rho(BzlaNode *lambda,
                                     BzlaPtrHashTable *static_rho);

/** (Deep) copy static rho table of a lambda node. */
BzlaPtrHashTable *bzla_node_lambda_copy_static_rho(Bzla *bzla,
                                                   BzlaNode *lambda);

/** Delete static rho table of a lambda node. */
void bzla_node_lambda_delete_static_rho(Bzla *bzla, BzlaNode *lambda);

/*------------------------------------------------------------------------*/

/** Get the upper index of a bit-vector extract node. */
uint32_t bzla_node_bv_slice_get_upper(const BzlaNode *slice);
/** Get the lower index of a bit-vector extract node. */
uint32_t bzla_node_bv_slice_get_lower(const BzlaNode *slice);

/*------------------------------------------------------------------------*/

/** Get the binder of a bound variable. */
BzlaNode *bzla_node_param_get_binder(BzlaNode *param);

/** Set the binder of a bound variable. */
void bzla_node_param_set_binder(BzlaNode *param, BzlaNode *lambda);

/** Return true if given bound variable is already bound. */
bool bzla_node_param_is_bound(BzlaNode *param);

/** Return true if given bound variable is an existential variable. */
bool bzla_node_param_is_exists_var(BzlaNode *param);

/** Return true if given bound variable is an universal variable. */
bool bzla_node_param_is_forall_var(BzlaNode *param);

/** Get the expression that instantiates given parameter. */
BzlaNode *bzla_node_param_get_assigned_exp(BzlaNode *param);

/** Instantiate given parameter. */
BzlaNode *bzla_node_param_set_assigned_exp(BzlaNode *param, BzlaNode *exp);

/*------------------------------------------------------------------------*/

/** Create a bit-vector constant. */
BzlaNode *bzla_node_create_bv_const(Bzla *bzla, const BzlaBitVector *bits);

/** Create a roundingmode constant. */
BzlaNode *bzla_node_create_rm_const(Bzla *bzla, const BzlaRoundingMode rm);

/** Create a floating-point constant. */
BzlaNode *bzla_node_create_fp_const(Bzla *bzla, const BzlaFloatingPoint *fp);

/** Create variable node of given sort. */
BzlaNode *bzla_node_create_var(Bzla *bzla, BzlaSortId sort, const char *symbol);

/*------------------------------------------------------------------------*/

/** Create uninterpreted function node of given (function) sort. */
BzlaNode *bzla_node_create_uf(Bzla *bzla, BzlaSortId sort, const char *symbol);

/** Create a bound variable node (for a lambda or quantifier nodes). */
BzlaNode *bzla_node_create_param(Bzla *bzla,
                                 BzlaSortId sort,
                                 const char *symbol);

/** Create equality node. */
BzlaNode *bzla_node_create_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create if-then-else node. */
BzlaNode *bzla_node_create_cond(Bzla *bzla,
                                BzlaNode *e_cond,
                                BzlaNode *e_if,
                                BzlaNode *e_else);

/** Create arguments node (for apply or update nodes). */
BzlaNode *bzla_node_create_args(Bzla *bzla, BzlaNode *args[], uint32_t argc);

/** Create function application node. */
BzlaNode *bzla_node_create_apply(Bzla *bzla, BzlaNode *fun, BzlaNode *args);

/** Create lambda node. */
BzlaNode *bzla_node_create_lambda(Bzla *bzla, BzlaNode *param, BzlaNode *body);

/** Create forall node. */
BzlaNode *bzla_node_create_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body);

/** Create quantifier (exists, forall) node. */
BzlaNode *bzla_node_create_quantifier(Bzla *bzla,
                                      BzlaNodeKind kind,
                                      BzlaNode *param,
                                      BzlaNode *body);

/** Create exists node. */
BzlaNode *bzla_node_create_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body);

/** Create update node (generalization of array writes). */
BzlaNode *bzla_node_create_update(Bzla *bzla,
                                  BzlaNode *fun,
                                  BzlaNode *args,
                                  BzlaNode *value);

/*------------------------------------------------------------------------*/

/** Create bit-vector bvand node. */
BzlaNode *bzla_node_create_bv_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvadd node. */
BzlaNode *bzla_node_create_bv_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvmul node. */
BzlaNode *bzla_node_create_bv_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvult node. */
BzlaNode *bzla_node_create_bv_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvslt node. */
BzlaNode *bzla_node_create_bv_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvshl node. */
BzlaNode *bzla_node_create_bv_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvlshr node. */
BzlaNode *bzla_node_create_bv_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvudiv node. */
BzlaNode *bzla_node_create_bv_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector bvurem node. */
BzlaNode *bzla_node_create_bv_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector concat node. */
BzlaNode *bzla_node_create_bv_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create bit-vector extract node. */
BzlaNode *bzla_node_create_bv_slice(Bzla *bzla,
                                    BzlaNode *exp,
                                    uint32_t upper,
                                    uint32_t lower);

/*------------------------------------------------------------------------*/

/** Create fp.abs node. */
BzlaNode *bzla_node_create_fp_abs(Bzla *bzla, BzlaNode *e0);
/** Create fp.neg node. */
BzlaNode *bzla_node_create_fp_neg(Bzla *bzla, BzlaNode *e0);

/** Create fp.isNormal node. */
BzlaNode *bzla_node_create_fp_is_normal(Bzla *bzla, BzlaNode *e0);
/** Create fp.isSubnormal node. */
BzlaNode *bzla_node_create_fp_is_subnormal(Bzla *bzla, BzlaNode *e0);
/** Create fp.isZero node. */
BzlaNode *bzla_node_create_fp_is_zero(Bzla *bzla, BzlaNode *e0);
/** Create fp.isInfinite node. */
BzlaNode *bzla_node_create_fp_is_inf(Bzla *bzla, BzlaNode *e0);
/** Create fp.isInfinite node. */
BzlaNode *bzla_node_create_fp_is_nan(Bzla *bzla, BzlaNode *e0);
/** Create fp.isNegative node. */
BzlaNode *bzla_node_create_fp_is_neg(Bzla *bzla, BzlaNode *e0);
/** Create fp.isPositive node. */
BzlaNode *bzla_node_create_fp_is_pos(Bzla *bzla, BzlaNode *e0);

/** Create fp.leq node. */
BzlaNode *bzla_node_create_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);
/** Create fp.lt node. */
BzlaNode *bzla_node_create_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create fp.min node. */
BzlaNode *bzla_node_create_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);
/** Create fp.max node. */
BzlaNode *bzla_node_create_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create fp.rem node. */
BzlaNode *bzla_node_create_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create fp.sqrt node. */
BzlaNode *bzla_node_create_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create fp.rti node. */
BzlaNode *bzla_node_create_fp_rti(Bzla *bzla, BzlaNode *e0, BzlaNode *e1);

/** Create fp.add node. */
BzlaNode *bzla_node_create_fp_add(Bzla *bzla,
                                  BzlaNode *e0,
                                  BzlaNode *e1,
                                  BzlaNode *e2);

/** Create fp.mul node. */
BzlaNode *bzla_node_create_fp_mul(Bzla *bzla,
                                  BzlaNode *e0,
                                  BzlaNode *e1,
                                  BzlaNode *e2);

/** Create fp.div node. */
BzlaNode *bzla_node_create_fp_div(Bzla *bzla,
                                  BzlaNode *e0,
                                  BzlaNode *e1,
                                  BzlaNode *e2);

/** Create fp.fma node. */
BzlaNode *bzla_node_create_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3);

/** Create fp.to_sbv node. */
BzlaNode *bzla_node_create_fp_to_sbv(Bzla *bzla,
                                     BzlaNode *e0,
                                     BzlaNode *e1,
                                     BzlaSortId sort);

/** Create fp.to_ubv node. */
BzlaNode *bzla_node_create_fp_to_ubv(Bzla *bzla,
                                     BzlaNode *e0,
                                     BzlaNode *e1,
                                     BzlaSortId sort);

/** Create to_fp from IEEE bit-vector node. */
BzlaNode *bzla_node_create_fp_to_fp_from_bv(Bzla *bzla,
                                            BzlaNode *exp,
                                            BzlaSortId sort);

/** Create to_fp from floating-point node. */
BzlaNode *bzla_node_create_fp_to_fp_from_fp(Bzla *bzla,
                                            BzlaNode *e0,
                                            BzlaNode *e1,
                                            BzlaSortId sort);

/** Create to_fp from machine integer (signed bit-vector) node. */
BzlaNode *bzla_node_create_fp_to_fp_from_sbv(Bzla *bzla,
                                             BzlaNode *e0,
                                             BzlaNode *e1,
                                             BzlaSortId sort);

/** Create to_fp from unsigned machine integer (unsigned bit-vector) node. */
BzlaNode *bzla_node_create_fp_to_fp_from_ubv(Bzla *bzla,
                                             BzlaNode *e0,
                                             BzlaNode *e1,
                                             BzlaSortId sort);

/*------------------------------------------------------------------------*/

/** Create a new value of with sort 'sort' from bit-vector 'bv'. */
BzlaNode *bzla_node_mk_value(Bzla *bzla,
                             BzlaSortId sort,
                             const BzlaBitVector *bv);

/*========================================================================*/

struct BzlaNodePair
{
  BzlaNode *node1;
  BzlaNode *node2;
};

typedef struct BzlaNodePair BzlaNodePair;

/** Create new node pair. */
BzlaNodePair *bzla_node_pair_new(Bzla *, BzlaNode *, BzlaNode *);

/** Delete given node pair. */
void bzla_node_pair_delete(Bzla *, BzlaNodePair *);

/** Compute hash value for given node pair. */
uint32_t bzla_node_pair_hash(const BzlaNodePair *);

/**
 * Compare two node pairs.
 * Returns
 * - 0 : if both node pairs contain nodes with the same ids, i.e.,
 *       p0->node0->id == p1->node0->id and p0->node1->id == p1->node1->id
 * - -1: if p0->node0 == p1->node0 and p0->node1->id < p1->node1->id,
 *       or p0->node1 == p1->node1 and p0->node0->id < p1->node0->id,
 * - 1 : if p0->node0 == p1->node0 and p0->node1->id > p1->node1->id,
 *       or p0->node1 == p1->node1 and p0->node0->id > p1->node0->id,
 */
int32_t bzla_node_pair_compare(const BzlaNodePair *p0, const BzlaNodePair *);

#endif
