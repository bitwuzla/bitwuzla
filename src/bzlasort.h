/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASORT_H_INCLUDED
#define BZLASORT_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "bzlatypes.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"

typedef uint32_t BzlaSortId;
// typedef struct bzlasortanon bzlasortanon; // debug
// typedef bzlasortanon* BzlaSortId;

enum BzlaSortKind
{
  BZLA_INVALID_SORT = 0,
  BZLA_BOOL_SORT    = 1,
  BZLA_BV_SORT      = 2,
  BZLA_ARRAY_SORT   = 3,
  BZLA_LST_SORT     = 4,
  BZLA_FUN_SORT     = 5,
  BZLA_FP_SORT      = 6,
  BZLA_RM_SORT      = 7,
  BZLA_TUPLE_SORT   = 8
};

typedef enum BzlaSortKind BzlaSortKind;

typedef struct BzlaSort BzlaSort;
typedef struct BzlaBitVecSort BzlaBitVecSort;
typedef struct BzlaArraySort BzlaArraySort;
typedef struct BzlaLstSort BzlaLstSort;
typedef struct BzlaFunSort BzlaFunSort;
typedef struct BzlaFloatingPointSort BzlaFloatingPointSort;
typedef struct BzlaTupleSort BzlaTupleSort;

struct BzlaBitVecSort
{
  uint32_t width;
};

struct BzlaArraySort
{
  BzlaSort *index;
  BzlaSort *element;
};

struct BzlaLstSort
{
  BzlaSort *head;
  BzlaSort *tail;
};

struct BzlaFunSort
{
  bool is_array;
  uint32_t arity;
  BzlaSort *domain;
  BzlaSort *codomain;
};

struct BzlaFloatingPointSort
{
  uint32_t width_exp;
  uint32_t width_sig;
};

struct BzlaTupleSort
{
  uint32_t num_elements;
  BzlaSort **elements;
};

typedef struct BzlaSortUniqueTable BzlaSortUniqueTable;

struct BzlaSort
{
  BzlaSortKind kind;
  BzlaSortId id;
  uint32_t refs;     /* reference counter */
  uint32_t ext_refs; /* reference counter for API references */
  BzlaSort *next;    /* collision chain for unique table */
  BzlaSortUniqueTable *table;
#ifndef NDEBUG
  Bzla *bzla;
  uint32_t parents;
#endif
  union
  {
    BzlaBitVecSort bitvec;
    BzlaArraySort array;
    BzlaLstSort lst;
    BzlaFunSort fun;
    BzlaFloatingPointSort fp;
    BzlaTupleSort tuple;
  };
};

BZLA_DECLARE_STACK(BzlaSortPtr, BzlaSort *);
BZLA_DECLARE_STACK(BzlaSortId, BzlaSortId);

struct BzlaSortUniqueTable
{
  uint32_t size;
  uint32_t num_elements;
  BzlaSort **chains;
  BzlaMemMgr *mm;
  BzlaSortPtrStack id2sort;
};

BzlaSortId bzla_sort_bool(Bzla *bzla);

BzlaSortId bzla_sort_bv(Bzla *bzla, uint32_t width);

BzlaSortId bzla_sort_array(Bzla *bzla,
                           BzlaSortId index_id,
                           BzlaSortId element_id);

BzlaSortId bzla_sort_fun(Bzla *bzla,
                         BzlaSortId domain_id,
                         BzlaSortId codomain_id);

/* Create floating-point sort with exponent bit-wdith 'width_exp' and
 * significand bit-width 'width_sig'. */
BzlaSortId bzla_sort_fp(Bzla *bzla, uint32_t width_exp, uint32_t width_sig);

/* Create RoundingMode sort. */
BzlaSortId bzla_sort_rm(Bzla *bzla);

BzlaSortId bzla_sort_tuple(Bzla *bzla,
                           BzlaSortId *element_ids,
                           size_t num_elements);

BzlaSortId bzla_sort_copy(Bzla *bzla, BzlaSortId id);

void bzla_sort_release(Bzla *bzla, BzlaSortId id);

BzlaSort *bzla_sort_get_by_id(Bzla *bzla, BzlaSortId id);

uint32_t bzla_sort_bv_get_width(Bzla *bzla, BzlaSortId id);

/* Return exponent width of given floating-point sort. */
uint32_t bzla_sort_fp_get_exp_width(Bzla *bzla, BzlaSortId id);
/* Return significant width of given floating-point sort. */
uint32_t bzla_sort_fp_get_sig_width(Bzla *bzla, BzlaSortId id);
/* Return width of bit-vector representation of given floating-point sort. */
uint32_t bzla_sort_fp_get_bv_width(Bzla *bzla, BzlaSortId id);

uint32_t bzla_sort_fun_get_arity(Bzla *bzla, BzlaSortId id);
uint32_t bzla_sort_tuple_get_arity(Bzla *bzla, BzlaSortId id);

BzlaSortId bzla_sort_fun_get_codomain(Bzla *bzla, BzlaSortId id);
BzlaSortId bzla_sort_fun_get_domain(Bzla *bzla, BzlaSortId id);

BzlaSortId bzla_sort_array_get_index(Bzla *bzla, BzlaSortId id);
BzlaSortId bzla_sort_array_get_element(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_valid(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_bool(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_bv(Bzla *bzla, BzlaSortId id);

/* Return true if given sort is a floating-point sort. */
bool bzla_sort_is_fp(Bzla *bzla, BzlaSortId id);

/* Return true if given sort is a RoundingMode sort. */
bool bzla_sort_is_rm(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_array(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_tuple(Bzla *bzla, BzlaSortId id);

bool bzla_sort_is_fun(Bzla *bzla, BzlaSortId id);

struct BzlaTupleSortIterator
{
  size_t pos;
  BzlaSort *tuple;
};

typedef struct BzlaTupleSortIterator BzlaTupleSortIterator;

void bzla_iter_tuple_sort_init(BzlaTupleSortIterator *it,
                               Bzla *bzla,
                               BzlaSortId id);

bool bzla_iter_tuple_sort_has_next(const BzlaTupleSortIterator *it);
BzlaSortId bzla_iter_tuple_sort_next(BzlaTupleSortIterator *it);

#endif
