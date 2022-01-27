/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzladumpbtor.h"

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
#include "bzlaopt.h"
#include "bzlasort.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlastack.h"

typedef struct BzlaDumpContextState BzlaDumpContextState;

struct BzlaDumpContextState
{
  BzlaNode *state;
  BzlaNode *init;
  BzlaNode *next;
};

struct BzlaDumpContext
{
  uint32_t maxid;
  uint32_t maxsortid;
  uint32_t version;
  Bzla *bzla;
  BzlaPtrHashTable *idtab;
  BzlaPtrHashTable *inputs;
  BzlaPtrHashTable *states;
  BzlaPtrHashTable *sorts;
  BzlaNodePtrStack outputs;
  BzlaNodePtrStack bads;
  BzlaNodePtrStack constraints;
  BzlaNodePtrStack roots;
  BzlaNodePtrStack work;
  BzlaPtrHashTable *no_dump;
};

BzlaDumpContext *
bzla_dumpbtor_new_dump_context(Bzla *bzla)
{
  BzlaDumpContext *res;
  BZLA_CNEW(bzla->mm, res);
  res->bzla    = bzla;
  res->version = 1;
  res->inputs  = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  res->states  = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  res->idtab   = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  res->sorts   = bzla_hashptr_table_new(bzla->mm, 0, 0);
  res->no_dump = bzla_hashptr_table_new(bzla->mm, 0, 0);

  /* set start id for roots */
  if (!bzla_opt_get(bzla, BZLA_OPT_PRETTY_PRINT))
    res->maxid = BZLA_COUNT_STACK(bzla->nodes_id_table);

  BZLA_INIT_STACK(bzla->mm, res->outputs);
  BZLA_INIT_STACK(bzla->mm, res->bads);
  BZLA_INIT_STACK(bzla->mm, res->constraints);
  BZLA_INIT_STACK(bzla->mm, res->roots);
  BZLA_INIT_STACK(bzla->mm, res->work);

  return res;
}

void
bzla_dumpbtor_delete_dump_context(BzlaDumpContext *bdc)
{
  BzlaPtrHashTableIterator it;

  BZLA_RELEASE_STACK(bdc->work);

  while (!BZLA_EMPTY_STACK(bdc->roots))
    bzla_node_release(bdc->bzla, BZLA_POP_STACK(bdc->roots));
  BZLA_RELEASE_STACK(bdc->roots);

  while (!BZLA_EMPTY_STACK(bdc->outputs))
    bzla_node_release(bdc->bzla, BZLA_POP_STACK(bdc->outputs));
  BZLA_RELEASE_STACK(bdc->outputs);

  while (!BZLA_EMPTY_STACK(bdc->bads))
    bzla_node_release(bdc->bzla, BZLA_POP_STACK(bdc->bads));
  BZLA_RELEASE_STACK(bdc->bads);

  while (!BZLA_EMPTY_STACK(bdc->constraints))
    bzla_node_release(bdc->bzla, BZLA_POP_STACK(bdc->constraints));
  BZLA_RELEASE_STACK(bdc->constraints);

  bzla_iter_hashptr_init(&it, bdc->inputs);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bdc->bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(bdc->inputs);

  bzla_iter_hashptr_init(&it, bdc->states);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaDumpContextState *l = it.bucket->data.as_ptr;
    bzla_node_release(bdc->bzla, l->state);
    if (l->next) bzla_node_release(bdc->bzla, l->next);
    if (l->init) bzla_node_release(bdc->bzla, l->init);
    BZLA_DELETE(bdc->bzla->mm, l);
    (void) bzla_iter_hashptr_next(&it);
  }
  bzla_hashptr_table_delete(bdc->states);

  bzla_iter_hashptr_init(&it, bdc->idtab);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bdc->bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(bdc->idtab);

  bzla_hashptr_table_delete(bdc->sorts);
  bzla_hashptr_table_delete(bdc->no_dump);
  BZLA_DELETE(bdc->bzla->mm, bdc);
}

void
bzla_dumpbtor_add_input_to_dump_context(BzlaDumpContext *bdc, BzlaNode *input)
{
  assert(bzla_node_is_regular(input));
  assert(bzla_node_is_bv_var(input));
  assert(!bzla_hashptr_table_get(bdc->inputs, input));
  assert(!bzla_hashptr_table_get(bdc->states, input));
  (void) bzla_node_copy(bdc->bzla, input);
  (void) bzla_hashptr_table_add(bdc->inputs, input);
}

void
bzla_dumpbtor_add_state_to_dump_context(BzlaDumpContext *bdc, BzlaNode *state)
{
  BzlaPtrHashBucket *b;
  BzlaDumpContextState *bdcl;
  assert(bzla_node_is_regular(state));
  assert(bzla_node_is_bv_var(state));
  assert(!bzla_hashptr_table_get(bdc->inputs, state));
  assert(!bzla_hashptr_table_get(bdc->states, state));
  b = bzla_hashptr_table_add(bdc->states, state);
  BZLA_CNEW(bdc->bzla->mm, bdcl);
  bdcl->state    = bzla_node_copy(bdc->bzla, state);
  b->data.as_ptr = bdcl;
}

void
bzla_dumpbtor_add_next_to_dump_context(BzlaDumpContext *bdc,
                                       BzlaNode *state,
                                       BzlaNode *next)
{
  BzlaDumpContextState *l;
  BzlaPtrHashBucket *b;
  b = bzla_hashptr_table_get(bdc->states, state);
  assert(b);
  l = b->data.as_ptr;
  assert(l);
  assert(l->state == state);
  assert(!l->next);
  l->next = bzla_node_copy(bdc->bzla, next);
}

void
bzla_dumpbtor_add_init_to_dump_context(BzlaDumpContext *bdc,
                                       BzlaNode *state,
                                       BzlaNode *init)
{
  BzlaDumpContextState *l;
  BzlaPtrHashBucket *b;
  b = bzla_hashptr_table_get(bdc->states, state);
  assert(b);
  l = b->data.as_ptr;
  assert(l);
  assert(l->state == state);
  assert(!l->init);
  l->init = bzla_node_copy(bdc->bzla, init);
}

void
bzla_dumpbtor_add_bad_to_dump_context(BzlaDumpContext *bdc, BzlaNode *bad)
{
  (void) bzla_node_copy(bdc->bzla, bad);
  BZLA_PUSH_STACK(bdc->bads, bad);
}

void
bzla_dumpbtor_add_output_to_dump_context(BzlaDumpContext *bdc, BzlaNode *output)
{
  (void) bzla_node_copy(bdc->bzla, output);
  BZLA_PUSH_STACK(bdc->outputs, output);
}

void
bzla_dumpbtor_add_root_to_dump_context(BzlaDumpContext *bdc, BzlaNode *root)
{
  assert(!bzla_node_is_args(root));
  (void) bzla_node_copy(bdc->bzla, root);
  BZLA_PUSH_STACK(bdc->roots, root);
}

void
bzla_dumpbtor_add_constraint_to_dump_context(BzlaDumpContext *bdc,
                                             BzlaNode *constraint)
{
  (void) bzla_node_copy(bdc->bzla, constraint);
  BZLA_PUSH_STACK(bdc->constraints, constraint);
}

static int32_t
bdcid(BzlaDumpContext *bdc, BzlaNode *node)
{
  BzlaPtrHashBucket *b;
  BzlaNode *real;
  int32_t res;
  real = bzla_node_real_addr(node);
  b    = bzla_hashptr_table_get(bdc->idtab, real);
  if (!b)
  {
    b = bzla_hashptr_table_add(bdc->idtab, bzla_node_copy(bdc->bzla, node));
    if (bzla_opt_get(bdc->bzla, BZLA_OPT_PRETTY_PRINT))
      b->data.as_int = ++bdc->maxid;
    else
      b->data.as_int = real->id;
  }
  res = b->data.as_int;
  if (!bzla_node_is_regular(node)) res = -res;
  return res;
}

static uint32_t
bdcsortid(BzlaDumpContext *bdc, BzlaSort *sort)
{
  assert(bzla_hashptr_table_get(bdc->sorts, sort));
  return bzla_hashptr_table_get(bdc->sorts, sort)->data.as_int;
}

static int32_t
compare_sorts(const void *p1, const void *p2)
{
  BzlaSort *a, *b;
  a = *((BzlaSort **) p1);
  b = *((BzlaSort **) p2);
  return a->id - b->id;
}

static BzlaSort *
get_sort(BzlaDumpContext *bdc, BzlaNode *node)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bdc->bzla, bzla_node_get_sort_id(node));
  assert(bzla_hashptr_table_get(bdc->sorts, sort));
  assert(sort->refs > 1);
  return sort;
}

#ifndef NDEBUG
static bool
has_lambda_parent(BzlaNode *exp)
{
  BzlaNode *p;
  BzlaNodeIterator it;
  bzla_iter_parent_init(&it, exp);
  while (bzla_iter_parent_has_next(&it))
  {
    p = bzla_iter_parent_next(&it);
    if (bzla_node_is_lambda(p)) return true;
  }
  return false;
}
#endif

static void
mark_no_dump(BzlaDumpContext *bdc, BzlaNode *node)
{
  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;

  mm = bdc->bzla->mm;
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, node);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (!cur->parameterized || bzla_hashptr_table_get(bdc->no_dump, cur))
      continue;

    bzla_hashptr_table_add(bdc->no_dump, cur);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  BZLA_RELEASE_STACK(visit);
}

static void
bdcnode(BzlaDumpContext *bdc, BzlaNode *node, FILE *file)
{
  uint32_t i;
  char *symbol, *cbits;
  const char *op;
  uint32_t opt;
  BzlaNode *n, *index, *value;
  BzlaArgsIterator ait;
  BzlaNodeIterator nit;
  BzlaPtrHashTable *rho;
  BzlaBitVector *bits;

  node  = bzla_node_real_addr(node);
  cbits = 0;

  /* argument nodes will not be dumped as they are purely internal nodes */
  if (bzla_node_is_args(node)) return;

#if 0
  if (bdc->version == 2
      && (bzla_node_is_args (node)
	  || (!BZLA_IS_FIRST_CURRIED_LAMBDA (node)
	      && BZLA_IS_CURRIED_LAMBDA_NODE (node))))
    return;
#endif

  /* do not dump parameterized nodes that belong to a "write-lambda" */
  if (bzla_hashptr_table_get(bdc->no_dump, node)) return;

  switch (node->kind)
  {
    case BZLA_BV_ADD_NODE: op = "add"; break;
    case BZLA_BV_AND_NODE: op = "and"; break;
    case BZLA_BV_CONCAT_NODE: op = "concat"; break;
    case BZLA_COND_NODE: op = bdc->version == 1 ? "cond" : "ite"; break;
    case BZLA_BV_EQ_NODE:
    case BZLA_FUN_EQ_NODE: op = "eq"; break;
    case BZLA_BV_MUL_NODE: op = "mul"; break;
    case BZLA_PROXY_NODE: op = "proxy"; break;
    case BZLA_BV_SLL_NODE: op = "sll"; break;
    case BZLA_BV_SRL_NODE: op = "srl"; break;
    case BZLA_BV_UDIV_NODE: op = "udiv"; break;
    case BZLA_BV_ULT_NODE: op = "ult"; break;
    case BZLA_BV_SLT_NODE: op = "slt"; break;
    case BZLA_BV_UREM_NODE: op = "urem"; break;
    case BZLA_BV_SLICE_NODE: op = "slice"; break;
    case BZLA_UF_NODE: op = bzla_node_is_uf_array(node) ? "array" : "uf"; break;
    case BZLA_BV_CONST_NODE:
      bits = bzla_node_bv_const_get_bits(node);
      opt  = bzla_opt_get(bdc->bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);
      if (bzla_bv_is_zero(bits))
      {
        op = "zero";
      }
      else if (bzla_bv_is_one(bits))
      {
        op = "one";
      }
      else if (bzla_bv_is_ones(bits))
      {
        op = "ones";
      }
      else if (opt == BZLA_OUTPUT_BASE_HEX)
      {
        op    = "consth";
        cbits = bzla_bv_to_hex_char(bdc->bzla->mm, bits);
      }
      else if (opt == BZLA_OUTPUT_BASE_DEC
               || bzla_bv_small_positive_int(bits) > 0)
      {
        op    = "constd";
        cbits = bzla_bv_to_dec_char(bdc->bzla->mm, bits);
      }
      else
      {
        op    = "const";
        cbits = bzla_bv_to_char(bdc->bzla->mm, bits);
      }
      break;
    case BZLA_PARAM_NODE: op = "param"; break;
    case BZLA_FORALL_NODE: op = "forall"; break;
    case BZLA_EXISTS_NODE: op = "exists"; break;
    case BZLA_LAMBDA_NODE:
      if (bzla_opt_get(bdc->bzla, BZLA_OPT_RW_LEVEL) == 0
          && bzla_node_lambda_get_static_rho(node))
      {
        op = "write";
        mark_no_dump(bdc, node->e[1]);
      }
      else if (bdc->version == 1
               || bzla_node_fun_get_arity(bdc->bzla, node) == 1)
        op = "lambda";
      else
        op = "fun";
      break;
    case BZLA_APPLY_NODE:
      if (bzla_node_is_uf_array(node->e[0])
          || (bzla_opt_get(bdc->bzla, BZLA_OPT_RW_LEVEL) == 0
              && bzla_node_is_lambda(node->e[0])
              && bzla_node_lambda_get_static_rho(node->e[0])))
        op = "read";
      else
        op = "apply";
      break;
    case BZLA_ARGS_NODE: op = "args"; break;
    case BZLA_UPDATE_NODE: op = "write"; break;
    default: assert(node->kind == BZLA_VAR_NODE); op = "var";
  }

  /* print id, operator and sort */
  if (bdc->version == 1)
  {
    fprintf(file, "%d %s", bdcid(bdc, node), op);

    /* print index bit width of arrays */
    if (bzla_node_is_uf_array(node) || bzla_node_is_fun_cond(node)
        || bzla_node_is_update(node))
    {
      fprintf(
          file,
          " %d",
          bzla_sort_bv_get_width(bdc->bzla,
                                 bzla_sort_fun_get_codomain(
                                     bdc->bzla, bzla_node_get_sort_id(node))));
      fprintf(
          file,
          " %d",
          bzla_sort_bv_get_width(bdc->bzla,
                                 bzla_sort_array_get_index(
                                     bdc->bzla, bzla_node_get_sort_id(node))));
    }
    else if (bzla_node_is_lambda(node))
    {
      fprintf(
          file,
          " %d",
          bzla_sort_bv_get_width(bdc->bzla,
                                 bzla_sort_fun_get_codomain(
                                     bdc->bzla, bzla_node_get_sort_id(node))));
      fprintf(file, " %d", bzla_node_bv_get_width(bdc->bzla, node->e[0]));
    }
    else if (!bzla_node_is_uf(node))
      fprintf(file, " %d", bzla_node_bv_get_width(bdc->bzla, node));

    if (bzla_node_is_apply(node))
    {
      fprintf(file, " %d", bdcid(bdc, node->e[0]));
      bzla_iter_args_init(&ait, node->e[1]);
      while (bzla_iter_args_has_next(&ait))
        fprintf(file, " %d", bdcid(bdc, bzla_iter_args_next(&ait)));
      goto DONE;
    }
  }
  else
  {
    fprintf(file,
            "%d %s %d",
            bdcid(bdc, node),
            op,
            bdcsortid(bdc, get_sort(bdc, node)));

    if (bzla_node_is_apply(node))
    {
      fprintf(file, " %d", bdcid(bdc, node->e[0]));
      bzla_iter_args_init(&ait, node->e[1]);
      while (bzla_iter_args_has_next(&ait))
        fprintf(file, " %d", bdcid(bdc, bzla_iter_args_next(&ait)));
      goto DONE;
    }
    else if (strcmp(op, "fun") == 0)
    {
      assert(!has_lambda_parent(node));
      bzla_iter_lambda_init(&nit, node);
      while (bzla_iter_lambda_has_next(&nit))
      {
        n = bzla_iter_lambda_next(&nit);
        fprintf(file, " %d", bdcid(bdc, n->e[0]));
      }
      fprintf(file, " %d", bdcid(bdc, bzla_node_binder_get_body(node)));
      goto DONE;
    }
  }

  /* print children or const values */
  if (cbits)
  {
    fprintf(file, " %s", cbits);
    bzla_mem_freestr(bdc->bzla->mm, cbits);
  }
  else if (bzla_node_is_proxy(node))
    fprintf(file, " %d", bdcid(bdc, node->simplified));
  /* print write instead of lambda */
  else if (bzla_opt_get(bdc->bzla, BZLA_OPT_RW_LEVEL) == 0
           && bzla_node_is_lambda(node)
           && bzla_node_lambda_get_static_rho(node))
  {
    assert(bzla_node_fun_get_arity(bdc->bzla, node) == 1);
    rho = bzla_node_lambda_get_static_rho(node);
    assert(rho->count == 1);
    index = rho->first->key;
    value = rho->first->data.as_ptr;
    assert(value);
    assert(bzla_node_is_regular(index));
    assert(bzla_node_is_args(index));
    assert(bzla_node_is_regular(node->e[1]));
    assert(bzla_node_is_bv_cond(node->e[1]));
    assert(bzla_node_is_regular(node->e[1]->e[2]));
    assert(bzla_node_is_apply(node->e[1]->e[2]));
    fprintf(file,
            " %d %d %d",
            bdcid(bdc, node->e[1]->e[2]->e[0]),
            bdcid(bdc, index->e[0]),
            bdcid(bdc, value));
  }
  else if (bzla_node_is_update(node))
  {
    fprintf(file, " %d", bdcid(bdc, node->e[0]));
    fprintf(file, " %d", bdcid(bdc, node->e[1]->e[0]));
    fprintf(file, " %d", bdcid(bdc, node->e[2]));
  }
  else
    for (i = 0; i < node->arity; i++)
      fprintf(file, " %d", bdcid(bdc, node->e[i]));

  /* print slice limits/var symbols */
  if (node->kind == BZLA_BV_SLICE_NODE)
    fprintf(file,
            " %d %d",
            bzla_node_bv_slice_get_upper(node),
            bzla_node_bv_slice_get_lower(node));
  else if (bzla_node_is_bv_var(node) || bzla_node_is_uf(node)
           || bzla_node_is_param(node))
  {
    symbol = bzla_node_get_symbol(bdc->bzla, node);
    if (symbol) fprintf(file, " %s", symbol);
  }
DONE:
  fputc('\n', file);
}

static void
bdcsort(BzlaDumpContext *bdc, BzlaSort *sort, FILE *file)
{
  uint32_t i, id;
  const char *kind;

  /* already dumped */
  if (bzla_hashptr_table_get(bdc->sorts, sort)) return;

  switch (sort->kind)
  {
    default:
    case BZLA_BOOL_SORT: kind = "bool"; break;
    case BZLA_BV_SORT: kind = "bv"; break;
    case BZLA_ARRAY_SORT: kind = "array"; break;
    case BZLA_FUN_SORT: kind = "fun"; break;
  }

  id = sort->id;
  if (bzla_opt_get(bdc->bzla, BZLA_OPT_PRETTY_PRINT)) id = ++bdc->maxsortid;

  fprintf(file, "%d sort %s", id, kind);

  if (sort->kind == BZLA_BV_SORT)
    fprintf(file, " %d", sort->bitvec.width);
  else if (sort->kind == BZLA_ARRAY_SORT)
    fprintf(file,
            " %d %d",
            bdcsortid(bdc, sort->array.index),
            bdcsortid(bdc, sort->array.element));
  else if (sort->kind == BZLA_FUN_SORT)
  {
    if (sort->fun.arity == 1)
      fprintf(file, " %d", bdcsortid(bdc, sort->fun.domain));
    else
    {
      for (i = 0; i < sort->fun.arity; i++)
        fprintf(
            file, " %d", bdcsortid(bdc, sort->fun.domain->tuple.elements[i]));
    }
    fprintf(file, " %d", bdcsortid(bdc, sort->fun.codomain));
  }
  fputc('\n', file);

  bzla_hashptr_table_add(bdc->sorts, sort)->data.as_int = id;
}

static void
bdcsorts(BzlaDumpContext *bdc, BzlaNode *start, FILE *file)
{
  uint32_t i;
  BzlaMemMgr *mm;
  BzlaNodePtrStack work;
  BzlaSortPtrStack sorts;
  BzlaNode *cur;
  BzlaSort *sort;
  BzlaPtrHashTable *mark_nodes, *mark_sorts;

  mm         = bdc->bzla->mm;
  mark_nodes = bzla_hashptr_table_new(mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  mark_sorts = bzla_hashptr_table_new(mm, 0, 0);

  BZLA_INIT_STACK(mm, sorts);
  BZLA_INIT_STACK(mm, work);
  BZLA_PUSH_STACK(work, start);

  while (!BZLA_EMPTY_STACK(work))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(work));

    if (bzla_hashptr_table_get(mark_nodes, cur)) continue;

    (void) bzla_hashptr_table_add(mark_nodes, cur);

    sort = bzla_sort_get_by_id(bdc->bzla, bzla_node_get_sort_id(cur));

    if (!(bzla_hashptr_table_get(bdc->sorts, sort)
          || bzla_hashptr_table_get(mark_sorts, sort)))
    {
      (void) bzla_hashptr_table_add(mark_sorts, sort);
      BZLA_PUSH_STACK(sorts, sort);
    }

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(work, cur->e[i]);
  }

  qsort(
      sorts.start, BZLA_COUNT_STACK(sorts), sizeof(BzlaSort *), compare_sorts);

  for (i = 0; i < BZLA_COUNT_STACK(sorts); i++)
  {
    sort = BZLA_PEEK_STACK(sorts, i);
    bdcsort(bdc, sort, file);
  }

  bzla_hashptr_table_delete(mark_nodes);
  bzla_hashptr_table_delete(mark_sorts);
  BZLA_RELEASE_STACK(sorts);
  BZLA_RELEASE_STACK(work);
}

static void
bdcrec(BzlaDumpContext *bdc, BzlaNode *start, FILE *file)
{
  assert(bdc);
  assert(start);
  assert(file);

  BzlaNode *node;
  uint32_t i;

  if (bdc->version == 2) bdcsorts(bdc, start, file);

  assert(BZLA_EMPTY_STACK(bdc->work));

  BZLA_PUSH_STACK(bdc->work, start);
  while (!BZLA_EMPTY_STACK(bdc->work))
  {
    node = BZLA_POP_STACK(bdc->work);
    if (node)
    {
      node = bzla_node_real_addr(node);
      if (bzla_hashptr_table_get(bdc->idtab, node)) continue;
      BZLA_PUSH_STACK(bdc->work, node);
      BZLA_PUSH_STACK(bdc->work, 0);

      for (i = 1; i <= node->arity; i++)
        BZLA_PUSH_STACK(bdc->work, node->e[node->arity - i]);

      if (node->simplified) BZLA_PUSH_STACK(bdc->work, node->simplified);
    }
    else
    {
      assert(!BZLA_EMPTY_STACK(bdc->work));
      node = BZLA_POP_STACK(bdc->work);
      assert(bzla_node_is_regular(node));
      if (!bzla_node_is_args(node))
      {
        (void) bdcid(bdc, node);
        bdcnode(bdc, node, file);
      }
    }
  }
}

void
bzla_dumpbtor_dump_bdc(BzlaDumpContext *bdc, FILE *file)
{
  BzlaPtrHashTableIterator it;
  uint32_t i;
  char *symbol;
  int32_t id;
  uint32_t len;

  bzla_iter_hashptr_init(&it, bdc->inputs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaNode *node = bzla_iter_hashptr_next(&it);
    assert(node);
    assert(bzla_node_is_regular(node));
    assert(bzla_node_is_bv_var(node));
    id = bdcid(bdc, node);
    fprintf(file, "%d input %u", id, bzla_node_bv_get_width(bdc->bzla, node));
    if ((symbol = bzla_node_get_symbol(bdc->bzla, node)))
      fprintf(file, " %s", symbol);
    fputc('\n', file);
  }

  bzla_iter_hashptr_init(&it, bdc->states);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaNode *node = bzla_iter_hashptr_next(&it);
    assert(node);
    assert(bzla_node_is_regular(node));
    assert(bzla_node_is_bv_var(node));
    id = bdcid(bdc, node);
    fprintf(file, "%d state %u", id, bzla_node_bv_get_width(bdc->bzla, node));
    if ((symbol = bzla_node_get_symbol(bdc->bzla, node)))
      fprintf(file, " %s", symbol);
    fputc('\n', file);
  }

  bzla_iter_hashptr_init(&it, bdc->states);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BzlaDumpContextState *bdcl = it.bucket->data.as_ptr;
    assert(bdcl->state);
    assert(bzla_node_is_regular(bdcl->state));
    assert(bzla_node_is_bv_var(bdcl->state));
    if (bdcl->next)
    {
      bdcrec(bdc, bdcl->next, file);
      id = ++bdc->maxid;
      fprintf(file,
              "%d next %u %d %d\n",
              id,
              bzla_node_bv_get_width(bdc->bzla, bdcl->next),
              bdcid(bdc, bdcl->state),
              bdcid(bdc, bdcl->next));
    }
    if (bdcl->init)
    {
      bdcrec(bdc, bdcl->init, file);
      id = ++bdc->maxid;
      fprintf(file,
              "%d init %u %d %d\n",
              id,
              bzla_node_bv_get_width(bdc->bzla, bdcl->init),
              bdcid(bdc, bdcl->state),
              bdcid(bdc, bdcl->init));
    }
    (void) bzla_iter_hashptr_next(&it);
  }

  for (i = 0; i < BZLA_COUNT_STACK(bdc->outputs); i++)
  {
    BzlaNode *node = BZLA_PEEK_STACK(bdc->outputs, i);
    bdcrec(bdc, node, file);
    id = ++bdc->maxid;
    fprintf(file,
            "%d output %u %d\n",
            id,
            bzla_node_bv_get_width(bdc->bzla, node),
            bdcid(bdc, node));
  }

  for (i = 0; i < BZLA_COUNT_STACK(bdc->bads); i++)
  {
    BzlaNode *node = BZLA_PEEK_STACK(bdc->bads, i);
    bdcrec(bdc, node, file);
    id = ++bdc->maxid;
    fprintf(file,
            "%d bad %u %d\n",
            id,
            bzla_node_bv_get_width(bdc->bzla, node),
            bdcid(bdc, node));
  }

  for (i = 0; i < BZLA_COUNT_STACK(bdc->constraints); i++)
  {
    BzlaNode *node = BZLA_PEEK_STACK(bdc->constraints, i);
    bdcrec(bdc, node, file);
    id = ++bdc->maxid;
    fprintf(file,
            "%d constraint %u %d\n",
            id,
            bzla_node_bv_get_width(bdc->bzla, node),
            bdcid(bdc, node));
  }

  for (i = 0; i < BZLA_COUNT_STACK(bdc->roots); i++)
  {
    BzlaNode *node = BZLA_PEEK_STACK(bdc->roots, i);
    assert(!bzla_node_is_args(node));
    bdcrec(bdc, node, file);
    id = ++bdc->maxid;
    if (bdc->version == 1)
    {
      if (bzla_sort_is_fun(bdc->bzla, bzla_node_get_sort_id(node)))
        len = bzla_sort_bv_get_width(
            bdc->bzla,
            bzla_sort_fun_get_codomain(bdc->bzla, bzla_node_get_sort_id(node)));
      else
        len = bzla_node_bv_get_width(bdc->bzla, node);
      fprintf(file, "%d root %u %d\n", id, len, bdcid(bdc, node));
    }
    else
      fprintf(file, "assert %d\n", bdcid(bdc, node));
  }
}

void
bzla_dumpbtor_dump_node(Bzla *bzla, FILE *file, BzlaNode *exp)
{
  assert(bzla);
  assert(file);
  assert(exp);
  assert(!bzla_node_is_args(exp));

  BzlaDumpContext *bdc;

  bdc = bzla_dumpbtor_new_dump_context(bzla);
  bzla_dumpbtor_add_root_to_dump_context(bdc, exp);
  bzla_dumpbtor_dump_bdc(bdc, file);
  bzla_dumpbtor_delete_dump_context(bdc);
}

void
bzla_dumpbtor_dump_nodes(Bzla *bzla,
                         FILE *file,
                         BzlaNode **roots,
                         uint32_t nroots)
{
  assert(bzla);
  assert(file);
  assert(roots);
  assert(nroots > 0);

  uint32_t i;
  BzlaDumpContext *bdc;

  bdc = bzla_dumpbtor_new_dump_context(bzla);

  for (i = 0; i < nroots; i++)
    bzla_dumpbtor_add_root_to_dump_context(bdc, roots[i]);

  bzla_dumpbtor_dump_bdc(bdc, file);
  bzla_dumpbtor_delete_dump_context(bdc);
}

void
bzla_dumpbtor_dump(Bzla *bzla, FILE *file, uint32_t version)
{
  assert(bzla);
  assert(file);
  assert(version == 1 || version == 2);
  (void) version;

  BzlaNode *tmp;
  BzlaDumpContext *bdc;
  BzlaPtrHashTableIterator it;

  bdc          = bzla_dumpbtor_new_dump_context(bzla);
  bdc->version = 1;  // NOTE: version 2 not yet supported

  if (bzla->inconsistent)
  {
    tmp = bzla_exp_false(bzla);
    bzla_dumpbtor_add_root_to_dump_context(bdc, tmp);
    bzla_node_release(bzla, tmp);
  }
  else if (bzla->unsynthesized_constraints->count == 0
           && bzla->synthesized_constraints->count == 0)
  {
    tmp = bzla_exp_true(bzla);
    bzla_dumpbtor_add_root_to_dump_context(bdc, tmp);
    bzla_node_release(bzla, tmp);
  }
  else
  {
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    while (bzla_iter_hashptr_has_next(&it))
      bzla_dumpbtor_add_root_to_dump_context(bdc, bzla_iter_hashptr_next(&it));
  }

  bzla_dumpbtor_dump_bdc(bdc, file);
  bzla_dumpbtor_delete_dump_context(bdc);
}

bool
bzla_dumpbtor_can_be_dumped(Bzla *bzla)
{
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, bzla->ufs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    if (!bzla_node_is_uf_array(cur)) return false;
  }
  return true;
}
