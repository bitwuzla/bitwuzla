/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaextract.h"

#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlasubst.h"
#include "preprocess/bzlapputils.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"


static void
extract_base_addr_offset(BzlaNode *bvadd, BzlaNode **base, BzlaNode **offset)
{
  assert(bzla_node_is_regular(bvadd));
  assert(bzla_node_is_bv_add(bvadd));

  if (bzla_node_is_bv_const(bvadd->e[0]))
  {
    if (offset) *offset = bvadd->e[0];
    if (base) *base = bvadd->e[1];
  }
  else
  {
    assert(bzla_node_is_bv_const(bvadd->e[1]));
    if (offset) *offset = bvadd->e[1];
    if (base) *base = bvadd->e[0];
  }
}

static int32_t
cmp_abs_rel_indices(const void *a, const void *b)
{
  bool is_abs;
  BzlaBitVector *bx, *by;
  BzlaNode *x, *y, *x_base_addr, *y_base_addr, *x_offset, *y_offset;

  x = *((BzlaNode **) a);
  y = *((BzlaNode **) b);

  is_abs = bzla_node_is_bv_const(x) && bzla_node_is_bv_const(y);

  if (is_abs) /* absolute address */
  {
    bx = bzla_node_bv_const_get_bits(x);
    by = bzla_node_bv_const_get_bits(y);
  }
  else /* relative address */
  {
    assert(!bzla_node_is_inverted(x));
    assert(!bzla_node_is_inverted(y));
    assert(bzla_node_is_bv_add(x));
    assert(bzla_node_is_bv_add(y));
    extract_base_addr_offset(x, &x_base_addr, &x_offset);
    extract_base_addr_offset(y, &y_base_addr, &y_offset);
    assert(x_base_addr == y_base_addr);
    assert(bzla_node_is_bv_const(x_offset));
    assert(bzla_node_is_bv_const(y_offset));
    bx = bzla_node_bv_const_get_bits(x_offset);
    by = bzla_node_bv_const_get_bits(y_offset);
  }
  assert(bx);
  assert(by);
  return bzla_bv_compare(bx, by);
}

/*
 *
 * diff: d
 * l,....,u
 * l <= i && i <= u && (u - i) % d == 0
 *
 * optimization if d is power of two
 *   l <= i && i <= u && (u - i) & (d - 1) = 0
 *
 *   l <= i && i <= u && (u - i)[bits(d) - 1 - 1: 0] = 0
 *
 *   d: 1
 *   l <= i && i <= u
 *
 *   d: 2
 *   l <= i && i <= u && (u - i)[0:0] = 0
 *
 *   d: 4
 *   l <= i && i <= u && (u - i)[1:0] = 0
 *
 *   d: 8
 *   l <= i && i <= u && (u - i)[2:0] = 0
 */
static inline BzlaNode *
create_range(Bzla *bzla,
             BzlaNode *lower,
             BzlaNode *upper,
             BzlaNode *param,
             BzlaBitVector *offset)
{
  assert(lower);
  assert(upper);
  assert(param);
  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));
  assert(bzla_node_is_bv_const(lower) || bzla_node_is_bv_add(lower));
  assert(bzla_node_is_bv_const(upper) || bzla_node_is_bv_add(upper));
  assert(bzla_node_get_sort_id(lower) == bzla_node_get_sort_id(upper));
  assert(offset);

  int64_t pos;
  BzlaNode *res, *le0, *le1, *and, *off, *sub, *rem, *eq, *zero, *slice;

  le0 = bzla_exp_bv_ulte(bzla, lower, param);
  le1 = bzla_exp_bv_ulte(bzla, param, upper);
  and = bzla_exp_bv_and(bzla, le0, le1);

  /* increment by one */
  if (bzla_bv_is_one(offset)) res = bzla_node_copy(bzla, and);
  /* increment by power of two */
  else if ((pos = bzla_bv_power_of_two(offset)) > -1)
  {
    assert(pos > 0);
    sub   = bzla_exp_bv_sub(bzla, upper, param);
    slice = bzla_exp_bv_slice(bzla, sub, pos - 1, 0);
    zero  = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(slice));
    eq    = bzla_exp_eq(bzla, slice, zero);
    res   = bzla_exp_bv_and(bzla, and, eq);

    bzla_node_release(bzla, zero);
    bzla_node_release(bzla, slice);
    bzla_node_release(bzla, sub);
    bzla_node_release(bzla, eq);
  }
  /* increment by some arbitrary value */
  else
  {
    zero = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(lower));
    off  = bzla_exp_bv_const(bzla, offset);
    assert(bzla_node_get_sort_id(off) == bzla_node_get_sort_id(lower));
    sub = bzla_exp_bv_sub(bzla, upper, param);
    rem = bzla_exp_bv_urem(bzla, sub, off);
    eq  = bzla_exp_eq(bzla, rem, zero);
    res = bzla_exp_bv_and(bzla, and, eq);

    bzla_node_release(bzla, zero);
    bzla_node_release(bzla, off);
    bzla_node_release(bzla, sub);
    bzla_node_release(bzla, rem);
    bzla_node_release(bzla, eq);
  }
  bzla_node_release(bzla, le0);
  bzla_node_release(bzla, le1);
  bzla_node_release(bzla, and);
  return res;
}

/* pattern: lower <= j <= upper && range_cond ? value : a[j] */
static inline BzlaNode *
create_pattern_memset(Bzla *bzla,
                      BzlaNode *lower,
                      BzlaNode *upper,
                      BzlaNode *value,
                      BzlaNode *array,
                      BzlaBitVector *offset)
{
  assert(lower);
  assert(upper);
  assert(bzla_node_real_addr(lower)->kind == bzla_node_real_addr(upper)->kind);
  assert(bzla_node_is_bv_const(lower) || bzla_node_is_bv_add(lower));
  assert(bzla_node_get_sort_id(lower) == bzla_node_get_sort_id(upper));
  assert(offset);

  BzlaNode *res, *param, *ite, *read, *cond;

  param = bzla_exp_param(bzla, bzla_node_get_sort_id(lower), 0);
  read  = bzla_exp_read(bzla, array, param);
  cond  = create_range(bzla, lower, upper, param, offset);
  ite   = bzla_exp_cond(bzla, cond, value, read);
  res   = bzla_exp_lambda(bzla, param, ite);

  bzla_node_release(bzla, param);
  bzla_node_release(bzla, read);
  bzla_node_release(bzla, cond);
  bzla_node_release(bzla, ite);

  return res;
}

/* pattern: lower <= j <= upper && range_cond ? j : a[j] */
static inline BzlaNode *
create_pattern_itoi(Bzla *bzla,
                    BzlaNode *lower,
                    BzlaNode *upper,
                    BzlaNode *array,
                    BzlaBitVector *offset)
{
  assert(lower);
  assert(upper);
  assert(bzla_node_real_addr(lower)->kind == bzla_node_real_addr(upper)->kind);
  assert(bzla_node_is_bv_const(lower) || bzla_node_is_bv_add(lower));
  assert(bzla_node_get_sort_id(lower) == bzla_node_get_sort_id(upper));
  assert(bzla_sort_fun_get_codomain(bzla, bzla_node_get_sort_id(array))
         == bzla_node_get_sort_id(lower));
  assert(offset);

  BzlaNode *res, *param, *ite, *read, *cond;

  param = bzla_exp_param(bzla, bzla_node_get_sort_id(lower), 0);
  read  = bzla_exp_read(bzla, array, param);
  cond  = create_range(bzla, lower, upper, param, offset);
  ite   = bzla_exp_cond(bzla, cond, param, read);
  res   = bzla_exp_lambda(bzla, param, ite);

  bzla_node_release(bzla, param);
  bzla_node_release(bzla, read);
  bzla_node_release(bzla, cond);
  bzla_node_release(bzla, ite);

  return res;
}

/* pattern: lower <= j <= upper && range_cond ? j + 1 : a[j] */
static inline BzlaNode *
create_pattern_itoip1(Bzla *bzla,
                      BzlaNode *lower,
                      BzlaNode *upper,
                      BzlaNode *array,
                      BzlaBitVector *offset)
{
  assert(lower);
  assert(upper);
  assert(bzla_node_real_addr(lower)->kind == bzla_node_real_addr(upper)->kind);
  assert(bzla_node_is_bv_const(lower) || bzla_node_is_bv_add(lower));
  assert(bzla_node_get_sort_id(lower) == bzla_node_get_sort_id(upper));
  assert(bzla_sort_fun_get_codomain(bzla, bzla_node_get_sort_id(array))
         == bzla_node_get_sort_id(lower));
  assert(offset);

  BzlaNode *res, *param, *ite, *read, *cond, *inc;

  param = bzla_exp_param(bzla, bzla_node_get_sort_id(lower), 0);
  read  = bzla_exp_read(bzla, array, param);
  cond  = create_range(bzla, lower, upper, param, offset);
  inc   = bzla_exp_bv_inc(bzla, param);
  ite   = bzla_exp_cond(bzla, cond, inc, read);
  res   = bzla_exp_lambda(bzla, param, ite);

  bzla_node_release(bzla, param);
  bzla_node_release(bzla, read);
  bzla_node_release(bzla, cond);
  bzla_node_release(bzla, inc);
  bzla_node_release(bzla, ite);

  return res;
}

static inline BzlaNode *
create_pattern_cpy(Bzla *bzla,
                   BzlaNode *lower,
                   BzlaNode *upper,
                   BzlaNode *src_array,
                   BzlaNode *dst_array,
                   BzlaNode *src_addr,
                   BzlaNode *dst_addr,
                   BzlaBitVector *offset)
{
  assert(!bzla_node_is_inverted(lower));
  assert(!bzla_node_is_inverted(upper));
  assert(bzla_node_is_bv_add(lower));
  assert(bzla_node_is_bv_add(upper));

  BzlaNode *res, *param, *ite, *read, *cond, *read_src, *add, *sub;

  param = bzla_exp_param(bzla, bzla_node_get_sort_id(lower), 0);
  read  = bzla_exp_read(bzla, dst_array, param);
  cond  = create_range(bzla, lower, upper, param, offset);

  sub      = bzla_exp_bv_sub(bzla, param, dst_addr);
  add      = bzla_exp_bv_add(bzla, src_addr, sub);
  read_src = bzla_exp_read(bzla, src_array, add);
  ite      = bzla_exp_cond(bzla, cond, read_src, read);
  res      = bzla_exp_lambda(bzla, param, ite);

  bzla_node_release(bzla, param);
  bzla_node_release(bzla, read);
  bzla_node_release(bzla, cond);
  bzla_node_release(bzla, sub);
  bzla_node_release(bzla, add);
  bzla_node_release(bzla, read_src);
  bzla_node_release(bzla, ite);
  return res;
}

static bool
is_write_exp(BzlaNode *exp,
             BzlaNode **array,
             BzlaNode **index,
             BzlaNode **value)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));

  BzlaNode *param, *body, *eq, *app;

  if (!bzla_node_is_lambda(exp) || bzla_node_fun_get_arity(exp->bzla, exp) > 1)
    return false;

  param = exp->e[0];
  body  = bzla_node_binder_get_body(exp);

  if (bzla_node_is_inverted(body) || !bzla_node_is_bv_cond(body)) return false;

  /* check condition */
  eq = body->e[0];
  if (bzla_node_is_inverted(eq) || !bzla_node_is_bv_eq(eq) || !eq->parameterized
      || (eq->e[0] != param && eq->e[1] != param))
    return false;

  /* check value */
  if (bzla_node_real_addr(body->e[1])->parameterized) return false;

  /* check apply on unmodified array */
  app = body->e[2];
  if (bzla_node_is_inverted(app) || !bzla_node_is_apply(app)
      || bzla_node_fun_get_arity(app->bzla, app->e[0]) > 1
      || app->e[1]->e[0] != param)
    return false;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return true;
}

static bool
is_array_ite_exp(BzlaNode *exp, BzlaNode **array_if, BzlaNode **array_else)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));

  BzlaNode *param, *body, *app_if, *app_else;

  if (!bzla_node_is_lambda(exp) || bzla_node_fun_get_arity(exp->bzla, exp) > 1)
    return false;

  param = exp->e[0];
  body  = bzla_node_binder_get_body(exp);

  if (bzla_node_is_inverted(body) || !bzla_node_is_bv_cond(body)) return false;

  /* check value */
  if (!bzla_node_real_addr(body->e[1])->parameterized
      || !bzla_node_real_addr(body->e[2])->parameterized)
    return false;

  /* check applies in if and else branch */
  app_if = body->e[1];
  if (bzla_node_is_inverted(app_if) || !bzla_node_is_apply(app_if)
      || bzla_node_fun_get_arity(app_if->bzla, app_if->e[0]) > 1
      || app_if->e[1]->e[0] != param)
    return false;

  app_else = body->e[1];
  if (bzla_node_is_inverted(app_else) || !bzla_node_is_apply(app_else)
      || bzla_node_fun_get_arity(app_else->bzla, app_else->e[0]) > 1
      || app_else->e[1]->e[0] != param)
    return false;

  if (array_if) *array_if = app_if->e[0];
  if (array_else) *array_else = app_else->e[0];
  return true;
}

inline static bool
is_itoi_pattern(BzlaNode *index, BzlaNode *value)
{
  return index == value;
}

static bool
is_itoip1_pattern(BzlaNode *index, BzlaNode *value)
{
  bool res;
  BzlaNode *inc;

  inc = bzla_exp_bv_inc(bzla_node_real_addr(index)->bzla, index);
  res = inc == value;
  bzla_node_release(bzla_node_real_addr(index)->bzla, inc);
  return res;
}

static bool
is_cpy_pattern(BzlaNode *index, BzlaNode *value)
{
  BzlaNode *bvadd, *dst_addr, *off;

  if (bzla_node_is_inverted(index) || !bzla_node_is_bv_add(index)
      || bzla_node_is_inverted(value) || !bzla_node_is_apply(value)
      || bzla_node_is_inverted(value->e[1]->e[0])
      || !bzla_node_is_bv_add(value->e[1]->e[0]))
    return false;

  if (bzla_node_is_bv_const(index->e[0]))
    off = index->e[0];
  else if (bzla_node_is_bv_const(index->e[1]))
    off = index->e[1];
  else
    return false;

  bvadd    = value->e[1]->e[0];
  dst_addr = 0;
  if (bvadd->e[0] == off)
    dst_addr = bvadd->e[1];
  else if (bvadd->e[1] == off)
    dst_addr = bvadd->e[0];

  return dst_addr != 0;
}

/* extracts source array, source address, destination address and offset of
 * a memcopy pattern. */
static void
extract_cpy_src_dst_info(BzlaNode *index,
                         BzlaNode *value,
                         BzlaNode **src_array,
                         BzlaNode **src_addr,
                         BzlaNode **dst_addr,
                         BzlaNode **off)
{
  assert(is_cpy_pattern(index, value));

  BzlaNode *bvadd, *offset;

  extract_base_addr_offset(index, dst_addr, &offset);
  bvadd = value->e[1]->e[0];
  if (off) *off = offset;
  if (src_addr) *src_addr = bvadd->e[0] == offset ? bvadd->e[1] : bvadd->e[0];
  if (src_array) *src_array = value->e[0];
}

inline static bool
is_abs_set_pattern(BzlaNode *index, BzlaNode *prev_index)
{
  return bzla_node_is_bv_const(index)
         && (!prev_index || bzla_node_is_bv_const(prev_index));
}

static void
add_to_index_map(Bzla *bzla,
                 BzlaPtrHashTable *map_value_index,
                 BzlaNode *lambda,
                 BzlaNode *index,
                 BzlaNode *value)
{
  BzlaMemMgr *mm;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTable *t;
  BzlaNodePtrStack *indices;
  BzlaNode *offset;

  mm = bzla->mm;

  if (!(b = bzla_hashptr_table_get(map_value_index, lambda)))
  {
    b              = bzla_hashptr_table_add(map_value_index, lambda);
    t              = bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    b->data.as_ptr = t;
  }
  else
    t = b->data.as_ptr;
  assert(t);

  if (!(b = bzla_hashptr_table_get(t, value)))
  {
    b = bzla_hashptr_table_add(t, value);
    BZLA_NEW(mm, indices);
    BZLA_INIT_STACK(mm, *indices);
    b->data.as_ptr = indices;
  }
  else
    indices = (BzlaNodePtrStack *) b->data.as_ptr;
  assert(indices);
  if (bzla_node_is_bv_const(index))
    offset = index;
  else
  {
    assert(bzla_node_is_regular(index));
    assert(bzla_node_is_bv_add(index));
    extract_base_addr_offset(index, 0, &offset);
    assert(bzla_node_is_bv_const(offset));
  }

  BZLA_PUSH_STACK(*indices, index);
}

static bool
check_and_add_index(Bzla *bzla,
                    BzlaPtrHashTable *map_value_index,
                    BzlaNode *fun,
                    BzlaNode *index,
                    BzlaNode *prev_index,
                    BzlaNode *value,
                    BzlaIntHashTable *index_cache)
{
  if (!is_abs_set_pattern(index, prev_index)) return false;

  bzla_hashint_table_add(index_cache, bzla_node_get_id(index));
  add_to_index_map(bzla, map_value_index, fun, index, value);
  return true;
}

static void
collect_indices_updates(Bzla *bzla,
                        BzlaPtrHashTable *map_value_index,
                        BzlaPtrHashTable *map_lambda_base)
{
  uint32_t i;
  BzlaNode *cur, *cur_upd, *top_upd, *index, *prev_index, *value;
  BzlaNode *prev_value;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack visit, upd_nodes;
  BzlaIntHashTable *visit_cache, *index_cache;

  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_INIT_STACK(bzla->mm, upd_nodes);
  visit_cache = bzla_hashint_table_new(bzla->mm);

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(visit, cur);
  }

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(visit_cache, cur->id)) continue;

    bzla_hashint_table_add(visit_cache, cur->id);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);

    /* follow update chains */
    // TODO: add fun equalities?
    if (bzla_node_is_apply(cur))
      BZLA_PUSH_STACK(upd_nodes, cur->e[0]);
    else if (bzla_node_is_fun_cond(cur))
    {
      BZLA_PUSH_STACK(upd_nodes, cur->e[1]);
      BZLA_PUSH_STACK(upd_nodes, cur->e[2]);
    }

    while (!BZLA_EMPTY_STACK(upd_nodes))
    {
      cur_upd = top_upd = BZLA_POP_STACK(upd_nodes);
      prev_index = prev_value = 0;

      if (bzla_hashint_table_contains(visit_cache, bzla_node_get_id(top_upd)))
        continue;

      index_cache = bzla_hashint_table_new(bzla->mm);
      while (bzla_node_is_update(cur_upd))
      {
        assert(bzla_node_is_regular(cur_upd));
        assert(cur_upd->is_array);
        index = cur_upd->e[1]->e[0];
        value = cur_upd->e[2];

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (bzla_hashint_table_contains(index_cache, bzla_node_get_id(index)))
        {
          cur_upd = cur_upd->e[0];
          continue;
        }

        /* use array as new start point */
        if (!check_and_add_index(bzla,
                                 map_value_index,
                                 top_upd,
                                 index,
                                 prev_index,
                                 value,
                                 index_cache))
        {
          break;
        }

        cur_upd    = cur_upd->e[0];
        prev_index = index;
        prev_value = value;
      }
      if (bzla_node_is_update(top_upd))
      {
        if (bzla_hashptr_table_get(map_value_index, top_upd))
        {
          assert(!bzla_hashptr_table_get(map_lambda_base, top_upd));
          bzla_hashptr_table_add(map_lambda_base, top_upd)->data.as_ptr =
              cur_upd;
        }
      }
      bzla_hashint_table_delete(index_cache);
      bzla_hashint_table_add(visit_cache, bzla_node_get_id(top_upd));
    }
  }
  bzla_hashint_table_delete(visit_cache);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(upd_nodes);
}

static void
collect_indices_lambdas(Bzla *bzla,
                        BzlaPtrHashTable *map_value_index,
                        BzlaPtrHashTable *map_lambda_base)
{
  size_t i;
  bool is_top;
  BzlaNode *lambda, *cur, *array, *index, *value, *tmp, *array_if, *array_else;
  BzlaNode *prev_index, *prev_value;
  BzlaNodeIterator it;
  BzlaNodePtrStack visit, lambdas;
  BzlaIntHashTable *index_cache, *visit_cache;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, lambdas);
  visit_cache = bzla_hashint_table_new(mm);

  bzla_pputils_collect_lambdas(bzla, &lambdas);

  /* collect lambdas that are at the top of lambda chains */
  for (i = 0; i < BZLA_COUNT_STACK(lambdas); i++)
  {
    lambda = bzla_node_get_simplified(bzla, BZLA_PEEK_STACK(lambdas, i));
    assert(bzla_node_is_regular(lambda));

    if (!bzla_node_is_lambda(lambda)) continue;

    /* already visited */
    if (bzla_hashptr_table_get(map_value_index, lambda)) continue;

    /* we only consider writes */
    if (!lambda->is_array || !bzla_node_lambda_get_static_rho(lambda)) continue;

    is_top = false;
    bzla_iter_apply_parent_init(&it, lambda);
    while (bzla_iter_apply_parent_has_next(&it))
    {
      tmp = bzla_iter_apply_parent_next(&it);

      if (!tmp->parameterized)
      {
        is_top = true;
        break;
      }
    }

    if (!is_top) continue;

    BZLA_PUSH_STACK(visit, lambda);
    while (!BZLA_EMPTY_STACK(visit))
    {
      lambda = BZLA_POP_STACK(visit);

      /* already visited */
      if (bzla_hashint_table_contains(visit_cache, bzla_node_get_id(lambda)))
        continue;

      bzla_hashint_table_add(visit_cache, bzla_node_get_id(lambda));

      cur         = lambda;
      index_cache = bzla_hashint_table_new(mm);
      prev_index = prev_value = 0;
      while (is_write_exp(cur, &array, &index, &value))
      {
        assert(bzla_node_is_regular(array));
        assert(bzla_node_is_fun(array));

        /* index already cached, this index will be overwritten anyways,
         * so we can skip it */
        if (bzla_hashint_table_contains(index_cache, bzla_node_get_id(index)))
        {
          cur = array;
          continue;
        }

        /* use array as new start point */
        if (!check_and_add_index(bzla,
                                 map_value_index,
                                 lambda,
                                 index,
                                 prev_index,
                                 value,
                                 index_cache))
        {
          BZLA_PUSH_STACK(visit, array);
          break;
        }

        cur        = array;
        prev_index = index;
        prev_value = value;
      }
      if (bzla_hashptr_table_get(map_value_index, lambda))
      {
        assert(!bzla_hashptr_table_get(map_lambda_base, lambda));
        bzla_hashptr_table_add(map_lambda_base, lambda)->data.as_ptr = cur;
      }
      bzla_hashint_table_delete(index_cache);

      // TODO (ma): can only be ite now change to is_fun_cond_node check
      if (is_array_ite_exp(cur, &array_if, &array_else))
      {
        BZLA_PUSH_STACK(visit, array_if);
        BZLA_PUSH_STACK(visit, array_else);
      }
    }
  }
  bzla_hashint_table_delete(visit_cache);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(lambdas);
}

static void
collect_indices_top_eqs(Bzla *bzla, BzlaPtrHashTable *map_value_index)
{
  BzlaPtrHashTableIterator it;
  BzlaNode *cur, *lhs, *rhs, *read, *array, *index, *value;

  /* top level equality pre-initialization */
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    if (bzla_node_is_inverted(cur) || !bzla_node_is_bv_eq(cur)) continue;

    lhs = cur->e[0];
    rhs = cur->e[1];

    index = value = 0;
    if (!bzla_node_is_inverted(lhs) && bzla_node_is_apply(lhs)
        && bzla_node_is_uf_array(lhs->e[0])
        && bzla_node_is_bv_const(lhs->e[1]->e[0]) && bzla_node_is_bv_const(rhs))
    {
      read  = lhs;
      array = lhs->e[0];
      index = lhs->e[1]->e[0];
      value = rhs;
    }
    else if (!bzla_node_is_inverted(rhs) && bzla_node_is_apply(rhs)
             && bzla_node_is_uf_array(rhs->e[0])
             && bzla_node_is_bv_const(rhs->e[1]->e[0])
             && bzla_node_is_bv_const(lhs))
    {
      read  = rhs;
      array = rhs->e[0];
      index = rhs->e[1]->e[0];
      value = lhs;
    }

    if (!index) continue;

    if (bzla_hashptr_table_get(bzla->substitutions, read)) continue;

    /* only add each index once */
    add_to_index_map(bzla, map_value_index, array, index, value);

    /* substitute 'read' with 'value', in order to prevent down propgation
     * rewriting for 'read' during substitute_and_rebuild(...), which
     * simplifies 'read' to 'value' anyways.
     * NOTE: if 'read' is already in 'substitutions', we let the rewriting
     * engine handle inconsistencies (i,e., if 'value' is not the same
     * as in 'substitutions'. */
    bzla_insert_substitution(bzla, read, value, false);
  }
}

static void
find_ranges(Bzla *bzla,
            BzlaNodePtrStack *stack,
            BzlaNodePtrStack *ranges,
            BzlaBitVectorPtrStack *increments,
            BzlaNodePtrStack *indices,
            BzlaNodePtrStack *indices_ranges,
            uint32_t *num_pat,
            uint32_t *num_pat_inc,
            uint32_t *size_pat,
            uint32_t *size_pat_inc)
{
  assert(stack);
  assert(ranges);
  assert(increments);
  assert(indices);
  assert(num_pat);
  assert(size_pat);

#ifndef NDEBUG
  uint32_t num_indices = 0;
#endif
  bool in_range;
  BzlaBitVector *b0, *b1, *inc, *prev_inc;
  uint32_t i, cnt, lower, upper;
  uint32_t num_pattern = 0, num_pattern_inc = 0, size_pattern = 0;
  uint32_t size_pattern_inc = 0;
  BzlaNode *n0, *n1, *n0_base_addr, *n1_base_addr, *n0_offset, *n1_offset;
  BzlaMemMgr *mm;
  BzlaNodePtrStack index_stack;

  mm          = bzla->mm;
  index_stack = *stack;
  cnt         = BZLA_COUNT_STACK(index_stack);
  if (cnt == 0) return;

  if (cnt == 1)
    BZLA_PUSH_STACK(*indices, BZLA_PEEK_STACK(index_stack, 0));
  else
  {
    assert(cnt > 1);
#ifndef NDEBUG
    /* sanity check: 'index_stack' contains either absolute or relative
     * addresses */
    for (i = 1; i < BZLA_COUNT_STACK(index_stack); i++)
    {
      n0 = bzla_node_real_addr(BZLA_PEEK_STACK(index_stack, i - 1));
      n1 = bzla_node_real_addr(BZLA_PEEK_STACK(index_stack, i));
      assert(n0->kind == n1->kind);
      assert(bzla_node_is_bv_add(n0) || bzla_node_is_bv_const(n0));
      if (bzla_node_is_bv_add(n0))
      {
        extract_base_addr_offset(n0, &n0_base_addr, &n0_offset);
        extract_base_addr_offset(n1, &n1_base_addr, &n1_offset);
        assert(n0_base_addr == n1_base_addr);
        assert(bzla_node_is_bv_const(n0_offset));
        assert(bzla_node_is_bv_const(n1_offset));
      }
    }
#endif
    qsort(index_stack.start, cnt, sizeof(BzlaNode *), cmp_abs_rel_indices);
    inc = prev_inc = 0;
    lower = upper = 0;
    while (upper < cnt)
    {
      in_range = false;
      inc      = 0;
      if (upper + 1 < cnt)
      {
        n0 = BZLA_PEEK_STACK(index_stack, upper);
        n1 = BZLA_PEEK_STACK(index_stack, upper + 1);

        if (bzla_node_is_bv_const(n0))
        {
          assert(bzla_node_is_bv_const(n1));
          b0 = bzla_node_bv_const_get_bits(n0);
          b1 = bzla_node_bv_const_get_bits(n1);
        }
        else
        {
          assert(!bzla_node_is_inverted(n0));
          assert(!bzla_node_is_inverted(n1));
          assert(bzla_node_is_bv_add(n0));
          assert(bzla_node_is_bv_add(n1));
          extract_base_addr_offset(n0, &n0_base_addr, &n0_offset);
          extract_base_addr_offset(n1, &n1_base_addr, &n1_offset);
          assert(n0_base_addr == n1_base_addr);
          b0 = bzla_node_bv_const_get_bits(n0_offset);
          b1 = bzla_node_bv_const_get_bits(n1_offset);
        }
        assert(b0);
        assert(b1);
        inc = bzla_bv_sub(mm, b1, b0);

        if (!prev_inc) prev_inc = bzla_bv_copy(mm, inc);

        /* increment upper bound of range */
        in_range = bzla_bv_compare(inc, prev_inc) == 0;
        if (in_range) upper += 1;
      }

      if (!in_range)
      {
        /* push index */
        if (upper == lower)
        {
          BZLA_PUSH_STACK(*indices, BZLA_PEEK_STACK(index_stack, lower));
#ifndef NDEBUG
          num_indices++;
#endif
          goto NEW_RANGE;
        }
        /* range is too small, push separate indices */
        else if (upper - lower <= 1
                 /* range with an offset greater than 1 */
                 && bzla_bv_power_of_two(prev_inc) != 0)
        {
          /* last iteration step: if range contains all indices
           * up to the last one, we can push all indices */
          if (upper == cnt - 1) upper += 1;

          /* push all indices from lower until upper - 1 */
          for (; lower < upper; lower++)
          {
            BZLA_PUSH_STACK(*indices, BZLA_PEEK_STACK(index_stack, lower));
#ifndef NDEBUG
            num_indices++;
#endif
          }
          /* lower is now that last index in the range, from
           * which we try to find a new range */
          upper += 1;
        }
        /* found range */
        else
        {
          assert(upper - lower > 0);
          BZLA_PUSH_STACK(*increments, prev_inc);
          BZLA_PUSH_STACK(*ranges, BZLA_PEEK_STACK(index_stack, lower));
          BZLA_PUSH_STACK(*ranges, BZLA_PEEK_STACK(index_stack, upper));
          /* push all indices in range lower <= i <= upper onto
           * 'indices_ranges' stack */
          for (i = lower; i <= upper; i++)
            BZLA_PUSH_STACK(*indices_ranges, BZLA_PEEK_STACK(index_stack, i));
          BZLA_PUSH_STACK(*indices_ranges, 0);
#ifndef NDEBUG
          num_indices += upper - lower + 1;
#endif
          if (bzla_bv_is_one(prev_inc))
          {
            size_pattern += upper - lower + 1;
            num_pattern++;
          }
          else
          {
            size_pattern_inc += upper - lower + 1;
            num_pattern_inc++;
          }
          /* 'prev_inc' will be released later */
          prev_inc = 0;
        NEW_RANGE:
          /* reset range */
          upper += 1;
          lower = upper;
          if (inc) bzla_bv_free(mm, inc);
          inc = 0;
        }
      }
      if (prev_inc) bzla_bv_free(mm, prev_inc);
      prev_inc = inc;
    }
    if (inc) bzla_bv_free(mm, inc);
    assert(num_indices == cnt);
  }

  /* return statistics */
  if (num_pat)
  {
    *num_pat += num_pattern;
    /* if no separate statistic variable is given for the 'inc' pattern,
     * we just add the number to the normal one */
    if (!num_pat_inc) *num_pat += num_pattern_inc;
  }
  if (num_pat_inc) *num_pat_inc += num_pattern_inc;
  if (size_pat)
  {
    *size_pat += size_pattern;
    /* if no separate statistic variable is given for the 'inc' pattern,
     * we just add the size to the normal one */
    if (!size_pat_inc) *size_pat += size_pattern_inc;
  }
  if (size_pat_inc) *size_pat_inc += size_pattern_inc;
}

static BzlaPtrHashTable *
create_static_rho(Bzla *bzla,
                  BzlaNode *indices[],
                  BzlaNode *value,
                  BzlaPtrHashTable *index_value_map)
{
  uint32_t i;
  BzlaNode *idx, *args;
  BzlaPtrHashTable *static_rho;
  BzlaPtrHashBucket *b;

  static_rho = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  if (value)
  {
    for (i = 0; indices[i]; i++)
    {
      idx            = indices[i];
      args           = bzla_exp_args(bzla, &idx, 1);
      b              = bzla_hashptr_table_add(static_rho, args);
      b->data.as_ptr = bzla_node_copy(bzla, value);
    }
  }
  else
  {
    assert(index_value_map);
    for (i = 0; indices[i]; i++)
    {
      idx = indices[i];
      b   = bzla_hashptr_table_get(index_value_map, idx);
      assert(b);
      value          = b->data.as_ptr;
      args           = bzla_exp_args(bzla, &idx, 1);
      b              = bzla_hashptr_table_add(static_rho, args);
      b->data.as_ptr = bzla_node_copy(bzla, value);
    }
  }
  return static_rho;
}

static uint32_t
extract_lambdas(Bzla *bzla,
                BzlaPtrHashTable *map_value_index,
                BzlaPtrHashTable *map_lambda_base)
{
  assert(bzla);
  assert(map_value_index);
  assert(map_lambda_base);

  bool is_top_eq;
  BzlaBitVector *inc;
  uint32_t i_range, i_index, i_value, i_inc, i_index_r;
  BzlaNode *subst, *base, *tmp, *array, *value, *lower, *upper;
  BzlaNode *src_array, *src_addr, *dst_addr;
  BzlaPtrHashTableIterator it, iit;
  BzlaPtrHashTable *t, *index_value_map, *static_rho;
  BzlaPtrHashBucket *b;
  BzlaNodePtrStack ranges, indices, values, indices_itoi, indices_itoip1;
  BzlaNodePtrStack indices_cpy, indices_rem, indices_ranges, *stack;
  BzlaBitVectorPtrStack increments;
  BzlaMemMgr *mm;

  /* statistics */
  uint32_t num_total = 0, num_writes = 0;
  uint32_t num_set = 0, num_set_inc = 0, num_set_itoi = 0, num_set_itoip1 = 0;
  uint32_t num_cpy = 0, size_set = 0, size_set_inc = 0, size_set_itoi = 0;
  uint32_t size_set_itoip1 = 0, size_cpy = 0;

  mm = bzla->mm;
  BZLA_INIT_STACK(mm, ranges);
  BZLA_INIT_STACK(mm, indices);
  BZLA_INIT_STACK(mm, indices_ranges);
  BZLA_INIT_STACK(mm, increments);
  BZLA_INIT_STACK(mm, values);
  BZLA_INIT_STACK(mm, indices_itoi);
  BZLA_INIT_STACK(mm, indices_itoip1);
  BZLA_INIT_STACK(mm, indices_cpy);
  BZLA_INIT_STACK(mm, indices_rem);
  bzla_iter_hashptr_init(&it, map_value_index);
  while (bzla_iter_hashptr_has_next(&it))
  {
    t     = it.bucket->data.as_ptr;
    array = bzla_node_get_simplified(bzla, bzla_iter_hashptr_next(&it));
    assert(t);
    assert(array->is_array);

    /* find memset patterns, the remaining unused indices are pushed onto
     * stack 'indices' */
    bzla_iter_hashptr_init(&iit, t);
    while (bzla_iter_hashptr_has_next(&iit))
    {
      stack = iit.bucket->data.as_ptr;
      value = bzla_iter_hashptr_next(&iit);
      assert(stack);
      find_ranges(bzla,
                  stack,
                  &ranges,
                  &increments,
                  &indices,
                  &indices_ranges,
                  &num_set,
                  &num_set_inc,
                  &size_set,
                  &size_set_inc);
      BZLA_PUSH_STACK(ranges, 0);
      BZLA_PUSH_STACK(indices, 0);
      BZLA_PUSH_STACK(values, value);
      assert(BZLA_COUNT_STACK(ranges) - BZLA_COUNT_STACK(values) > 0
             || BZLA_COUNT_STACK(indices) - BZLA_COUNT_STACK(values) > 0);
      assert((BZLA_COUNT_STACK(ranges) - BZLA_COUNT_STACK(values)) % 2 == 0);
      assert((BZLA_COUNT_STACK(ranges) - BZLA_COUNT_STACK(values)) / 2
             == BZLA_COUNT_STACK(increments));
    }

    /* choose base array for patterns/writes:
     *  1) write chains: base array of the write chains
     *  2) top eqs: a new UF symbol */
    if ((b = bzla_hashptr_table_get(map_lambda_base, array)))
    {
      assert(bzla_node_is_lambda(array) || bzla_node_is_update(array));
      b = bzla_hashptr_table_get(map_lambda_base, array);
      assert(b);
      subst     = bzla_node_copy(bzla, b->data.as_ptr);
      is_top_eq = false;
    }
    else if (bzla_node_is_uf_array(array))
    {
      subst     = bzla_exp_array(bzla, bzla_node_get_sort_id(array), 0);
      is_top_eq = true;
    }
    else
    {
      continue;
    }

    index_value_map =
        bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    base    = subst;
    i_range = i_index = i_inc = 0;
    i_index_r                 = 0;
    for (i_value = 0; i_value < BZLA_COUNT_STACK(values); i_value++)
    {
      value = BZLA_PEEK_STACK(values, i_value);

      /* create memset regions */
      for (; i_range < BZLA_COUNT_STACK(ranges) - 1; i_range += 2)
      {
        lower = BZLA_PEEK_STACK(ranges, i_range);
        /* next value */
        if (!lower)
        {
          i_range++;
          break;
        }
        upper = BZLA_PEEK_STACK(ranges, i_range + 1);
        assert(i_inc < BZLA_COUNT_STACK(increments));
        inc = BZLA_PEEK_STACK(increments, i_inc);
        tmp = create_pattern_memset(bzla, lower, upper, value, subst, inc);
        tmp->is_array = 1;
        bzla_node_release(bzla, subst);
        subst = tmp;
        bzla_bv_free(mm, inc);
        i_inc++;

        assert(i_index_r < BZLA_COUNT_STACK(indices_ranges));
        static_rho =
            create_static_rho(bzla, indices_ranges.start + i_index_r, value, 0);
        i_index_r += static_rho->count + 1;
        if (bzla_node_lambda_get_static_rho(subst))
          bzla_node_lambda_delete_static_rho(bzla, subst);
        bzla_node_lambda_set_static_rho(subst, static_rho);
      }

      /* find patterns that are dependent on the current index */
      for (; i_index < BZLA_COUNT_STACK(indices); i_index++)
      {
        lower = BZLA_PEEK_STACK(indices, i_index);
        /* next value */
        if (!lower)
        {
          i_index++;
          break;
        }
        assert(!bzla_hashptr_table_get(index_value_map, lower));
        /* save index value pairs for later */
        bzla_hashptr_table_add(index_value_map, lower)->data.as_ptr = value;

        /* pattern 1: index -> index */
        if (is_itoi_pattern(lower, value)) BZLA_PUSH_STACK(indices_itoi, lower);
        /* pattern 2: index -> index + 1 */
        else if (is_itoip1_pattern(lower, value))
          BZLA_PUSH_STACK(indices_itoip1, lower);
        /* pattern 3: memcopy pattern */
        else if (is_cpy_pattern(lower, value))
          BZLA_PUSH_STACK(indices_cpy, lower);
        else /* no pattern found */
          BZLA_PUSH_STACK(indices_rem, lower);
      }
    }

    /* pattern: index -> index */
    BZLA_RESET_STACK(ranges);
    BZLA_RESET_STACK(indices_ranges);
    BZLA_RESET_STACK(increments);
    find_ranges(bzla,
                &indices_itoi,
                &ranges,
                &increments,
                &indices_rem,
                &indices_ranges,
                &num_set_itoi,
                0,
                &size_set_itoi,
                0);
    i_index_r = 0;
    if (!BZLA_EMPTY_STACK(ranges))
    {
      assert(BZLA_COUNT_STACK(ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BZLA_COUNT_STACK(ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BZLA_PEEK_STACK(ranges, i_range);
        upper = BZLA_PEEK_STACK(ranges, i_range + 1);
        assert(i_inc < BZLA_COUNT_STACK(increments));
        inc           = BZLA_PEEK_STACK(increments, i_inc);
        tmp           = create_pattern_itoi(bzla, lower, upper, subst, inc);
        tmp->is_array = 1;
        bzla_node_release(bzla, subst);
        subst = tmp;
        bzla_bv_free(mm, inc);

        assert(i_index_r < BZLA_COUNT_STACK(indices_ranges));
        static_rho = create_static_rho(
            bzla, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (bzla_node_lambda_get_static_rho(subst))
          bzla_node_lambda_delete_static_rho(bzla, subst);
        bzla_node_lambda_set_static_rho(subst, static_rho);
      }
    }

    /* pattern: index -> index + 1 */
    BZLA_RESET_STACK(ranges);
    BZLA_RESET_STACK(indices_ranges);
    BZLA_RESET_STACK(increments);
    find_ranges(bzla,
                &indices_itoip1,
                &ranges,
                &increments,
                &indices_rem,
                &indices_ranges,
                &num_set_itoip1,
                0,
                &size_set_itoip1,
                0);
    i_index_r = 0;
    if (!BZLA_EMPTY_STACK(ranges))
    {
      assert(BZLA_COUNT_STACK(ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BZLA_COUNT_STACK(ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BZLA_PEEK_STACK(ranges, i_range);
        upper = BZLA_PEEK_STACK(ranges, i_range + 1);
        assert(i_inc < BZLA_COUNT_STACK(increments));
        inc           = BZLA_PEEK_STACK(increments, i_inc);
        tmp           = create_pattern_itoip1(bzla, lower, upper, subst, inc);
        tmp->is_array = 1;
        bzla_node_release(bzla, subst);
        subst = tmp;
        bzla_bv_free(mm, inc);

        assert(i_index_r < BZLA_COUNT_STACK(indices_ranges));
        static_rho = create_static_rho(
            bzla, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (bzla_node_lambda_get_static_rho(subst))
          bzla_node_lambda_delete_static_rho(bzla, subst);
        bzla_node_lambda_set_static_rho(subst, static_rho);
      }
    }

    /* pattern: memcopy */
    BZLA_RESET_STACK(ranges);
    BZLA_RESET_STACK(indices_ranges);
    BZLA_RESET_STACK(increments);
    find_ranges(bzla,
                &indices_cpy,
                &ranges,
                &increments,
                &indices_rem,
                &indices_ranges,
                &num_cpy,
                0,
                &size_cpy,
                0);
    i_index_r = 0;
    if (!BZLA_EMPTY_STACK(ranges))
    {
      assert(base == subst);
      assert(BZLA_COUNT_STACK(ranges) % 2 == 0);
      for (i_range = 0, i_inc = 0; i_range < BZLA_COUNT_STACK(ranges) - 1;
           i_range += 2, i_inc++)
      {
        lower = BZLA_PEEK_STACK(ranges, i_range);
        upper = BZLA_PEEK_STACK(ranges, i_range + 1);
        assert(i_inc < BZLA_COUNT_STACK(increments));
        inc   = BZLA_PEEK_STACK(increments, i_inc);
        b     = bzla_hashptr_table_get(index_value_map, lower);
        value = b->data.as_ptr;
        extract_cpy_src_dst_info(
            lower, value, &src_array, &src_addr, &dst_addr, 0);
        /* 'subst' == destination array */
        tmp = create_pattern_cpy(
            bzla, lower, upper, src_array, subst, src_addr, dst_addr, inc);
        tmp->is_array = 1;
        bzla_node_release(bzla, subst);
        subst = tmp;
        bzla_bv_free(mm, inc);

        assert(i_index_r < BZLA_COUNT_STACK(indices_ranges));
        static_rho = create_static_rho(
            bzla, indices_ranges.start + i_index_r, 0, index_value_map);
        i_index_r += static_rho->count + 1;
        if (bzla_node_lambda_get_static_rho(subst))
          bzla_node_lambda_delete_static_rho(bzla, subst);
        bzla_node_lambda_set_static_rho(subst, static_rho);
      }
    }

    num_total = num_set + num_set_inc + num_set_itoi + num_set_itoip1 + num_cpy;

    /* we can skip creating writes if we did not find any pattern in a write
     * chain, and thus can leave the write chain as-is.
     * for the top equality case we always have to create writes since we
     * convert top level equalities to writes. */
    if (is_top_eq || num_total > 0)
    {
      /* no pattern found for indices in 'indices_rem'. create writes */
      for (i_index = 0; i_index < BZLA_COUNT_STACK(indices_rem); i_index++)
      {
        lower = BZLA_PEEK_STACK(indices_rem, i_index);
        b     = bzla_hashptr_table_get(index_value_map, lower);
        assert(b);
        value = b->data.as_ptr;
        tmp   = bzla_exp_write(bzla, subst, lower, value);
        bzla_node_release(bzla, subst);
        subst = tmp;
        num_writes++;
      }
    }

    assert((is_top_eq || num_total > 0) || base == subst);
    if (base != subst) bzla_insert_substitution(bzla, array, subst, false);

    bzla_iter_hashptr_init(&iit, t);
    while (bzla_iter_hashptr_has_next(&iit))
    {
      stack = iit.bucket->data.as_ptr;
      (void) bzla_iter_hashptr_next(&iit);
      BZLA_RELEASE_STACK(*stack);
      BZLA_DELETE(mm, stack);
    }
    bzla_node_release(bzla, subst);

    bzla_hashptr_table_delete(index_value_map);
    bzla_hashptr_table_delete(t);
    BZLA_RESET_STACK(ranges);
    BZLA_RESET_STACK(indices);
    BZLA_RESET_STACK(indices_ranges);
    BZLA_RESET_STACK(values);
    BZLA_RESET_STACK(increments);
    BZLA_RESET_STACK(indices_itoi);
    BZLA_RESET_STACK(indices_itoip1);
    BZLA_RESET_STACK(indices_cpy);
    BZLA_RESET_STACK(indices_rem);
  }
  BZLA_RELEASE_STACK(ranges);
  BZLA_RELEASE_STACK(indices);
  BZLA_RELEASE_STACK(indices_ranges);
  BZLA_RELEASE_STACK(values);
  BZLA_RELEASE_STACK(increments);
  BZLA_RELEASE_STACK(indices_itoi);
  BZLA_RELEASE_STACK(indices_itoip1);
  BZLA_RELEASE_STACK(indices_cpy);
  BZLA_RELEASE_STACK(indices_rem);

  BZLA_MSG(bzla->msg,
           1,
           "set: %u (%u), "
           "set_inc: %u (%u), "
           "set_itoi: %u (%u), "
           "set_itoip1: %u (%u), "
           "cpy: %u (%u)",
           num_set,
           size_set,
           num_set_inc,
           size_set_inc,
           num_set_itoi,
           size_set_itoi,
           num_set_itoip1,
           size_set_itoip1,
           num_cpy,
           size_cpy);
  return num_total;
}

/* NOTE: Macro extraction may introduce extensional lambdas, which can not be
 * handled right now. If that happens Bitwuzla aborts with an error message
 * about extensional lambdas. However, this is not a problem since we would
 * abort anyways since we only support pure quantified BV right now. */
static void
extract_macros(Bzla *bzla)
{
  double start;
  BzlaPtrHashTableIterator it;
  BzlaNode *cur, *eq, *app, *var, *lambda, *param;
  BzlaNode *body, *fun_body, *lambda_body;
  uint32_t num_extracted = 0;

  if (bzla->quantifiers->count == 0) return;

  start = bzla_util_time_stamp();
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);

    if (bzla_node_is_inverted(cur) || !bzla_node_is_forall(cur)) continue;

    body = cur->e[1];
    if (bzla_node_is_inverted(body) || !bzla_node_is_bv_eq(body)) continue;

    if (bzla_node_is_apply(body->e[0]))
    {
      app      = body->e[0];
      fun_body = body->e[1];
    }
    else if (bzla_node_is_apply(body->e[1]))
    {
      app      = body->e[1];
      fun_body = body->e[0];
    }
    else
      continue;

    if (bzla_node_is_inverted(app))
    {
      app      = bzla_node_invert(app);
      fun_body = bzla_node_invert(fun_body);
    }

    if (bzla_node_is_lambda(app->e[0])) continue;
    assert(bzla_node_is_uf(app->e[0]));

    if (bzla_sort_fun_get_arity(bzla, app->e[0]->sort_id) != 1) continue;

    var = app->e[1]->e[0];

    if (!bzla_node_param_is_forall_var(var) || var != cur->e[0]) continue;

    num_extracted++;
    param       = bzla_exp_param(bzla, var->sort_id, 0);
    lambda_body = bzla_substitute_node(bzla, fun_body, var, param);
    lambda      = bzla_exp_lambda(bzla, param, lambda_body);
    assert(!lambda->parameterized);
    lambda->is_array = app->e[0]->is_array;
    eq               = bzla_exp_eq(bzla, app->e[0], lambda);
    bzla_assert_exp(bzla, eq);
    bzla_node_release(bzla, eq);
    bzla_node_release(bzla, param);
    bzla_node_release(bzla, lambda_body);
    bzla_node_release(bzla, lambda);
    bzla_hashptr_table_remove(bzla->unsynthesized_constraints, cur, 0, 0);
    bzla_node_release(bzla, cur);
  }
  BZLA_MSG(bzla->msg,
           1,
           "extracted %u macros in %.3f seconds",
           num_extracted,
           bzla_util_time_stamp() - start);
}

void
bzla_extract_lambdas(Bzla *bzla)
{
  assert(bzla);

  uint32_t num_lambdas;
  double start, delta;
  BzlaPtrHashTable *map_value_index, *map_lambda_base;
  BzlaMemMgr *mm;

  if (bzla->lambdas->count == 0 && bzla->ufs->count == 0) return;

  start = bzla_util_time_stamp();

  mm = bzla->mm;
  /* maps for each array values to stacks of indices */
  map_value_index =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  /* contains the base array for each write chain */
  map_lambda_base =
      bzla_hashptr_table_new(mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla_init_substitutions(bzla);

  /* collect lambdas that are at the top of lambda chains */
  collect_indices_lambdas(bzla, map_value_index, map_lambda_base);
  collect_indices_updates(bzla, map_value_index, map_lambda_base);
  /* top level equality pre-initialization */
  collect_indices_top_eqs(bzla, map_value_index);
  num_lambdas = extract_lambdas(bzla, map_value_index, map_lambda_base);
  bzla_hashptr_table_delete(map_lambda_base);
  bzla_hashptr_table_delete(map_value_index);

  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);
  delta = bzla_util_time_stamp() - start;
  BZLA_MSG(
      bzla->msg, 1, "extracted %u lambdas in %.3f seconds", num_lambdas, delta);
  bzla->time.extract += delta;

  extract_macros(bzla);
}
