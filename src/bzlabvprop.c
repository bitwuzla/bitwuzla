/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

/*
 * Bit-vector operator propagators based on [1] and [2].
 *
 * [1] Wenxi Wang, Harald SøndergaardPeter J. Stuckey:
 *   A Bit-Vector Solver with Word-Level Propagation
 *
 * [2] L. Michel, P. Van Hentenryck:
 *   Constraint Satisfaction over Bit-Vectors
 */

#include "bzlabvprop.h"

#include <stdio.h>

#include "utils/bzlautil.h"

/* -------------------------------------------------------------------------- */

BZLA_DECLARE_STACK(BzlaBvDomainPtr, BzlaBvDomain *);

/* -------------------------------------------------------------------------- */

#ifndef NDEBUG
static bool
compare_fixed_domain(BzlaMemMgr *mm, BzlaBvDomain *a, BzlaBvDomain *b)
{
  assert(bzla_bvdomain_is_fixed(mm, a));
  assert(bzla_bvdomain_is_fixed(mm, b));
  return bzla_bvdomain_is_equal(a, b);
}
#define BVPROP_LOG_LEVEL 0
#define BVPROP_LOG(FMT, ...)    \
  if (BVPROP_LOG_LEVEL > 0)     \
  {                             \
    printf(FMT, ##__VA_ARGS__); \
  }
#define BVPROP_LOG_DOMAIN(mm, domain)      \
  if (BVPROP_LOG_LEVEL > 0)                \
  {                                        \
    printf(#domain ": ");                  \
    bzla_bvdomain_print(mm, domain, true); \
  }
#else
#define BVPROP_LOG(FMT, ...)
#define BVPROP_LOG_DOMAIN(mm, domain)
#endif

/* -------------------------------------------------------------------------- */

static BzlaBvDomain *
new_domain(BzlaMemMgr *mm)
{
  BzlaBvDomain *res;
  BZLA_CNEW(mm, res);
  return res;
}

static BzlaBvDomain *
new_invalid_domain(BzlaMemMgr *mm, uint32_t width)
{
  BzlaBvDomain *res;
  BZLA_CNEW(mm, res);
  res->lo = bzla_bv_ones(mm, width);
  res->hi = bzla_bv_zero(mm, width);
  return res;
}

/* -------------------------------------------------------------------------- */

static bool
made_progress(BzlaBvDomain *d_x,
              BzlaBvDomain *d_y,
              BzlaBvDomain *d_z,
              BzlaBvDomain *d_c,
              BzlaBvDomain *res_d_x,
              BzlaBvDomain *res_d_y,
              BzlaBvDomain *res_d_z,
              BzlaBvDomain *res_d_c)
{
  assert(d_x);
  assert(d_z);
  assert(res_d_x);
  assert(res_d_z);
  assert(!d_y || res_d_y);

  if (bzla_bv_compare(d_x->lo, res_d_x->lo)
      || bzla_bv_compare(d_x->hi, res_d_x->hi)
      || (d_y && bzla_bv_compare(d_y->lo, res_d_y->lo))
      || (d_y && bzla_bv_compare(d_y->hi, res_d_y->hi))
      || bzla_bv_compare(d_z->lo, res_d_z->lo)
      || bzla_bv_compare(d_z->hi, res_d_z->hi)
      || (d_c && bzla_bv_compare(d_c->lo, res_d_c->lo))
      || (d_c && bzla_bv_compare(d_c->hi, res_d_c->hi)))
  {
    return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

typedef bool (*BVPropFunUnary)(BzlaMemMgr *,
                               BzlaBvDomain *,
                               BzlaBvDomain *,
                               BzlaBvDomain **,
                               BzlaBvDomain **);

typedef bool (*BVPropFunBinary)(BzlaMemMgr *,
                                BzlaBvDomain *,
                                BzlaBvDomain *,
                                BzlaBvDomain *,
                                BzlaBvDomain **,
                                BzlaBvDomain **,
                                BzlaBvDomain **);

typedef bool (*BVPropFunBinaryAux)(BzlaMemMgr *,
                                   BzlaBvDomain *,
                                   BzlaBvDomain *,
                                   BzlaBvDomain *,
                                   BzlaBvDomain **,
                                   BzlaBvDomain **,
                                   BzlaBvDomain **,
                                   bool);

typedef bool (*BVPropFunTernary)(BzlaMemMgr *,
                                 BzlaBvDomain *,
                                 BzlaBvDomain *,
                                 BzlaBvDomain *,
                                 BzlaBvDomain *,
                                 BzlaBvDomain **,
                                 BzlaBvDomain **,
                                 BzlaBvDomain **,
                                 BzlaBvDomain **);

typedef bool (*BVPropFunTernaryAux)(BzlaMemMgr *,
                                    BzlaBvDomain *,
                                    BzlaBvDomain *,
                                    BzlaBvDomain *,
                                    BzlaBvDomain *,
                                    BzlaBvDomain **,
                                    BzlaBvDomain **,
                                    BzlaBvDomain **,
                                    BzlaBvDomain **,
                                    bool);

typedef bool (*BVPropFunShiftConst)(BzlaMemMgr *,
                                    BzlaBvDomain *,
                                    BzlaBvDomain *,
                                    BzlaBitVector *,
                                    BzlaBvDomain **,
                                    BzlaBvDomain **);

typedef bool (*BVPropFunSlice)(BzlaMemMgr *,
                               BzlaBvDomain *,
                               BzlaBvDomain *,
                               uint32_t,
                               uint32_t,
                               BzlaBvDomain **,
                               BzlaBvDomain **);

/* -------------------------------------------------------------------------- */

static bool
decomp_step(BzlaMemMgr *mm,
            BzlaBvDomain **tmp_x,
            BzlaBvDomain **tmp_y,
            BzlaBvDomain **tmp_z,
            BzlaBvDomain **tmp_c,
            BzlaBitVector *n,
            uint32_t hi,
            uint32_t lo,
            bool no_overflows,
            BzlaBvDomain **res_d_x,
            BzlaBvDomain **res_d_y,
            BzlaBvDomain **res_d_z,
            BzlaBvDomain **res_d_c,
            BVPropFunUnary fun1,
            BVPropFunBinary fun2,
            BVPropFunBinaryAux fun2_aux,
            BVPropFunTernary fun3,
            BVPropFunTernaryAux fun3_aux,
            BVPropFunShiftConst fun_shift,
            BVPropFunSlice fun_slice,
            bool *progress)
{
  assert(tmp_x);
  assert(tmp_z);
  assert(res_d_x);
  assert(res_d_z);
  assert(!tmp_y || res_d_y);
  assert(!tmp_c || res_d_c);
  assert((fun1 && !fun2 && !fun2_aux && !fun3 && !fun3_aux && !fun_shift
          && !fun_slice)
         || (!fun1 && fun2 && !fun2_aux && !fun3 && !fun3_aux && !fun_shift
             && !fun_slice)
         || (!fun1 && !fun2 && fun2_aux && !fun3 && !fun3_aux && !fun_shift
             && !fun_slice)
         || (!fun1 && !fun2 && !fun2_aux && fun3 && !fun3_aux && !fun_shift
             && !fun_slice)
         || (!fun1 && !fun2 && !fun2_aux && !fun3 && fun3_aux && !fun_shift
             && !fun_slice)
         || (!fun1 && !fun2 && !fun2_aux && !fun3 && !fun3_aux && fun_shift
             && !fun_slice)
         || (!fun1 && !fun2 && !fun2_aux && !fun3 && !fun3_aux && !fun_shift
             && fun_slice));
  assert(!fun3 || tmp_c);
  assert(!fun_shift || (n && !tmp_y && !res_d_y && !tmp_c && !res_d_c));
  assert(progress);

  if ((fun1 && !fun1(mm, *tmp_x, *tmp_z, res_d_x, res_d_z))
      || (fun2 && !fun2(mm, *tmp_x, *tmp_y, *tmp_z, res_d_x, res_d_y, res_d_z))
      || (fun2_aux
          && !fun2_aux(mm,
                       *tmp_x,
                       *tmp_y,
                       *tmp_z,
                       res_d_x,
                       res_d_y,
                       res_d_z,
                       no_overflows))
      || (fun3
          && !fun3(mm,
                   *tmp_x,
                   *tmp_y,
                   *tmp_z,
                   *tmp_c,
                   res_d_x,
                   res_d_y,
                   res_d_z,
                   res_d_c))
      || (fun3_aux
          && !fun3_aux(mm,
                       *tmp_x,
                       *tmp_y,
                       *tmp_z,
                       tmp_c ? *tmp_c : 0,
                       res_d_x,
                       res_d_y,
                       res_d_z,
                       res_d_c,
                       no_overflows))
      || (fun_shift && !fun_shift(mm, *tmp_x, *tmp_z, n, res_d_x, res_d_z))
      || (fun_slice
          && !fun_slice(mm, *tmp_x, *tmp_z, hi, lo, res_d_x, res_d_z)))
  {
    bzla_bvdomain_free(mm, *res_d_x);
    if (res_d_y) bzla_bvdomain_free(mm, *res_d_y);
    bzla_bvdomain_free(mm, *res_d_z);
    if (res_d_c) bzla_bvdomain_free(mm, *res_d_c);
    return false;
  }
  assert(bzla_bvdomain_is_valid(mm, *res_d_x));
  assert(!res_d_y || bzla_bvdomain_is_valid(mm, *res_d_y));
  assert(bzla_bvdomain_is_valid(mm, *res_d_z));
  assert(!res_d_c || bzla_bvdomain_is_valid(mm, *res_d_c));
  if (!(*progress))
  {
    *progress = made_progress(*tmp_x,
                              tmp_y ? *tmp_y : 0,
                              *tmp_z,
                              tmp_c ? *tmp_c : 0,
                              *res_d_x,
                              res_d_y ? *res_d_y : 0,
                              *res_d_z,
                              res_d_c ? *res_d_c : 0);
  }
  bzla_bvdomain_free(mm, *tmp_x);
  *tmp_x = *res_d_x;
  if (tmp_y)
  {
    bzla_bvdomain_free(mm, *tmp_y);
    *tmp_y = *res_d_y;
  }
  bzla_bvdomain_free(mm, *tmp_z);
  *tmp_z = *res_d_z;
  if (tmp_c)
  {
    bzla_bvdomain_free(mm, *tmp_c);
    *tmp_c = *res_d_c;
  }
  return true;
}

static bool
decomp_step_unary(BzlaMemMgr *mm,
                  BzlaBvDomain **tmp_x,
                  BzlaBvDomain **tmp_z,
                  BzlaBvDomain **res_d_x,
                  BzlaBvDomain **res_d_z,
                  BVPropFunUnary fun1,
                  bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     0,
                     tmp_z,
                     0,
                     0,
                     0,
                     0,
                     false,
                     res_d_x,
                     0,
                     res_d_z,
                     0,
                     fun1,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     progress);
}

static bool
decomp_step_binary(BzlaMemMgr *mm,
                   BzlaBvDomain **tmp_x,
                   BzlaBvDomain **tmp_y,
                   BzlaBvDomain **tmp_z,
                   BzlaBvDomain **res_d_x,
                   BzlaBvDomain **res_d_y,
                   BzlaBvDomain **res_d_z,
                   BVPropFunBinary fun2,
                   bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     tmp_y,
                     tmp_z,
                     0,
                     0,
                     0,
                     0,
                     false,
                     res_d_x,
                     res_d_y,
                     res_d_z,
                     0,
                     0,
                     fun2,
                     0,
                     0,
                     0,
                     0,
                     0,
                     progress);
}

static bool
decomp_step_binary_aux(BzlaMemMgr *mm,
                       BzlaBvDomain **tmp_x,
                       BzlaBvDomain **tmp_y,
                       BzlaBvDomain **tmp_z,
                       BzlaBvDomain **res_d_x,
                       BzlaBvDomain **res_d_y,
                       BzlaBvDomain **res_d_z,
                       bool no_overflows,
                       BVPropFunBinaryAux fun2_aux,
                       bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     tmp_y,
                     tmp_z,
                     0,
                     0,
                     0,
                     0,
                     no_overflows,
                     res_d_x,
                     res_d_y,
                     res_d_z,
                     0,
                     0,
                     0,
                     fun2_aux,
                     0,
                     0,
                     0,
                     0,
                     progress);
}

static bool
decomp_step_ternary(BzlaMemMgr *mm,
                    BzlaBvDomain **tmp_x,
                    BzlaBvDomain **tmp_y,
                    BzlaBvDomain **tmp_z,
                    BzlaBvDomain **tmp_c,
                    BzlaBvDomain **res_d_x,
                    BzlaBvDomain **res_d_y,
                    BzlaBvDomain **res_d_z,
                    BzlaBvDomain **res_d_c,
                    BVPropFunTernary fun3,
                    bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     tmp_y,
                     tmp_z,
                     tmp_c,
                     0,
                     0,
                     0,
                     false,
                     res_d_x,
                     res_d_y,
                     res_d_z,
                     res_d_c,
                     0,
                     0,
                     0,
                     fun3,
                     0,
                     0,
                     0,
                     progress);
}

static bool
decomp_step_ternary_aux(BzlaMemMgr *mm,
                        BzlaBvDomain **tmp_x,
                        BzlaBvDomain **tmp_y,
                        BzlaBvDomain **tmp_z,
                        BzlaBvDomain **tmp_c,
                        BzlaBvDomain **res_d_x,
                        BzlaBvDomain **res_d_y,
                        BzlaBvDomain **res_d_z,
                        BzlaBvDomain **res_d_c,
                        bool no_overflows,
                        BVPropFunTernaryAux fun3_aux,
                        bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     tmp_y,
                     tmp_z,
                     tmp_c,
                     0,
                     0,
                     0,
                     no_overflows,
                     res_d_x,
                     res_d_y,
                     res_d_z,
                     res_d_c,
                     0,
                     0,
                     0,
                     0,
                     fun3_aux,
                     0,
                     0,
                     progress);
}

static bool
decomp_step_shiftc(BzlaMemMgr *mm,
                   BzlaBvDomain **tmp_x,
                   BzlaBvDomain **tmp_z,
                   BzlaBitVector *n,
                   BzlaBvDomain **res_d_x,
                   BzlaBvDomain **res_d_z,
                   BVPropFunShiftConst fun_shift,
                   bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     0,
                     tmp_z,
                     0,
                     n,
                     0,
                     0,
                     false,
                     res_d_x,
                     0,
                     res_d_z,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     fun_shift,
                     0,
                     progress);
}

static bool
decomp_step_slice(BzlaMemMgr *mm,
                  BzlaBvDomain **tmp_x,
                  BzlaBvDomain **tmp_z,
                  uint32_t hi,
                  uint32_t lo,
                  BzlaBvDomain **res_d_x,
                  BzlaBvDomain **res_d_z,
                  BVPropFunSlice fun_slice,
                  bool *progress)
{
  return decomp_step(mm,
                     tmp_x,
                     0,
                     tmp_z,
                     0,
                     0,
                     hi,
                     lo,
                     false,
                     res_d_x,
                     0,
                     res_d_z,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     0,
                     fun_slice,
                     progress);
}

/* -------------------------------------------------------------------------- */

bool
bzla_bvprop_eq(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain *d_z,
               BzlaBvDomain **res_d_x,
               BzlaBvDomain **res_d_y,
               BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(bzla_bvdomain_get_width(d_x) == bzla_bvdomain_get_width(d_y));
  assert(bzla_bvdomain_get_width(d_z) == 1);

  bool valid = true;
  BzlaBvDomain *tmp;
  BzlaBitVector *sext_lo_z, *not_hi_y, *not_hi_x;
  BzlaBitVector *lo_z_and_lo_y, *lo_z_and_hi_y, *not_and;
  BzlaBitVector *hi_x, *lo_x, *hi_y, *lo_y, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_y = d_y->hi;
  lo_y = d_y->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  sext_lo_z = bzla_bv_sext(mm, lo_z, bzla_bvdomain_get_width(d_x) - 1);
  not_hi_y  = bzla_bv_not(mm, hi_y);
  not_hi_x  = bzla_bv_not(mm, hi_x);

  tmp = new_domain(mm);

  /* lo_x' = lo_x | (sext(lo_z,n) & lo_y) */
  lo_z_and_lo_y = bzla_bv_and(mm, sext_lo_z, lo_y);
  tmp->lo       = bzla_bv_or(mm, lo_x, lo_z_and_lo_y);

  /* hi_x' = hi_x & ~(sext(hi_z,n) & ~hi_y) */
  lo_z_and_hi_y = bzla_bv_and(mm, sext_lo_z, not_hi_y);
  not_and       = bzla_bv_not(mm, lo_z_and_hi_y);
  tmp->hi       = bzla_bv_and(mm, hi_x, not_and);

  bzla_bv_free(mm, lo_z_and_lo_y);
  bzla_bv_free(mm, lo_z_and_hi_y);
  bzla_bv_free(mm, not_and);

  valid = valid & bzla_bvdomain_is_valid(mm, tmp);
  if (res_d_x)
  {
    *res_d_x = tmp;
  }
  else
  {
    bzla_bvdomain_free(mm, tmp);
  }

  if (valid)
  {
    BzlaBitVector *lo_z_and_lo_x, *lo_z_and_hi_x;
    tmp = new_domain(mm);

    /* lo_y' = lo_y | (sext(lo_z,n) & lo_x) */
    lo_z_and_lo_x = bzla_bv_and(mm, sext_lo_z, lo_x);
    tmp->lo       = bzla_bv_or(mm, lo_y, lo_z_and_lo_x);

    /* hi_y' = hi_y & ~(sext(hi_z,n) & ~hi_x) */
    lo_z_and_hi_x = bzla_bv_and(mm, sext_lo_z, not_hi_x);
    not_and       = bzla_bv_not(mm, lo_z_and_hi_x);
    tmp->hi       = bzla_bv_and(mm, hi_y, not_and);

    bzla_bv_free(mm, lo_z_and_lo_x);
    bzla_bv_free(mm, lo_z_and_hi_x);
    bzla_bv_free(mm, not_and);

    valid = valid & bzla_bvdomain_is_valid(mm, tmp);
  }
  else
  {
    tmp = bzla_bvdomain_new(mm, lo_y, hi_y);
  }
  if (res_d_y)
  {
    *res_d_y = tmp;
  }
  else
  {
    bzla_bvdomain_free(mm, tmp);
  }

  if (valid)
  {
    BzlaBitVector *lo_x_and_lo_y, *hi_x_and_hi_y, * or, *red;
    BzlaBitVector *lo_x_and_hi_y, *hi_x_and_lo_y, *not_red;
    tmp = new_domain(mm);

    /* lo_z' = lo_z | redand((lo_x & lo_y) | (~hi_x & ~hi_y)) */
    lo_x_and_lo_y = bzla_bv_and(mm, lo_x, lo_y);
    hi_x_and_hi_y = bzla_bv_and(mm, not_hi_x, not_hi_y);
    or            = bzla_bv_or(mm, lo_x_and_lo_y, hi_x_and_hi_y);
    red           = bzla_bv_redand(mm, or);
    tmp->lo       = bzla_bv_or(mm, lo_z, red);

    bzla_bv_free(mm, lo_x_and_lo_y);
    bzla_bv_free(mm, hi_x_and_hi_y);
    bzla_bv_free(mm, or);
    bzla_bv_free(mm, red);

    /* hi_z' = hi_z & ~redor((lo_x & ~hi_y) | (~hi_x & lo_y)) */
    lo_x_and_hi_y = bzla_bv_and(mm, lo_x, not_hi_y);
    hi_x_and_lo_y = bzla_bv_and(mm, not_hi_x, lo_y);
    or            = bzla_bv_or(mm, lo_x_and_hi_y, hi_x_and_lo_y);
    red           = bzla_bv_redor(mm, or);
    not_red       = bzla_bv_not(mm, red);
    tmp->hi       = bzla_bv_and(mm, hi_z, not_red);

    bzla_bv_free(mm, lo_x_and_hi_y);
    bzla_bv_free(mm, hi_x_and_lo_y);
    bzla_bv_free(mm, or);
    bzla_bv_free(mm, red);
    bzla_bv_free(mm, not_red);

    valid = valid & bzla_bvdomain_is_valid(mm, tmp);
  }
  else
  {
    tmp = bzla_bvdomain_new(mm, lo_z, hi_z);
  }
  if (res_d_z)
  {
    *res_d_z = tmp;
  }
  else
  {
    bzla_bvdomain_free(mm, tmp);
  }

  bzla_bv_free(mm, sext_lo_z);
  bzla_bv_free(mm, not_hi_x);
  bzla_bv_free(mm, not_hi_y);

  return valid;
}

bool
bzla_bvprop_not(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));

  BzlaBitVector *not_hi, *not_lo;
  BzlaBitVector *hi_x, *lo_x, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  /**
   * lo_x' = lo_x | ~hi_z
   * hi_x' = hi_x & ~hi_z
   */
  not_hi         = bzla_bv_not(mm, hi_z);
  not_lo         = bzla_bv_not(mm, lo_z);
  *res_d_x       = new_domain(mm);
  (*res_d_x)->lo = bzla_bv_or(mm, lo_x, not_hi);
  (*res_d_x)->hi = bzla_bv_and(mm, hi_x, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);

  /**
   * lo_z' = lo_z | ~hi_x
   * hi_z' = hi_z & ~hi_x
   */
  not_hi         = bzla_bv_not(mm, hi_x);
  not_lo         = bzla_bv_not(mm, lo_x);
  *res_d_z       = new_domain(mm);
  (*res_d_z)->lo = bzla_bv_or(mm, lo_z, not_hi);
  (*res_d_z)->hi = bzla_bv_and(mm, hi_z, not_lo);
  bzla_bv_free(mm, not_hi);
  bzla_bv_free(mm, not_lo);

  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

static bool
bvprop_shift_const_aux(BzlaMemMgr *mm,
                       BzlaBvDomain *d_x,
                       BzlaBvDomain *d_z,
                       BzlaBitVector *n,
                       BzlaBvDomain **res_d_x,
                       BzlaBvDomain **res_d_z,
                       bool is_srl)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(n);
  assert(bzla_bvdomain_get_width(d_x) == bzla_bv_get_width(n));
  assert(res_d_x);
  assert(res_d_z);

  uint32_t w, wn;
  BzlaBitVector *mask1, *ones_wn, *zero_wn, *ones_w_wn, *zero_w_wn;
  BzlaBitVector *tmp0, *tmp1;
  BzlaBitVector *hi_x, *lo_x, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  w = bzla_bvdomain_get_width(d_z);
  assert(w == bzla_bvdomain_get_width(d_x));
#ifndef NDEBUG
  BzlaBitVector *uint32maxbv = bzla_bv_ones(mm, 32);
  assert(bzla_bv_compare(n, uint32maxbv) <= 0);
  bzla_bv_free(mm, uint32maxbv);
#endif
  wn = (uint32_t) bzla_bv_to_uint64(n);

  /**
   * SLL: mask1 = 1_[wn]   :: 0_[w-wn]
   * SRL: mask1 = 0_[w-wn] :: 1_[wn]
   */
  if (wn == 0)
  {
    mask1 = bzla_bv_zero(mm, w);
  }
  else if (wn >= w)
  {
    mask1 = bzla_bv_ones(mm, w);
  }
  else
  {
    zero_wn   = bzla_bv_zero(mm, wn);
    zero_w_wn = bzla_bv_zero(mm, w - wn);
    ones_wn   = bzla_bv_ones(mm, wn);
    ones_w_wn = bzla_bv_ones(mm, w - wn);

    mask1 = is_srl ? bzla_bv_concat(mm, zero_w_wn, ones_wn)
                   : bzla_bv_concat(mm, ones_wn, zero_w_wn);
    bzla_bv_free(mm, zero_wn);
    bzla_bv_free(mm, zero_w_wn);
    bzla_bv_free(mm, ones_wn);
    bzla_bv_free(mm, ones_w_wn);
  }

  *res_d_x = new_domain(mm);
  *res_d_z = new_domain(mm);

  /**
   * SLL: lo_x' = lo_x | (lo_z >> n)
   * SRL: lo_x' = lo_x | (lo_z << n)
   */
  tmp0           = is_srl ? bzla_bv_sll(mm, lo_z, n) : bzla_bv_srl(mm, lo_z, n);
  (*res_d_x)->lo = bzla_bv_or(mm, lo_x, tmp0);
  bzla_bv_free(mm, tmp0);

  /**
   * SLL: hi_x' = ((hi_z >> n) | mask1) & hi_x
   * SRL: hi_x' = ((hi_z << n) | mask1) & hi_x
   */
  tmp0           = is_srl ? bzla_bv_sll(mm, hi_z, n) : bzla_bv_srl(mm, hi_z, n);
  tmp1           = bzla_bv_or(mm, tmp0, mask1);
  (*res_d_x)->hi = bzla_bv_and(mm, tmp1, hi_x);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /**
   * SLL: lo_z' = ((low_x << n) | lo_z)
   * SRL: lo_z' = ((low_x >> n) | lo_z)
   *
   * Note: Propagator in [1] is incorrect!
   * (was:
   *   SLL: lo_z' = ((low_x << n) | lo_z) & mask2
   *   SRL: lo_z' = ((low_x >> n) | lo_z) & mask2
   *  with:
   *   SLL: mask2 = 1_[w-wn] :: 0_[wn]
   *   SRL: mask2 = 0_[wn]   :: 1_[w-wn]
   *  )
   */
  tmp0           = is_srl ? bzla_bv_srl(mm, lo_x, n) : bzla_bv_sll(mm, lo_x, n);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, lo_z);
  bzla_bv_free(mm, tmp0);

  /**
   * SLL: hi_z' = (hi_x << n) & hi_z
   * SRL: hi_z' = (hi_x >> n) & hi_z
   */
  tmp0           = is_srl ? bzla_bv_srl(mm, hi_x, n) : bzla_bv_sll(mm, hi_x, n);
  (*res_d_z)->hi = bzla_bv_and(mm, tmp0, hi_z);
  bzla_bv_free(mm, tmp0);

  bzla_bv_free(mm, mask1);

  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_sll_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  return bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, false);
}

bool
bzla_bvprop_srl_const(BzlaMemMgr *mm,
                      BzlaBvDomain *d_x,
                      BzlaBvDomain *d_z,
                      BzlaBitVector *n,
                      BzlaBvDomain **res_d_x,
                      BzlaBvDomain **res_d_z)
{
  return bvprop_shift_const_aux(mm, d_x, d_z, n, res_d_x, res_d_z, true);
}

static bool
bvprop_shift_aux(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_y,
                 BzlaBvDomain **res_d_z,
                 bool is_srl)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(bzla_bvdomain_get_width(d_x) == bzla_bvdomain_get_width(d_y));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  /* z_[bw] = x_[bw] << y_[bw]
   *
   * SLL:
   *   prev_z = x
   *   for i = 0 to bw - 1:
   *     shift = 1 << i
   *     cur_z = ite (y[i:i], prev_z << (1 << i), prev_z)
   *     prev_z = cur_z
   *   z = ite (y[MSB:MSB], prev_z << (1 << log2_bw - 1), prev_z)
   *
   * SRL:
   *   prev_z = x
   *   for i = 0 to bw - 1:
   *     shift = 1 << i
   *     cur_z = ite (y[i:i], prev_z >> (1 >> i), prev_z)
   *     prev_z = cur_z
   *   z = ite (y[MSB:MSB], prev_z >> (1 >> log2_bw - 1), prev_z)
   */

  uint32_t i, n, bw;
  bool res, progress;
  BzlaBitVector *bv;
  BzlaBvDomain *d, *tmp_x, *tmp_x_bit, *tmp_y, *tmp_z;
  BzlaBvDomain *tmp_eq_z, *tmp_eq_x_bit, *tmp_zero, *tmp_zero_bw, *tmp_one;
#ifndef NDEBUG
  BzlaBvDomain *d_zero, *d_zero_bw, *d_one;
#endif
  BzlaBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack;
  BzlaBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp_z_prev;
  BzlaBvDomain *tmp_res_c;
  BzlaBitVectorPtrStack shift_stack;

  res = true;

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_z));

  BZLA_INIT_STACK(mm, d_c_stack);
  BZLA_INIT_STACK(mm, d_shift_stack);
  BZLA_INIT_STACK(mm, d_ite_stack);
  BZLA_INIT_STACK(mm, shift_stack);

  for (i = 0; i < bw; i++)
  {
    /* slice y into bw ite conditions */
    d     = new_domain(mm);
    d->lo = bzla_bv_slice(mm, d_y->lo, i, i);
    d->hi = bzla_bv_slice(mm, d_y->hi, i, i);
    BZLA_PUSH_STACK(d_c_stack, d);
    /* bw shift propagators */
    d = bzla_bvdomain_new_init(mm, bw);
    BZLA_PUSH_STACK(d_shift_stack, d);
    /* bw ite propagators */
    if (i == bw - 1)
      d = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);
    else
      d = bzla_bvdomain_new_init(mm, bw);
    BZLA_PUSH_STACK(d_ite_stack, d);
    /* shift width */
    bv = bzla_bv_uint64_to_bv(mm, 1u << i, bw);
    BZLA_PUSH_STACK(shift_stack, bv);
  }

  assert(BZLA_COUNT_STACK(d_c_stack) == bw);
  assert(BZLA_COUNT_STACK(d_shift_stack) == bw);
  assert(BZLA_COUNT_STACK(d_ite_stack) == bw);
  assert(BZLA_COUNT_STACK(shift_stack) == bw);

  tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);

  tmp_x_bit     = new_domain(mm);
  tmp_x_bit->lo = bzla_bv_uint64_to_bv(
      mm, bzla_bv_get_bit(d_x->lo, is_srl ? bw - 1 : 0), 1);
  tmp_x_bit->hi = bzla_bv_uint64_to_bv(
      mm, bzla_bv_get_bit(d_x->hi, is_srl ? bw - 1 : 0), 1);

  tmp_eq_z     = bzla_bvdomain_new_init(mm, 1);
  tmp_eq_x_bit = bzla_bvdomain_new_init(mm, 1);

  tmp_zero        = new_domain(mm);
  tmp_zero->lo    = bzla_bv_zero(mm, 1);
  tmp_zero->hi    = bzla_bv_zero(mm, 1);
  tmp_zero_bw     = new_domain(mm);
  tmp_zero_bw->lo = bzla_bv_zero(mm, bw);
  tmp_zero_bw->hi = bzla_bv_zero(mm, bw);
  tmp_one         = new_domain(mm);
  tmp_one->lo     = bzla_bv_one(mm, 1);
  tmp_one->hi     = bzla_bv_one(mm, 1);
#ifndef NDEBUG
  d_zero        = new_domain(mm);
  d_zero->lo    = bzla_bv_zero(mm, 1);
  d_zero->hi    = bzla_bv_zero(mm, 1);
  d_zero_bw     = new_domain(mm);
  d_zero_bw->lo = bzla_bv_zero(mm, bw);
  d_zero_bw->hi = bzla_bv_zero(mm, bw);
  d_one         = new_domain(mm);
  d_one->lo     = bzla_bv_one(mm, 1);
  d_one->hi     = bzla_bv_one(mm, 1);
#endif

  do
  {
    progress = false;

    for (i = 0; i < bw; i++)
    {
      /**
       * SLL:
       *   prev_z = x
       *   for i = 0 to bw - 1:
       *     cur_z = ite (y[i:i], prev_z << shift, prev_z)
       *     prev_z = cur_z
       *
       * SRL:
       *   prev_z = x
       *   for i = 0 to bw - 1:
       *     cur_z = ite (y[i:i], prev_z << shift, prev_z)
       *     prev_z = cur_z
       */

#if 0
      /**
       * SLL: x_bit = x[LSB:LSB]
       * SRL: x_bit = x[MSB:MSB]
       */
      if (!(res = decomp_step_slice (mm,
                                     &tmp_x,
                                     &tmp_x_bit,
                                     is_srl ? bw - 1 : 0,
                                     is_srl ? bw - 1 : 0,
                                     res_d_x,
                                     res_d_z,
                                     bzla_bvprop_slice,
                                     &progress)))
      {
        goto DONE;
      }

      /* eq_z = z == 0 */
      if (!(res = decomp_step_binary (mm,
                                      &tmp_z,
                                      &tmp_zero_bw,
                                      &tmp_eq_z,
                                      res_d_x,
                                      res_d_y,
                                      res_d_z,
                                      bzla_bvprop_eq,
                                      &progress)))
      {
        goto DONE;
      }
      assert (compare_fixed_domain (mm, tmp_zero_bw, d_zero_bw));

      /* eq_x_bit = x_bit == 1 */
      if (!(res = decomp_step_binary (mm,
                                      &tmp_x_bit,
                                      &tmp_one,
                                      &tmp_eq_x_bit,
                                      res_d_x,
                                      res_d_y,
                                      res_d_z,
                                      bzla_bvprop_eq,
                                      &progress)))
      {
        goto DONE;
      }
      assert (compare_fixed_domain (mm, tmp_one, d_one));

      /* 0 = eq_z && eq_x_bit */
      if (!(res = decomp_step_binary (mm,
                                      &tmp_eq_z,
                                      &tmp_eq_x_bit,
                                      &tmp_zero,
                                      res_d_x,
                                      res_d_y,
                                      res_d_z,
                                      bzla_bvprop_and,
                                      &progress)))
      {
        goto DONE;
      }
      assert (!bzla_bv_compare (tmp_zero->lo, d_zero->lo));
      assert (!bzla_bv_compare (tmp_zero->hi, d_zero->hi));
#endif

      assert(compare_fixed_domain(mm, tmp_zero, d_zero));

      /* shift = 1 << i */
      bv = BZLA_PEEK_STACK(shift_stack, i);

      tmp_shift  = &d_shift_stack.start[i];
      tmp_z_prev = i ? &d_ite_stack.start[i - 1] : &tmp_x;

      /**
       * SLL: prev_z << shift
       * SRL: prev_z >> shift
       */
      if (!(res = decomp_step_shiftc(
                mm,
                tmp_z_prev,
                tmp_shift,
                bv,
                res_d_x,
                res_d_z,
                is_srl ? bzla_bvprop_srl_const : bzla_bvprop_sll_const,
                &progress)))
      {
        goto DONE;
      }

      /**
       * SLL: ite (y[i:i], z << (1 << i), x)
       * SRL: ite (y[i:i], z >> (1 << i), x)
       */
      tmp_c   = &d_c_stack.start[i];
      tmp_ite = &d_ite_stack.start[i];
      if (!(res = decomp_step_ternary(mm,
                                      tmp_shift,
                                      tmp_z_prev,
                                      tmp_ite,
                                      tmp_c,
                                      res_d_x,
                                      res_d_y,
                                      res_d_z,
                                      &tmp_res_c,
                                      bzla_bvprop_cond,
                                      &progress)))
      {
        goto DONE;
      }
    }
  } while (progress);

  /* Collect y bits into the result for d_y. */
  for (i = 0; i < bw; i++)
  {
    d = BZLA_PEEK_STACK(d_c_stack, i);
    assert(bzla_bvdomain_get_width(d) == 1);
    bzla_bv_set_bit(tmp_y->lo, i, bzla_bv_get_bit(d->lo, 0));
    bzla_bv_set_bit(tmp_y->hi, i, bzla_bv_get_bit(d->hi, 0));
  }

  /* Result for d_z. */
  bzla_bvdomain_free(mm, tmp_z);
  tmp_z     = new_domain(mm);
  tmp_z->lo = bzla_bv_copy(mm, d_ite_stack.start[bw - 1]->lo);
  tmp_z->hi = bzla_bv_copy(mm, d_ite_stack.start[bw - 1]->hi);
  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(bzla_bvdomain_is_valid(mm, tmp_z));
DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  for (i = 0, n = BZLA_COUNT_STACK(d_c_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_c_stack));
    assert(!BZLA_EMPTY_STACK(d_shift_stack));
    assert(!BZLA_EMPTY_STACK(d_ite_stack));
    assert(!BZLA_EMPTY_STACK(shift_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_c_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_shift_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_ite_stack));
    bzla_bv_free(mm, BZLA_POP_STACK(shift_stack));
  }
  BZLA_RELEASE_STACK(d_c_stack);
  BZLA_RELEASE_STACK(d_shift_stack);
  BZLA_RELEASE_STACK(d_ite_stack);
  BZLA_RELEASE_STACK(shift_stack);
  bzla_bvdomain_free(mm, tmp_x_bit);
  bzla_bvdomain_free(mm, tmp_eq_z);
  bzla_bvdomain_free(mm, tmp_eq_x_bit);
  bzla_bvdomain_free(mm, tmp_zero);
  bzla_bvdomain_free(mm, tmp_zero_bw);
  bzla_bvdomain_free(mm, tmp_one);
#ifndef NDEBUG
  bzla_bvdomain_free(mm, d_zero);
  bzla_bvdomain_free(mm, d_zero_bw);
  bzla_bvdomain_free(mm, d_one);
#endif

  return res;
}

bool
bzla_bvprop_sll(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  return bvprop_shift_aux(mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
bzla_bvprop_srl(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  return bvprop_shift_aux(mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, true);
}

bool
bzla_bvprop_and(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1;
  BzlaBitVector *hi_x, *lo_x, *hi_y, *lo_y, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_y = d_y->hi;
  lo_y = d_y->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  /* lo_x' = lo_x | lo_z */
  (*res_d_x)->lo = bzla_bv_or(mm, lo_x, lo_z);

  /* hi_x' = hi_x & (hi_z | ~lo_y) */
  tmp0           = bzla_bv_not(mm, lo_y);
  tmp1           = bzla_bv_or(mm, hi_z, tmp0);
  (*res_d_x)->hi = bzla_bv_and(mm, hi_x, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* lo_y' = lo_y | lo_z */
  (*res_d_y)->lo = bzla_bv_or(mm, lo_y, lo_z);

  /* hi_y' = hi_y & (hi_z | ~lo_x) */
  tmp0           = bzla_bv_not(mm, lo_x);
  tmp1           = bzla_bv_or(mm, hi_z, tmp0);
  (*res_d_y)->hi = bzla_bv_and(mm, hi_y, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* lo_z' = lo_z | (lo_x & lo_y) */
  tmp0           = bzla_bv_and(mm, lo_x, lo_y);
  (*res_d_z)->lo = bzla_bv_or(mm, lo_z, tmp0);
  bzla_bv_free(mm, tmp0);

  /* hi_z' = hi_z & hi_x & hi_y */
  tmp0           = bzla_bv_and(mm, hi_x, hi_y);
  (*res_d_z)->hi = bzla_bv_and(mm, hi_z, tmp0);
  bzla_bv_free(mm, tmp0);

  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_y)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_or(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain *d_z,
               BzlaBvDomain **res_d_x,
               BzlaBvDomain **res_d_y,
               BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1;
  BzlaBitVector *hi_x, *lo_x, *hi_y, *lo_y, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_y = d_y->hi;
  lo_y = d_y->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  /* lo_x' = lo_x | (~hi_y & lo_z) */
  tmp0           = bzla_bv_not(mm, hi_y);
  tmp1           = bzla_bv_and(mm, tmp0, lo_z);
  (*res_d_x)->lo = bzla_bv_or(mm, lo_x, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_x' = hi_x & hi_z */
  (*res_d_x)->hi = bzla_bv_and(mm, hi_x, hi_z);

  /* lo_y' = lo_y | (~hi_x & lo_z) */
  tmp0           = bzla_bv_not(mm, hi_x);
  tmp1           = bzla_bv_and(mm, tmp0, lo_z);
  (*res_d_y)->lo = bzla_bv_or(mm, lo_y, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_y' = hi_y & hi_z */
  (*res_d_y)->hi = bzla_bv_and(mm, hi_y, hi_z);

  /* lo_z' = lo_z | lo_x | lo_y */
  tmp0           = bzla_bv_or(mm, lo_z, lo_x);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, lo_y);
  bzla_bv_free(mm, tmp0);

  /* hi_z' = hi_z & (hi_x | hi_y) */
  tmp0           = bzla_bv_or(mm, hi_x, hi_y);
  (*res_d_z)->hi = bzla_bv_and(mm, hi_z, tmp0);
  bzla_bv_free(mm, tmp0);

  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_y)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_xor(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  BzlaBitVector *tmp0, *tmp1, *tmp2;
  BzlaBitVector *not_hi_z, *not_hi_y, *not_hi_x;
  BzlaBitVector *hi_x, *lo_x, *hi_y, *lo_y, *hi_z, *lo_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_y = d_y->hi;
  lo_y = d_y->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  *res_d_x = new_domain(mm);
  *res_d_y = new_domain(mm);
  *res_d_z = new_domain(mm);

  not_hi_z = bzla_bv_not(mm, hi_z);
  not_hi_y = bzla_bv_not(mm, hi_y);
  not_hi_x = bzla_bv_not(mm, hi_x);

  /* lo_x' = lo_x | (~hi_z & lo_y) | (lo_z & ~hi_y) */
  tmp0 = bzla_bv_and(mm, not_hi_z, lo_y);
  tmp1 = bzla_bv_or(mm, lo_x, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, not_hi_y, lo_z);
  (*res_d_x)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_x' = hi_x & (hi_z | hi_y) & (~(lo_y & lo_z)) */
  tmp0 = bzla_bv_or(mm, hi_z, hi_y);
  tmp1 = bzla_bv_and(mm, hi_x, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, lo_y, lo_z);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_x)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);

  /* lo_y' = lo_y | (~hi_z & lo_x) | (lo_z & ~hi_x) */
  tmp0 = bzla_bv_and(mm, not_hi_z, lo_x);
  tmp1 = bzla_bv_or(mm, tmp0, lo_y);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, lo_z, not_hi_x);
  (*res_d_y)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_y' = hi_y & (hi_z | hi_x) & (~(lo_x & lo_z)) */
  tmp0 = bzla_bv_or(mm, hi_z, hi_x);
  tmp1 = bzla_bv_and(mm, hi_y, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, lo_x, lo_z);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_y)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);

  /* lo_z' = lo_z | (~hi_x & lo_y) | (lo_x & ~hi_y) */
  tmp0 = bzla_bv_and(mm, not_hi_x, lo_y);
  tmp1 = bzla_bv_or(mm, lo_z, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, lo_x, not_hi_y);
  (*res_d_z)->lo = bzla_bv_or(mm, tmp0, tmp1);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);

  /* hi_z' = hi_z & (hi_x | hi_y) & (~(lo_x & lo_y)) */
  tmp0 = bzla_bv_or(mm, hi_x, hi_y);
  tmp1 = bzla_bv_and(mm, hi_z, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp0           = bzla_bv_and(mm, lo_x, lo_y);
  tmp2           = bzla_bv_not(mm, tmp0);
  (*res_d_z)->hi = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp0);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  bzla_bv_free(mm, not_hi_x);
  bzla_bv_free(mm, not_hi_y);
  bzla_bv_free(mm, not_hi_z);
  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_y)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_slice(BzlaMemMgr *mm,
                  BzlaBvDomain *d_x,
                  BzlaBvDomain *d_z,
                  uint32_t upper,
                  uint32_t lower,
                  BzlaBvDomain **res_d_x,
                  BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(upper >= lower);
  assert(upper < bzla_bvdomain_get_width(d_x));
  assert(upper - lower + 1 == bzla_bvdomain_get_width(d_z));

  /* Apply equality propagator on sliced 'x' domain.
   *
   * lo_x' = lo_x[wx-1:upper+1] o lo_x[upper:lower] | lo_z o lo_x[lower - 1:0]
   * hi_x' = hi_x[wx-1:upper+1] o hi_x[upper:lower] & hi_z o hi_x[lower - 1:0]
   *
   * Note: We don't use the propagator described in [1] since it changes the
   *       don't care bits of 'd_x'.
   */

  BzlaBvDomain *sliced_x = new_domain(mm);
  sliced_x->lo           = bzla_bv_slice(mm, d_x->lo, upper, lower);
  sliced_x->hi           = bzla_bv_slice(mm, d_x->hi, upper, lower);

  BzlaBitVector *one = bzla_bv_one(mm, 1);
  BzlaBvDomain *d_eq = bzla_bvdomain_new(mm, one, one);
  bzla_bv_free(mm, one);

  bool valid = bzla_bvprop_eq(mm, sliced_x, d_z, d_eq, res_d_z, 0, 0);
  bzla_bvdomain_free(mm, d_eq);
  bzla_bvdomain_free(mm, sliced_x);
  uint32_t wx = bzla_bvdomain_get_width(d_x);

  if (!valid)
  {
    *res_d_x = new_invalid_domain(mm, wx);
    return false;
  }

  *res_d_x = new_domain(mm);

  BzlaBitVector *lo_x = bzla_bv_copy(mm, (*res_d_z)->lo);
  BzlaBitVector *hi_x = bzla_bv_copy(mm, (*res_d_z)->hi);
  BzlaBitVector *tmp;
  if (lower > 0)
  {
    BzlaBitVector *lower_lo_x = bzla_bv_slice(mm, d_x->lo, lower - 1, 0);
    BzlaBitVector *lower_hi_x = bzla_bv_slice(mm, d_x->hi, lower - 1, 0);
    tmp                       = bzla_bv_concat(mm, lo_x, lower_lo_x);
    bzla_bv_free(mm, lo_x);
    lo_x = tmp;
    tmp  = bzla_bv_concat(mm, hi_x, lower_hi_x);
    bzla_bv_free(mm, hi_x);
    hi_x = tmp;
    bzla_bv_free(mm, lower_lo_x);
    bzla_bv_free(mm, lower_hi_x);
  }

  if (upper < wx - 1)
  {
    BzlaBitVector *upper_lo_x = bzla_bv_slice(mm, d_x->lo, wx - 1, upper + 1);
    BzlaBitVector *upper_hi_x = bzla_bv_slice(mm, d_x->hi, wx - 1, upper + 1);
    tmp                       = bzla_bv_concat(mm, upper_lo_x, lo_x);
    bzla_bv_free(mm, lo_x);
    lo_x = tmp;
    tmp  = bzla_bv_concat(mm, upper_hi_x, hi_x);
    bzla_bv_free(mm, hi_x);
    hi_x = tmp;
    bzla_bv_free(mm, upper_lo_x);
    bzla_bv_free(mm, upper_hi_x);
  }

  assert(bzla_bv_get_width(lo_x) == wx);
  assert(bzla_bv_get_width(hi_x) == wx);
  (*res_d_x)->lo = lo_x;
  (*res_d_x)->hi = hi_x;
  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_concat(BzlaMemMgr *mm,
                   BzlaBvDomain *d_x,
                   BzlaBvDomain *d_y,
                   BzlaBvDomain *d_z,
                   BzlaBvDomain **res_d_x,
                   BzlaBvDomain **res_d_y,
                   BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool res;
  uint32_t wy, wz;

  wy = bzla_bvdomain_get_width(d_y);
  wz = bzla_bvdomain_get_width(d_z);

#if 0
  /* These are the propagators as proposed in [1]. */

  uint32_t wx;
  BzlaBitVector *mask, *zero, *ones, *tmp0, *tmp1;
  BzlaBitVector *lo_x, *hi_x, *lo_y, *hi_y;

  wx = bzla_bvdomain_get_width (d_x);

  lo_x = bzla_bv_uext (mm, d_x->lo, wz - wx);
  hi_x = bzla_bv_uext (mm, d_x->hi, wz - wx);
  lo_y = bzla_bv_uext (mm, d_y->lo, wz - wy);
  hi_y = bzla_bv_uext (mm, d_y->hi, wz - wy);

  zero = bzla_bv_zero (mm, wz - wy);
  ones = bzla_bv_ones (mm, wy);
  mask = bzla_bv_concat (mm, zero, ones);

  *res_d_x = new_domain (mm);
  *res_d_y = new_domain (mm);
  *res_d_z = new_domain (mm);

  /* lo_z' = lo_z | ((lo_x << wy) | lo_y) */
  tmp0           = bzla_bv_sll_uint32 (mm, lo_x, wy);
  tmp1           = bzla_bv_or (mm, tmp0, lo_y);
  (*res_d_z)->lo = bzla_bv_or (mm, d_z->lo, tmp1);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_z' = hi_z & ((hi_x << wy) | hi_y) */
  tmp0           = bzla_bv_sll_uint32 (mm, hi_x, wy);
  tmp1           = bzla_bv_or (mm, tmp0, hi_y);
  (*res_d_z)->hi = bzla_bv_and (mm, d_z->hi, tmp1);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* lo_x' = lo_x | (lo_z >> wy) */
  tmp0           = bzla_bv_srl_uint32 (mm, d_z->lo, wy);
  tmp1           = bzla_bv_or (mm, lo_x, tmp0);
  (*res_d_x)->lo = bzla_bv_slice (mm, tmp1, wx - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_x' = hi_x & (hi_z >> wy) */
  tmp0           = bzla_bv_srl_uint32 (mm, d_z->hi, wy);
  tmp1           = bzla_bv_and (mm, hi_x, tmp0);
  (*res_d_x)->hi = bzla_bv_slice (mm, tmp1, wx - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* lo_y' = lo_y | (lo_z & mask */
  tmp0           = bzla_bv_and (mm, d_z->lo, mask);
  tmp1           = bzla_bv_or (mm, lo_y, tmp0);
  (*res_d_y)->lo = bzla_bv_slice (mm, tmp1, wy - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  /* hi_y' = hi_y & (hi_z & mask) */
  tmp0           = bzla_bv_and (mm, d_z->hi, mask);
  tmp1           = bzla_bv_and (mm, hi_y, tmp0);
  (*res_d_y)->hi = bzla_bv_slice (mm, tmp1, wy - 1, 0);
  bzla_bv_free (mm, tmp0);
  bzla_bv_free (mm, tmp1);

  bzla_bv_free (mm, lo_x);
  bzla_bv_free (mm, hi_x);
  bzla_bv_free (mm, lo_y);
  bzla_bv_free (mm, hi_y);

  bzla_bv_free (mm, zero);
  bzla_bv_free (mm, ones);
  bzla_bv_free (mm, mask);
  res = bzla_bvdomain_is_valid (mm, *res_d_x)
        && bzla_bvdomain_is_valid (mm, *res_d_y)
        && bzla_bvdomain_is_valid (mm, *res_d_z);
#else
  /* These propagators are decompositional (simpler). */

  BzlaBitVector *lo_zx, *lo_zy, *hi_zx, *hi_zy;
  BzlaBvDomain *d_zx, *d_zy;

  /* z = zx o zy */
  lo_zx = bzla_bv_slice(mm, d_z->lo, wz - 1, wy);
  hi_zx = bzla_bv_slice(mm, d_z->hi, wz - 1, wy);
  lo_zy = bzla_bv_slice(mm, d_z->lo, wy - 1, 0);
  hi_zy = bzla_bv_slice(mm, d_z->hi, wy - 1, 0);
  d_zx  = bzla_bvdomain_new(mm, lo_zx, hi_zx);
  d_zy  = bzla_bvdomain_new(mm, lo_zy, hi_zy);

  *res_d_z = new_domain(mm);

  BzlaBitVector *one = bzla_bv_one(mm, 1);
  BzlaBvDomain *d_eq = bzla_bvdomain_new(mm, one, one);
  bzla_bv_free(mm, one);

  /* res_z = prop(d_zx = d_x) o prop(d_zy o d_y) */
  if (!bzla_bvprop_eq(mm, d_zx, d_x, d_eq, res_d_x, 0, 0))
  {
    res = false;
    goto DONE;
  }
  if (!bzla_bvprop_eq(mm, d_zy, d_y, d_eq, res_d_y, 0, 0))
  {
    res = false;
    goto DONE;
  }

  (*res_d_z)->lo = bzla_bv_concat(mm, (*res_d_x)->lo, (*res_d_y)->lo);
  (*res_d_z)->hi = bzla_bv_concat(mm, (*res_d_x)->hi, (*res_d_y)->hi);

  res = bzla_bvdomain_is_valid(mm, *res_d_x)
        && bzla_bvdomain_is_valid(mm, *res_d_y)
        && bzla_bvdomain_is_valid(mm, *res_d_z);
DONE:
  bzla_bv_free(mm, lo_zx);
  bzla_bv_free(mm, lo_zy);
  bzla_bv_free(mm, hi_zx);
  bzla_bv_free(mm, hi_zy);
  bzla_bvdomain_free(mm, d_zx);
  bzla_bvdomain_free(mm, d_zy);
  bzla_bvdomain_free(mm, d_eq);
#endif
  return res;
}

bool
bzla_bvprop_sext(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_z);

  uint32_t wx, wn, wz, lo_x_lsb, hi_x_lsb;
  BzlaBitVector *hi_x, *lo_x, *hi_z, *lo_z;
  BzlaBitVector *tmp0, *tmp1, *tmp2;
  BzlaBitVector *slice_lo_z_hi, *slice_hi_z_hi;
  BzlaBitVector *redor, *redand, *x_or_z, *x_and_z;

  hi_x = d_x->hi;
  lo_x = d_x->lo;
  hi_z = d_z->hi;
  lo_z = d_z->lo;

  *res_d_x = new_domain(mm);
  *res_d_z = new_domain(mm);

  wx = bzla_bvdomain_get_width(d_x);
  wz = bzla_bvdomain_get_width(d_z);
  wn = wz - wx;
  assert(wn);

  lo_x_lsb = bzla_bv_get_bit(lo_x, wx - 1);
  hi_x_lsb = bzla_bv_get_bit(hi_x, wx - 1);

  /* Note: The propagators for x and z from [1] are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  if (wx > 1)
  {
    tmp0   = bzla_bv_slice(mm, lo_x, wx - 2, 0);
    tmp1   = bzla_bv_slice(mm, lo_z, wx - 2, 0);
    x_or_z = bzla_bv_or(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    tmp0    = bzla_bv_slice(mm, hi_x, wx - 2, 0);
    tmp1    = bzla_bv_slice(mm, hi_z, wx - 2, 0);
    x_and_z = bzla_bv_and(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
  }
  slice_lo_z_hi = wx > 1 ? bzla_bv_slice(mm, lo_z, wz - 1, wx - 1) : lo_z;
  slice_hi_z_hi = wx > 1 ? bzla_bv_slice(mm, hi_z, wz - 1, wx - 1) : hi_z;

  redor  = bzla_bv_redor(mm, slice_lo_z_hi);
  redand = bzla_bv_redand(mm, slice_hi_z_hi);

  /**
   * lo_x' = (lo_x[wx-1:wx-1] | redor (lo_z[wz-1:wx-1]))
   *         :: (lo_x[wx-2:0] | lo_z[wx-2:0])
   */
  tmp1 = bzla_bv_slice(mm, lo_x, wx - 1, wx - 1);
  tmp0 = bzla_bv_or(mm, tmp1, redor);
  bzla_bv_free(mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->lo = bzla_bv_concat(mm, tmp0, x_or_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_x)->lo = tmp0;
  }

  /**
   * hi_x' = (hi_x[wx-1:wx-1] & redand (hi_z[wz-1:wx-1]))
   *         :: (hi_x[wx-2:0] & hi_z[wx-2:0])
   */
  tmp1 = bzla_bv_slice(mm, hi_x, wx - 1, wx - 1);
  tmp0 = bzla_bv_and(mm, tmp1, redand);
  bzla_bv_free(mm, tmp1);
  if (wx > 1)
  {
    (*res_d_x)->hi = bzla_bv_concat(mm, tmp0, x_and_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_x)->hi = tmp0;
  }

  /**
   * lo_z' = (lo_z[wz-1:wx-1]
   *          | sext(redor (lo_z[wz-1:wx-1]), wn)
   *          | sext(lo_x[wx-1:wx-1], wn))
   *         :: (lo_z[wx-2:0] | lo_x[wx-2:0])
   */
  tmp0 = lo_x_lsb ? bzla_bv_ones(mm, wn + 1) : bzla_bv_zero(mm, wn + 1);
  tmp1 = bzla_bv_or(mm, slice_lo_z_hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp2 = bzla_bv_sext(mm, redor, wn);
  tmp0 = bzla_bv_or(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->lo = bzla_bv_concat(mm, tmp0, x_or_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_z)->lo = tmp0;
  }

  /**
   * hi_z' = (hi_z[[wz-1:wx-1]
   *          & sext(redand (lo_z[wz-1:wx-1]), wn)
   *          & sext(hi_x[wx-1:wx-1], wn))
   *         :: (hi_z[wx-2:0] & hi_x[wx-2:0])
   */
  tmp0 = hi_x_lsb ? bzla_bv_ones(mm, wn + 1) : bzla_bv_zero(mm, wn + 1);
  tmp1 = bzla_bv_and(mm, slice_hi_z_hi, tmp0);
  bzla_bv_free(mm, tmp0);
  tmp2 = bzla_bv_sext(mm, redand, wn);
  tmp0 = bzla_bv_and(mm, tmp1, tmp2);
  bzla_bv_free(mm, tmp1);
  bzla_bv_free(mm, tmp2);
  if (wx > 1)
  {
    (*res_d_z)->hi = bzla_bv_concat(mm, tmp0, x_and_z);
    bzla_bv_free(mm, tmp0);
  }
  else
  {
    (*res_d_z)->hi = tmp0;
  }

  if (wx > 1)
  {
    bzla_bv_free(mm, x_or_z);
    bzla_bv_free(mm, x_and_z);
    bzla_bv_free(mm, slice_lo_z_hi);
    bzla_bv_free(mm, slice_hi_z_hi);
  }
  bzla_bv_free(mm, redor);
  bzla_bv_free(mm, redand);

#if 0
  /* These are the propagators from [1] which are incorrect!
   * E.g. for x = 1 and z = 001 we expect an invalid result, but these
   * propagators produce x' = 1 and z' = 111. */

  uint32_t i, lo_z_bit, hi_z_bit;
  BzlaBvDomain *tmp_x = bzla_bvdomain_new (mm, lo_x, hi_x);

  /**
   * lo_x' = lo_x | (lo_z & mask1) with mask1 = 0_[wn] :: ~0_[wx]
   * simplifies to
   * lo_x' = lo_x | lo_z[wx-1:0]
   */
  slice = bzla_bv_slice (mm, lo_z, wx-1, 0);
  (*res_tmp_x)->lo = bzla_bv_or (mm, tmp_x->lo, slice);
  bzla_bv_free (mm, slice);

  /**
   * hi_x' = hi_x & (hi_z & mask1)
   * simplifies to
   * hi_x' = hi_x & hi_z[wx-1:0]
   */
  slice = bzla_bv_slice (mm, hi_z, wx-1, 0);
  (*res_tmp_x)->hi = bzla_bv_and (mm, tmp_x->hi, slice);
  bzla_bv_free (mm, slice);

  if (!lo_x_lsb && !hi_x_lsb)     /* sign bit 0 */
  {
SEXT_SIGN_0:
    /**
     * lo_z' = (lo_x | mask2) | lo_z with mask2 = 0_[wx+wn]
     * simplifies to
     * lo_x' = uext(lo_x, wn) | lo_z
     */
    tmp0 = bzla_bv_uext(mm, tmp_x->lo, wn);
    (*res_d_z)->lo = bzla_bv_or (mm, lo_z, tmp0);
    bzla_bv_free (mm, tmp0);

    /**
     * hi_z' = (hi_x | mask2) & hi_z
     * simplifies to
     * hi_z' = uext(hi_x, wn) & hi_z
     */
    tmp0 = bzla_bv_uext(mm, tmp_x->hi, wn);
    (*res_d_z)->hi = bzla_bv_and (mm, hi_z, tmp0);
    bzla_bv_free (mm, tmp0);
  }
  else if (lo_x_lsb && hi_x_lsb)  /* sign bit 1 */
  {
SEXT_SIGN_1:
    tmp0 = bzla_bv_ones (mm, wn);
    /**
     * lo_z' = lo_x | mask2 with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * lo_z' = ~0_[wn] :: lo_x
     */
    (*res_d_z)->lo = bzla_bv_concat (mm, tmp0, tmp_x->lo);
    /**
     * hi_z' = hi_x | mask2
     * simplifies to
     * hi_z' = ~0_[wn] :: hi_x
     */
    (*res_d_z)->hi = bzla_bv_concat (mm, tmp0, tmp_x->hi);
    bzla_bv_free (mm, tmp0);
  }
  else                            /* sign bit x */
  {
    assert (!lo_x_lsb && hi_x_lsb);

    for (i = wz - 1; i >= wx - 1; i--)
    {
      lo_z_bit = bzla_bv_get_bit (lo_z, i);
      hi_z_bit = bzla_bv_get_bit (hi_z, i);
      /* if exists z_i = 0 with i >= wx - 1 apply rule for zero sign bit */
      if (!lo_z_bit && !hi_z_bit)
      {
        bzla_bv_set_bit (tmp_x->lo, wx - 1, 0);
        goto SEXT_SIGN_0;
      }
      /* if exists z_i = 1 with i >= wx - 1 apply rule for one sign bit */
      if (lo_z_bit && hi_z_bit)
      {
        bzla_bv_set_bit (tmp_x->lo, wx - 1, 1);
        goto SEXT_SIGN_1;
      }
    }
    /**
     * lo_z' = lo_z | (lo_x | mask3) with mask3 = 0_[wz]
     * simplifies to
     * lo_x' = lo_z | uext(lo_x, wn)
     */
    tmp0 = bzla_bv_uext (mm, tmp_x->lo, wn);
    (*res_d_x)->lo = bzla_bv_or (mm, lo_z, tmp0);
    bzla_bv_free (mm, tmp0);

    /**
     * hi_z' = hi_z & (hi_x | mask2) with mask2 = ~0_[wn] :: 0_[wx]
     * simplifies to
     * hi_z' = hi_z & (~0_[wn] :: hi_x)
     */
    tmp0 = bzla_bv_ones (mm, wn);
    tmp1 = bzla_bv_concat (mm, tmp0, tmp_x->hi);
    (*res_d_x)->lo = bzla_bv_and (mm, hi_z, tmp1);
    bzla_bv_free (mm, tmp0);
    bzla_bv_free (mm, tmp1);
  }
  bzla_bvdomain_free (mm, tmp_x);
#endif
  return bzla_bvdomain_is_valid(mm, *res_d_x)
         && bzla_bvdomain_is_valid(mm, *res_d_z);
}

bool
bzla_bvprop_cond(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain *d_c,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_y,
                 BzlaBvDomain **res_d_z,
                 BzlaBvDomain **res_d_c)
{
  assert(mm);
  assert(d_c);
  assert(bzla_bvdomain_is_valid(mm, d_c));
  assert(bzla_bvdomain_get_width(d_c) == 1);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_c);
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool res;
  uint32_t bw;
  bool progress, c_is_fixed;
  BzlaBvDomain *tmp_bvc, *res_tmp_bvc, *tmp_x, *tmp_y, *tmp_z, *tmp_c;
  BzlaBitVector *hi_x, *lo_x, *not_hi_x, *not_lo_x;
  BzlaBitVector *hi_y, *lo_y, *not_hi_y, *not_lo_y;
  BzlaBitVector *hi_z, *lo_z, *not_hi_z;
  BzlaBitVector *hi_bvc, *lo_bvc, *not_hi_bvc, *not_lo_bvc;
  BzlaBitVector *ones, *zero, *tmp0, *tmp1, *tmp2;

  res = true;

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_y));
  assert(bw == bzla_bvdomain_get_width(d_z));

  ones = bzla_bv_ones(mm, bw);
  zero = bzla_bv_zero(mm, bw);

  if (bzla_bvdomain_is_fixed(mm, d_c))
  {
    c_is_fixed = true;
    if (bzla_bv_get_bit(d_c->lo, 0) == 0)
    {
      tmp_bvc = bzla_bvdomain_new(mm, zero, zero);
    }
    else
    {
      assert(bzla_bv_get_bit(d_c->lo, 0) == 1);
      tmp_bvc = bzla_bvdomain_new(mm, ones, ones);
    }
  }
  else
  {
    c_is_fixed = false;
    tmp_bvc    = bzla_bvdomain_new_init(mm, bw);
  }

  tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);
  tmp_c = bzla_bvdomain_new(mm, d_c->lo, d_c->hi);

  not_hi_x   = 0;
  not_lo_x   = 0;
  not_hi_y   = 0;
  not_lo_y   = 0;
  not_hi_z   = 0;
  not_hi_bvc = 0;
  not_lo_bvc = 0;

  do
  {
    progress = false;

    hi_x   = tmp_x->hi;
    lo_x   = tmp_x->lo;
    hi_y   = tmp_y->hi;
    lo_y   = tmp_y->lo;
    hi_z   = tmp_z->hi;
    lo_z   = tmp_z->lo;
    hi_bvc = tmp_bvc->hi;
    lo_bvc = tmp_bvc->lo;

    res_tmp_bvc = new_domain(mm);
    *res_d_x    = new_domain(mm);
    *res_d_y    = new_domain(mm);
    *res_d_z    = new_domain(mm);

    if (not_hi_x) bzla_bv_free(mm, not_hi_x);
    if (not_lo_x) bzla_bv_free(mm, not_lo_x);
    if (not_hi_y) bzla_bv_free(mm, not_hi_y);
    if (not_lo_y) bzla_bv_free(mm, not_lo_y);
    if (not_hi_z) bzla_bv_free(mm, not_hi_z);
    if (not_hi_bvc) bzla_bv_free(mm, not_hi_bvc);
    if (not_lo_bvc) bzla_bv_free(mm, not_lo_bvc);

    not_hi_x   = bzla_bv_not(mm, hi_x);
    not_lo_x   = bzla_bv_not(mm, lo_x);
    not_hi_y   = bzla_bv_not(mm, hi_y);
    not_lo_y   = bzla_bv_not(mm, lo_y);
    not_hi_z   = bzla_bv_not(mm, hi_z);
    not_lo_bvc = bzla_bv_not(mm, lo_bvc);
    not_hi_bvc = bzla_bv_not(mm, hi_bvc);

    /* lo_bvc' = lo_bvc | (lo_z & ~hi_y) | (~hi_z & lo_y) */
    tmp0            = bzla_bv_and(mm, not_hi_z, lo_y);
    tmp1            = bzla_bv_and(mm, lo_z, not_hi_y);
    tmp2            = bzla_bv_or(mm, tmp0, tmp1);
    res_tmp_bvc->lo = bzla_bv_or(mm, lo_bvc, tmp2);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* hi_bvc' = hi_bvc & (~lo_z | hi_x) & (hi_z | ~lo_x) */
    tmp0 = bzla_bv_or(mm, hi_z, not_lo_x);
    tmp1 = bzla_bv_not(mm, lo_z);
    tmp2 = bzla_bv_or(mm, tmp1, hi_x);
    bzla_bv_free(mm, tmp1);
    tmp1            = bzla_bv_and(mm, tmp0, tmp2);
    res_tmp_bvc->hi = bzla_bv_and(mm, hi_bvc, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* lo_x' = lo_x | (lo_z & (lo_bvc | ~hi_y)) */
    tmp0           = bzla_bv_or(mm, lo_bvc, not_hi_y);
    tmp1           = bzla_bv_and(mm, lo_z, tmp0);
    (*res_d_x)->lo = bzla_bv_or(mm, lo_x, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* hi_x' = hi_x & (~(~hi_z & (lo_bvc | lo_y)))
     *
     * (corresponds to
     *    hi_x' = hi_x & (hi_z | (~lo_bvc & ~lo_y))
     * )
     */
    tmp0           = bzla_bv_and(mm, not_lo_bvc, not_lo_y);
    tmp1           = bzla_bv_or(mm, hi_z, tmp0);
    (*res_d_x)->hi = bzla_bv_and(mm, hi_x, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* lo_y' = lo_y | (lo_z & (~hi_bvc | ~hi_x)) */
    tmp0           = bzla_bv_or(mm, not_hi_bvc, not_hi_x);
    tmp1           = bzla_bv_and(mm, lo_z, tmp0);
    (*res_d_y)->lo = bzla_bv_or(mm, lo_y, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* hi_y' = hi_y & (hi_z | (hi_bvc & ~lo_x)) */
    tmp0           = bzla_bv_and(mm, hi_bvc, not_lo_x);
    tmp1           = bzla_bv_or(mm, hi_z, tmp0);
    (*res_d_y)->hi = bzla_bv_and(mm, hi_y, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);

    /* lo_z' = lo_z | (lo_bvc & lo_x) | (~hi_bvc & lo_y) | (lo_x & lo_y) */
    tmp0 = bzla_bv_and(mm, lo_x, lo_y);
    tmp1 = bzla_bv_and(mm, not_hi_bvc, lo_y);
    tmp2 = bzla_bv_or(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    tmp0           = bzla_bv_and(mm, lo_bvc, lo_x);
    tmp1           = bzla_bv_or(mm, tmp0, tmp2);
    (*res_d_z)->lo = bzla_bv_or(mm, lo_z, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    /* hi_z' = hi_z & (~lo_bvc | hi_x) & (hi_bvc | hi_y) & (hi_x | hi_y) */
    tmp0 = bzla_bv_or(mm, hi_x, hi_y);
    tmp1 = bzla_bv_or(mm, hi_bvc, hi_y);
    tmp2 = bzla_bv_and(mm, tmp0, tmp1);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    tmp1           = bzla_bv_or(mm, not_lo_bvc, hi_x);
    tmp0           = bzla_bv_and(mm, tmp1, tmp2);
    (*res_d_z)->hi = bzla_bv_and(mm, hi_z, tmp0);
    bzla_bv_free(mm, tmp0);
    bzla_bv_free(mm, tmp1);
    bzla_bv_free(mm, tmp2);

    if (!bzla_bvdomain_is_valid(mm, res_tmp_bvc)
        || !bzla_bvdomain_is_valid(mm, *res_d_x)
        || !bzla_bvdomain_is_valid(mm, *res_d_y)
        || !bzla_bvdomain_is_valid(mm, *res_d_z))
    {
      res = false;
      bzla_bvdomain_free(mm, tmp_x);
      bzla_bvdomain_free(mm, tmp_y);
      bzla_bvdomain_free(mm, tmp_z);
      bzla_bvdomain_free(mm, res_tmp_bvc);
      tmp_x = *res_d_x;
      tmp_y = *res_d_y;
      tmp_z = *res_d_z;
      goto DONE;
    }

    if (bw > 1 && !progress)
    {
      progress = made_progress(tmp_x,
                               tmp_y,
                               tmp_z,
                               tmp_bvc,
                               *res_d_x,
                               *res_d_y,
                               *res_d_z,
                               res_tmp_bvc);
    }

    bzla_bvdomain_free(mm, tmp_x);
    bzla_bvdomain_free(mm, tmp_y);
    bzla_bvdomain_free(mm, tmp_z);
    bzla_bvdomain_free(mm, tmp_bvc);
    tmp_x   = *res_d_x;
    tmp_y   = *res_d_y;
    tmp_z   = *res_d_z;
    tmp_bvc = res_tmp_bvc;

    if (bw > 1 && !c_is_fixed && progress)
    {
      if (!(res = decomp_step_unary(mm,
                                    &tmp_c,
                                    &tmp_bvc,
                                    res_d_c,
                                    &res_tmp_bvc,
                                    bzla_bvprop_sext,
                                    &progress)))
      {
        goto DONE;
      }
    }
  } while (progress);

  assert(bzla_bvdomain_is_valid(mm, tmp_bvc));
  assert(bzla_bvdomain_is_valid(mm, tmp_c));
  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(bzla_bvdomain_is_valid(mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;
  *res_d_c = tmp_c;

  bzla_bv_free(mm, not_hi_x);
  bzla_bv_free(mm, not_lo_x);
  bzla_bv_free(mm, not_hi_y);
  bzla_bv_free(mm, not_lo_y);
  bzla_bv_free(mm, not_hi_z);
  bzla_bv_free(mm, not_lo_bvc);
  bzla_bv_free(mm, not_hi_bvc);

  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, zero);
  bzla_bvdomain_free(mm, tmp_bvc);

  return res;
}

/**
 * Note: 'd_cout' optionally passes in the input domain for cout.
 *       'res_d_cout' optionally returns the resulting domain for cout.
 */
static bool
bvprop_add_aux(BzlaMemMgr *mm,
               BzlaBvDomain *d_x,
               BzlaBvDomain *d_y,
               BzlaBvDomain *d_z,
               BzlaBvDomain *d_cout,
               BzlaBvDomain **res_d_x,
               BzlaBvDomain **res_d_y,
               BzlaBvDomain **res_d_z,
               BzlaBvDomain **res_d_cout,
               bool no_overflows)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  bool progress, res;
  uint32_t bw;
  BzlaBitVector *one;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_z;
  BzlaBvDomain *tmp_cin, *tmp_cout;
  BzlaBvDomain *tmp_x_xor_y, *tmp_x_and_y;
  BzlaBvDomain *tmp_cin_and_x_xor_y;
  BzlaBvDomain *tmp_cout_msb;
#ifndef NDEBUG
  BzlaBvDomain *d_one;
#endif
  BzlaBvDomain *tmp_one;

  res = true;

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_y));
  assert(bw == bzla_bvdomain_get_width(d_z));
  one = bzla_bv_one(mm, bw);

  /* cin = x...x0 */
  tmp_cin = bzla_bvdomain_new_init(mm, bw);
  bzla_bv_set_bit(tmp_cin->hi, 0, 0);
  /* cout = x...x if not given */
  tmp_cout = d_cout ? bzla_bvdomain_new(mm, d_cout->lo, d_cout->hi)
                    : bzla_bvdomain_new_init(mm, bw);

  /**
   * full adder:
   * z    = x ^ y ^ cin
   * cout = (x & y) | (cin & (x ^ y))
   * cin  = cout << 1
   */

  tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);

  tmp_x_xor_y         = bzla_bvdomain_new_init(mm, bw);
  tmp_x_and_y         = bzla_bvdomain_new_init(mm, bw);
  tmp_cin_and_x_xor_y = bzla_bvdomain_new_init(mm, bw);

  tmp_cout_msb = 0;
  tmp_one      = 0;
#ifndef NDEBUG
  d_one = 0;
#endif

  if (no_overflows)
  {
    tmp_cout_msb = bzla_bvdomain_new_init(mm, 1);
    tmp_one      = bzla_bvdomain_new_init(mm, 1);
    bzla_bv_set_bit(tmp_one->lo, 0, 1);
#ifndef NDEBUG
    d_one = bzla_bvdomain_new_init(mm, 1);
    bzla_bv_set_bit(d_one->lo, 0, 1);
#endif
  }

  do
  {
    progress = false;

    /* x_xor_y = x ^ y */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_x,
                                   &tmp_y,
                                   &tmp_x_xor_y,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_xor,
                                   &progress)))
    {
      goto DONE;
    }

    /* z = x_xor_y ^ cin */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_x_xor_y,
                                   &tmp_cin,
                                   &tmp_z,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_xor,
                                   &progress)))
    {
      goto DONE;
    }

    /* x_and_y = x & y */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_x,
                                   &tmp_y,
                                   &tmp_x_and_y,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_and,
                                   &progress)))
    {
      goto DONE;
    }

    /* cin_and_x_xor_y = cin & x_xor_y */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_cin,
                                   &tmp_x_xor_y,
                                   &tmp_cin_and_x_xor_y,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_and,
                                   &progress)))
    {
      goto DONE;
    }

    /* cout = x_and_y | cin_and_x_xor_y */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_x_and_y,
                                   &tmp_cin_and_x_xor_y,
                                   &tmp_cout,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_or,
                                   &progress)))
    {
      goto DONE;
    }

    /* cin  = cout << 1 */
    if (!(res = decomp_step_shiftc(mm,
                                   &tmp_cout,
                                   &tmp_cin,
                                   one,
                                   res_d_x,
                                   res_d_z,
                                   bzla_bvprop_sll_const,
                                   &progress)))
    {
      goto DONE;
    }

    if (no_overflows)
    {
      assert(tmp_cout_msb);
      assert(tmp_one);

      /**
       * Overflow:
       * cout[MSB:MSB] == 1
       *
       * Add no-overflow propagation constraint:
       * cout[MSB:MSB] == 0
       * <->
       * 1 xor cout[MSB:MSB] = 1
       */

      /* cout[MSB:MSB] */
      if (!(res = decomp_step_slice(mm,
                                    &tmp_cout,
                                    &tmp_cout_msb,
                                    bw - 1,
                                    bw - 1,
                                    res_d_x,
                                    res_d_z,
                                    bzla_bvprop_slice,
                                    &progress)))
      {
        goto DONE;
      }

      /* 1 xor cout[MSB:MSB] = 1 */
      if (!(res = decomp_step_binary(mm,
                                     &tmp_one,
                                     &tmp_cout_msb,
                                     &tmp_one,
                                     res_d_x,
                                     res_d_y,
                                     res_d_z,
                                     bzla_bvprop_xor,
                                     &progress)))
      {
        goto DONE;
      }
      assert(compare_fixed_domain(mm, d_one, tmp_one));
    }
  } while (progress);

  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(bzla_bvdomain_is_valid(mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  if (res_d_cout)
    *res_d_cout = tmp_cout;
  else
    bzla_bvdomain_free(mm, tmp_cout);

  bzla_bvdomain_free(mm, tmp_cin);
  bzla_bvdomain_free(mm, tmp_x_xor_y);
  bzla_bvdomain_free(mm, tmp_x_and_y);
  bzla_bvdomain_free(mm, tmp_cin_and_x_xor_y);
  if (tmp_cout_msb) bzla_bvdomain_free(mm, tmp_cout_msb);
  if (tmp_one) bzla_bvdomain_free(mm, tmp_one);
#ifndef NDEBUG
  if (d_one) bzla_bvdomain_free(mm, d_one);
#endif

  bzla_bv_free(mm, one);

  return res;
}

bool
bzla_bvprop_add_aux(BzlaMemMgr *mm,
                    BzlaBvDomain *d_x,
                    BzlaBvDomain *d_y,
                    BzlaBvDomain *d_z,
                    BzlaBvDomain **res_d_x,
                    BzlaBvDomain **res_d_y,
                    BzlaBvDomain **res_d_z,
                    bool no_overflows)
{
  bool res;
  res = bvprop_add_aux(
      mm, d_x, d_y, d_z, 0, res_d_x, res_d_y, res_d_z, 0, no_overflows);
  return res;
}

bool
bzla_bvprop_add(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  return bzla_bvprop_add_aux(
      mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
bzla_bvprop_mul_aux(BzlaMemMgr *mm,
                    BzlaBvDomain *d_x,
                    BzlaBvDomain *d_y,
                    BzlaBvDomain *d_z,
                    BzlaBvDomain **res_d_x,
                    BzlaBvDomain **res_d_y,
                    BzlaBvDomain **res_d_z,
                    bool no_overflows)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));
  assert(res_d_x);
  assert(res_d_y);
  assert(res_d_z);

  /* z_[bw] = x_[bw] * y_[bw]
   * rewrites to
   * ite (y[bw-1:bw-1], x << (bw - 1), 0)
   *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
   *   + ...
   *   + ite (y[1:1], x << 1, 0)
   *   + ite (y[0:0], x, 0)
   */

  uint32_t i, bw, bwo, n;
  bool res, progress;
  BzlaBitVector *bv, *lo, *hi;
  BzlaBvDomain *d;
#ifndef NDEBUG
  BzlaBvDomain *d_one, *d_zero, *d_zero_bw;
#endif
  BzlaBvDomain *tmp_one, *tmp_zero;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_z, *tmp_zero_bw;
  BzlaBvDomain **tmp_c, **tmp_shift, **tmp_ite, **tmp0, **tmp1, **tmp_add;
  BzlaBvDomain *tmp_res_c, *tmp_slice;
  BzlaBvDomain **tmp;
  BzlaBvDomainPtrStack d_c_stack, d_shift_stack, d_ite_stack, d_add_stack;
  BzlaBitVectorPtrStack shift_stack;

  progress = false;

  BZLA_INIT_STACK(mm, d_c_stack);
  BZLA_INIT_STACK(mm, d_shift_stack);
  BZLA_INIT_STACK(mm, d_ite_stack);
  BZLA_INIT_STACK(mm, d_add_stack);
  BZLA_INIT_STACK(mm, shift_stack);

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_y));
  assert(bw == bzla_bvdomain_get_width(d_z));

#ifndef NDEBUG
  d_one  = 0;
  d_zero = 0;
#endif
  tmp_one   = 0;
  tmp_zero  = 0;
  tmp_slice = 0;

  tmp_y = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);

  if (bw == 1)
  {
    /**
     * For bit-width 1, multiplication simplifies to d_z = ite (d_y, x, 0).
     * No overflows for bit-width 1.
     */

    tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);

    tmp_zero_bw     = new_domain(mm);
    tmp_zero_bw->lo = bzla_bv_zero(mm, bw);
    tmp_zero_bw->hi = bzla_bv_zero(mm, bw);
#ifndef NDEBUG
    d_zero_bw     = new_domain(mm);
    d_zero_bw->lo = bzla_bv_zero(mm, bw);
    d_zero_bw->hi = bzla_bv_zero(mm, bw);
#endif

    if (!(res = decomp_step_ternary(mm,
                                    &tmp_x,
                                    &tmp_zero_bw,
                                    &tmp_z,
                                    &tmp_y,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    &tmp_res_c,
                                    bzla_bvprop_cond,
                                    &progress)))
    {
      goto DONE;
    }
    assert(compare_fixed_domain(mm, d_zero_bw, tmp_zero_bw));
  }
  else
  {
    /**
     * The full implementation of
     *   ite (y[bw-1:bw-1], x << (bw - 1), 0)
     *     + ite (y[bw-2:bw-2], x << (bw-2), 0)
     *     + ...
     *     + ite (y[1:1], x << 1, 0)
     *     + ite (y[0:0], x, 0)
     * would require n left shift propagators, n ite propagators, and n - 1
     * add propagators (n = bw).
     * We can simplify that since for each ite, the initial result domain is
     * x...x = ite (condition, shift, 0). If the y bit at an index i (and
     * therefore the condition for the i-th ite) is 0, the result of the ite
     * is always 0 (that's the only possible propagation, no invalid results
     * possible). Hence we can skip all 0 bits of y (i.e., all ite with a 0
     * condition), except the last one (the last one is the end result).
     */

    bwo = no_overflows ? 2 * bw : bw;

#ifndef NDEBUG
    d_zero_bw     = new_domain(mm);
    d_zero_bw->lo = bzla_bv_zero(mm, bwo);
    d_zero_bw->hi = bzla_bv_zero(mm, bwo);
#endif
    tmp_zero_bw     = new_domain(mm);
    tmp_zero_bw->lo = bzla_bv_zero(mm, bwo);
    tmp_zero_bw->hi = bzla_bv_zero(mm, bwo);

    if (no_overflows)
    {
      /**
       * no overflows: double the bit-width and assert that the upper half of
       *               the multiplication result is 0
       */

      lo    = bzla_bv_uext(mm, d_x->lo, bw);
      hi    = bzla_bv_uext(mm, d_x->hi, bw);
      tmp_x = bzla_bvdomain_new(mm, lo, hi);
      bzla_bv_free(mm, lo);
      bzla_bv_free(mm, hi);

#ifndef NDEBUG
      d_zero     = new_domain(mm);
      d_zero->lo = bzla_bv_zero(mm, bw);
      d_zero->hi = bzla_bv_zero(mm, bw);

      d_one     = new_domain(mm);
      d_one->lo = bzla_bv_one(mm, 1);
      d_one->hi = bzla_bv_one(mm, 1);
#endif
      tmp_zero     = new_domain(mm);
      tmp_zero->lo = bzla_bv_zero(mm, bw);
      tmp_zero->hi = bzla_bv_zero(mm, bw);

      tmp_one     = new_domain(mm);
      tmp_one->lo = bzla_bv_one(mm, 1);
      tmp_one->hi = bzla_bv_one(mm, 1);

      tmp_slice = bzla_bvdomain_new_init(mm, bw);
    }
    else
    {
      tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);
    }

    for (i = 0; i < bw; i++)
    {
      n = bw - 1 - i;

      /* if y bit is zero, the result of the ite is zero, skip */
      if (i < bw - 1 && !bzla_bv_get_bit(d_y->lo, n)
          && !bzla_bv_get_bit(d_y->hi, n))
        continue;

      /* slice y into bw ite conditions */
      d     = new_domain(mm);
      d->lo = bzla_bv_slice(mm, d_y->lo, n, n);
      d->hi = bzla_bv_slice(mm, d_y->hi, n, n);
      BZLA_PUSH_STACK(d_c_stack, d);
      /* m shift propagators (m = number of 1 or x bits in y) */
      d = bzla_bvdomain_new_init(mm, bwo);
      BZLA_PUSH_STACK(d_shift_stack, d);
      /* m ite propagators */
      d = bzla_bvdomain_new_init(mm, bwo);
      BZLA_PUSH_STACK(d_ite_stack, d);
      /* m - 1 add propagators */
      if (BZLA_COUNT_STACK(d_c_stack) > 1)
      {
        d = bzla_bvdomain_new_init(mm, bwo);
        BZLA_PUSH_STACK(d_add_stack, d);
      }
      /* shift width */
      bv = bzla_bv_uint64_to_bv(mm, n, bwo);
      BZLA_PUSH_STACK(shift_stack, bv);
    }

    /**
     * if m > 0: final add is end result
     * else    : there is a single ite which is the end result
     */
    if (BZLA_COUNT_STACK(d_add_stack))
    {
      /* last adder is end result: d_z = add_[m-1]*/
      if (no_overflows)
      {
        d     = new_domain(mm);
        d->lo = bzla_bv_uext(mm, d_z->lo, bw);
        d->hi = bzla_bv_uext(mm, d_z->hi, bw);
      }
      else
      {
        d = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);
      }
      bzla_bvdomain_free(mm, BZLA_POP_STACK(d_add_stack));
      BZLA_PUSH_STACK(d_add_stack, d);
    }
    else
    {
      /**
       * We have at least one ite propagator, even if all bits in y are 0.
       * In case there is only a single ite propagator, it is the end result.
       */
      assert(BZLA_COUNT_STACK(d_ite_stack) == 1);
      if (BZLA_COUNT_STACK(d_ite_stack))
      {
        if (no_overflows)
        {
          d     = new_domain(mm);
          d->lo = bzla_bv_uext(mm, d_z->lo, bw);
          d->hi = bzla_bv_uext(mm, d_z->hi, bw);
        }
        else
        {
          d = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);
        }
        bzla_bvdomain_free(mm, BZLA_POP_STACK(d_ite_stack));
        BZLA_PUSH_STACK(d_ite_stack, d);
      }
    }

    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_shift_stack));
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_ite_stack));
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(d_add_stack) + 1);
    assert(BZLA_COUNT_STACK(d_c_stack) == BZLA_COUNT_STACK(shift_stack));

    do
    {
      progress = false;

      for (i = 0; i < BZLA_COUNT_STACK(d_c_stack); i++)
      {
        /**
         * x << bw - 1 - m where m is the current bit index.
         * The shift width of the current bit index (!= i) is stored at index i.
         * The current bit index is not explicit here, since we only generate
         * propagators for bits that 1/x (or for the last 0 bit if y = 0).
         */
        bv        = BZLA_PEEK_STACK(shift_stack, i);
        tmp_shift = &d_shift_stack.start[i];
        if (!(res = decomp_step_shiftc(mm,
                                       &tmp_x,
                                       tmp_shift,
                                       bv,
                                       res_d_x,
                                       res_d_z,
                                       bzla_bvprop_sll_const,
                                       &progress)))
        {
          goto DONE;
        }

        /* ite (y[bw-1-m:bw-1-m], x << bw - 1 - m, 0) */
        tmp_c   = &d_c_stack.start[i];
        tmp_ite = &d_ite_stack.start[i];
        assert(!no_overflows || bzla_bvdomain_get_width((*tmp_shift)) == bwo);
        assert(!no_overflows || bzla_bvdomain_get_width((tmp_zero_bw)) == bwo);
        assert(!no_overflows || bzla_bvdomain_get_width((*tmp_ite)) == bwo);
        if (!(res = decomp_step_ternary(mm,
                                        tmp_shift,
                                        &tmp_zero_bw,
                                        tmp_ite,
                                        tmp_c,
                                        res_d_x,
                                        res_d_y,
                                        res_d_z,
                                        &tmp_res_c,
                                        bzla_bvprop_cond,
                                        &progress)))
        {
          goto DONE;
        }
        assert(compare_fixed_domain(mm, d_zero_bw, tmp_zero_bw));

        /**
         * ite (y[bw-1:bw-1], x << (bw - 1), 0)
         *   + ite (y[bw-2:bw-2], x << (bw-2), 0)
         *   + ...
         *   + ite (y[1:1], x << 1, 0)
         *   + ite (y[0:0], x, 0)
         *
         * Note that we only create ite for bits in y that are 1/x. Thus, we
         * don't create 'bw' adders but 'm = number of 1/x bits - 1' adders.
         */
        if (i > 0)
        {
          tmp0 = i == 1 ? &d_ite_stack.start[i - 1] : &d_add_stack.start[i - 2];
          tmp1 = tmp_ite;
          tmp_add = &d_add_stack.start[i - 1];
          if (!(res = decomp_step_binary_aux(mm,
                                             tmp0,
                                             tmp1,
                                             tmp_add,
                                             res_d_x,
                                             res_d_y,
                                             res_d_z,
                                             no_overflows,
                                             bzla_bvprop_add_aux,
                                             &progress)))
          {
            goto DONE;
          }
        }
      }

      if (no_overflows)
      {
        assert(tmp_zero);
        assert(tmp_one);
        assert(tmp_slice);

        /* upper half of multiplication result must be 0 */
        tmp = n > 1 ? &d_add_stack.start[n - 2] : &d_ite_stack.start[0];
        if (!(res = decomp_step_slice(mm,
                                      tmp,
                                      &tmp_slice,
                                      bwo - 1,
                                      bw,
                                      res_d_x,
                                      res_d_z,
                                      bzla_bvprop_slice,
                                      &progress)))
        {
          goto DONE;
        }
        assert(!no_overflows || bzla_bvdomain_get_width((*tmp)) == bwo);

        if (!(res = decomp_step_binary(mm,
                                       &tmp_slice,
                                       &tmp_zero,
                                       &tmp_one,
                                       res_d_x,
                                       res_d_y,
                                       res_d_z,
                                       bzla_bvprop_eq,
                                       &progress)))
        {
          goto DONE;
        }
        assert(compare_fixed_domain(mm, d_zero, tmp_zero));
        assert(compare_fixed_domain(mm, d_one, tmp_one));
      }
    } while (progress);

    /* Collect y bits into the result for d_y. */
    for (i = 0, n = 0; i < bw; i++)
    {
      if (i < bw - 1 && !bzla_bv_get_bit(tmp_y->lo, bw - 1 - i)
          && !bzla_bv_get_bit(tmp_y->hi, bw - 1 - i))
        continue;
      assert(n < BZLA_COUNT_STACK(d_c_stack));
      d = BZLA_PEEK_STACK(d_c_stack, n);
      assert(bzla_bvdomain_get_width(d) == 1);
      bzla_bv_set_bit(tmp_y->lo, bw - 1 - i, bzla_bv_get_bit(d->lo, 0));
      bzla_bv_set_bit(tmp_y->hi, bw - 1 - i, bzla_bv_get_bit(d->hi, 0));
      n += 1;
    }
    assert(n == BZLA_COUNT_STACK(d_c_stack));

    /* Result for d_z. */
    bzla_bvdomain_free(mm, tmp_z);
    tmp_z = new_domain(mm);
    tmp   = n > 1 ? &d_add_stack.start[n - 2] : &d_ite_stack.start[0];
    if (no_overflows)
    {
      tmp_z->lo = bzla_bv_slice(mm, (*tmp)->lo, bw - 1, 0);
      tmp_z->hi = bzla_bv_slice(mm, (*tmp)->hi, bw - 1, 0);
    }
    else
    {
      tmp_z->lo = bzla_bv_copy(mm, (*tmp)->lo);
      tmp_z->hi = bzla_bv_copy(mm, (*tmp)->hi);
    }
  }
  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(bzla_bvdomain_is_valid(mm, tmp_z));
DONE:
  if (bw > 1 && no_overflows)
  {
    lo = bzla_bv_slice(mm, tmp_x->lo, bw - 1, 0);
    hi = bzla_bv_slice(mm, tmp_x->hi, bw - 1, 0);
    bzla_bvdomain_free(mm, tmp_x);
    tmp_x     = new_domain(mm);
    tmp_x->lo = lo;
    tmp_x->hi = hi;
  }

  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

#ifndef NDEBUG
  if (d_one) bzla_bvdomain_free(mm, d_one);
  if (d_zero) bzla_bvdomain_free(mm, d_zero);
  bzla_bvdomain_free(mm, d_zero_bw);
#endif
  if (tmp_one) bzla_bvdomain_free(mm, tmp_one);
  if (tmp_zero) bzla_bvdomain_free(mm, tmp_zero);
  bzla_bvdomain_free(mm, tmp_zero_bw);
  if (tmp_slice) bzla_bvdomain_free(mm, tmp_slice);

  for (i = 0, n = BZLA_COUNT_STACK(d_c_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_c_stack));
    assert(!BZLA_EMPTY_STACK(d_shift_stack));
    assert(!BZLA_EMPTY_STACK(d_ite_stack));
    assert(!BZLA_EMPTY_STACK(shift_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_c_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_shift_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_ite_stack));
    bzla_bv_free(mm, BZLA_POP_STACK(shift_stack));
    if (i < n - 1)
    {
      assert(!BZLA_EMPTY_STACK(d_add_stack));
      bzla_bvdomain_free(mm, BZLA_POP_STACK(d_add_stack));
    }
  }
  BZLA_RELEASE_STACK(d_c_stack);
  BZLA_RELEASE_STACK(d_shift_stack);
  BZLA_RELEASE_STACK(d_ite_stack);
  BZLA_RELEASE_STACK(d_add_stack);
  BZLA_RELEASE_STACK(shift_stack);
  return res;
}

bool
bzla_bvprop_mul(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  return bzla_bvprop_mul_aux(
      mm, d_x, d_y, d_z, res_d_x, res_d_y, res_d_z, false);
}

bool
bzla_bvprop_ult(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain **res_d_x,
                BzlaBvDomain **res_d_y,
                BzlaBvDomain **res_d_z)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert(d_z);
  assert(bzla_bvdomain_is_valid(mm, d_z));

  bool progress, res;
  uint32_t bw;
  BzlaBvDomain *tmp_add_1, *tmp_add_2;
  BzlaBvDomain *tmp_cout_1, *tmp_cout_msb_1, *tmp_cout_2, *tmp_cout_msb_2;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_not_y, *tmp_z, *tmp_cout_msb;
  BzlaBvDomain *res_d_cout;
#ifndef NDEBUG
  BzlaBvDomain *d_one;
#endif
  BzlaBvDomain *tmp_one;

  res = true;

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_y));
  assert(bzla_bvdomain_get_width(d_z) == 1);

  /**
   * z_[1] = x_[bw] < y_[bw]
   *       = ~(cout(x - y))[MSB:MSB]
   *       = ~(cout(x + (~y + 1)))[MSB:MSB]
   *       = ~(cout(~y + 1)[MSB:MSB] | cout(x + (~y + 1))[MSB:MSB]) */

  tmp_x = bzla_bvdomain_new(mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new(mm, d_z->lo, d_z->hi);

  tmp_not_y  = bzla_bvdomain_new_init(mm, bw);
  tmp_add_1  = bzla_bvdomain_new_init(mm, bw);
  tmp_add_2  = bzla_bvdomain_new_init(mm, bw);
  tmp_cout_1 = bzla_bvdomain_new_init(mm, bw);
  tmp_cout_2 = bzla_bvdomain_new_init(mm, bw);

  tmp_cout_msb   = bzla_bvdomain_new_init(mm, 1);
  tmp_cout_msb_1 = bzla_bvdomain_new_init(mm, 1);
  tmp_cout_msb_2 = bzla_bvdomain_new_init(mm, 1);

#ifndef NDEBUG
  d_one     = new_domain(mm);
  d_one->lo = bzla_bv_one(mm, bw);
  d_one->hi = bzla_bv_one(mm, bw);
#endif
  tmp_one     = new_domain(mm);
  tmp_one->lo = bzla_bv_one(mm, bw);
  tmp_one->hi = bzla_bv_one(mm, bw);

  do
  {
    progress = false;

    /* not_y = ~y */
    if (!(res = decomp_step_unary(mm,
                                  &tmp_y,
                                  &tmp_not_y,
                                  res_d_x,
                                  res_d_z,
                                  bzla_bvprop_not,
                                  &progress)))
    {
      goto DONE;
    }

    /* (add_1, cout_1) = not_y + 1 */
    if (!(res = decomp_step_ternary_aux(mm,
                                        &tmp_not_y,
                                        &tmp_one,
                                        &tmp_add_1,
                                        &tmp_cout_1,
                                        res_d_x,
                                        res_d_y,
                                        res_d_z,
                                        &res_d_cout,
                                        false,
                                        bvprop_add_aux,
                                        &progress)))
    {
      goto DONE;
    }
    assert(compare_fixed_domain(mm, d_one, tmp_one));

    /* (add_2, cout_2) = x + add_1 */
    if (!(res = decomp_step_ternary_aux(mm,
                                        &tmp_x,
                                        &tmp_add_1,
                                        &tmp_add_2,
                                        &tmp_cout_2,
                                        res_d_x,
                                        res_d_y,
                                        res_d_z,
                                        &res_d_cout,
                                        false,
                                        bvprop_add_aux,
                                        &progress)))
    {
      goto DONE;
    }

    /* cout_msb_1 = cout(add_1)[MSB:MSB] */
    if (!(res = decomp_step_slice(mm,
                                  &tmp_cout_1,
                                  &tmp_cout_msb_1,
                                  bw - 1,
                                  bw - 1,
                                  res_d_x,
                                  res_d_z,
                                  bzla_bvprop_slice,
                                  &progress)))
    {
      goto DONE;
    }

    /* cout_msb_2 = cout(add_2))[MSB:MSB] */
    if (!(res = decomp_step_slice(mm,
                                  &tmp_cout_2,
                                  &tmp_cout_msb_2,
                                  bw - 1,
                                  bw - 1,
                                  res_d_x,
                                  res_d_z,
                                  bzla_bvprop_slice,
                                  &progress)))
    {
      goto DONE;
    }

    /* cout_msb = cout_msb_1 | cout_msb_2 */
    if (!(res = decomp_step_binary(mm,
                                   &tmp_cout_msb_1,
                                   &tmp_cout_msb_2,
                                   &tmp_cout_msb,
                                   res_d_x,
                                   res_d_y,
                                   res_d_z,
                                   bzla_bvprop_or,
                                   &progress)))
    {
      goto DONE;
    }

    /* z = ~cout_msb */
    if (!(res = decomp_step_unary(mm,
                                  &tmp_cout_msb,
                                  &tmp_z,
                                  res_d_x,
                                  res_d_z,
                                  bzla_bvprop_not,
                                  &progress)))
    {
      goto DONE;
    }
  } while (progress);

  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(bzla_bvdomain_is_valid(mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  bzla_bvdomain_free(mm, tmp_not_y);
  bzla_bvdomain_free(mm, tmp_add_1);
  bzla_bvdomain_free(mm, tmp_add_2);
  bzla_bvdomain_free(mm, tmp_cout_1);
  bzla_bvdomain_free(mm, tmp_cout_2);
  bzla_bvdomain_free(mm, tmp_cout_msb);
  bzla_bvdomain_free(mm, tmp_cout_msb_1);
  bzla_bvdomain_free(mm, tmp_cout_msb_2);
#ifndef NDEBUG
  bzla_bvdomain_free(mm, d_one);
#endif
  bzla_bvdomain_free(mm, tmp_one);

  return res;
}

#if 0
static bool
bvprop_udiv_old (BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_y,
                 BzlaBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (bzla_bvdomain_is_valid (mm, d_x));
  assert (d_y);
  assert (bzla_bvdomain_is_valid (mm, d_y));
  assert (d_z);
  assert (bzla_bvdomain_is_valid (mm, d_z));

  bool progress, res;
  uint32_t bw;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_z;
  BzlaBvDomain *tmp_m, *tmp_r, *tmp_eq_y, *tmp_not_eq_y, *tmp_eq_z, *tmp_ite;
  BzlaBvDomain *res_d_c;
#ifndef NDEBUG
  BzlaBvDomain *d_one, *d_zero, *d_zero_bw, *d_ones_bw;
#endif
  BzlaBvDomain *tmp_one, *tmp_zero, *tmp_zero_bw, *tmp_ones_bw;

  res = true;

  bw = bzla_bvdomain_get_width (d_x);
  assert (bw == bzla_bvdomain_get_width (d_y));
  assert (bw == bzla_bvdomain_get_width (d_z));

  /**
   * z_[bw] = x_[bw] / y_[bw]
   * <->
   * m_[bw]   = y_[bw] * z_[bw]  (no overflows!)
   * x_[bw]   = m_[bw] + r_[bw]  (no overflows!)
   * eq_y_[1] = y_[bw] = 0_[bw]
   * ite_[1]  = eq_y_[1] ? 0_[1] : 1_[1]
   * ite_[1]  = r_[bw] <_u y_[bw]
   * 1_[1]    = ~eq_y_[1] | z_[bw] == ~0_[bw]
   *
   * Note: [1] does not interpret div-by-zero as defined by the standard,
   *       but treats the operation as undefined if divisor is 0.
   *       The propagator above is fixed w.r.t. to the standardized behavior.
   */

  tmp_x = bzla_bvdomain_new (mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new (mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new (mm, d_z->lo, d_z->hi);

  tmp_m = bzla_bvdomain_new_init (mm, bw);
  tmp_r = bzla_bvdomain_new_init (mm, bw);

  tmp_eq_y     = bzla_bvdomain_new_init (mm, 1);
  tmp_not_eq_y = bzla_bvdomain_new_init (mm, 1);
  tmp_eq_z     = bzla_bvdomain_new_init (mm, 1);
  tmp_ite      = bzla_bvdomain_new_init (mm, 1);

#ifndef NDEBUG
  d_one     = new_domain (mm);
  d_one->lo = bzla_bv_one (mm, 1);
  d_one->hi = bzla_bv_one (mm, 1);

  d_zero     = new_domain (mm);
  d_zero->lo = bzla_bv_zero (mm, 1);
  d_zero->hi = bzla_bv_zero (mm, 1);

  d_zero_bw     = new_domain (mm);
  d_zero_bw->lo = bzla_bv_zero (mm, bw);
  d_zero_bw->hi = bzla_bv_zero (mm, bw);

  d_ones_bw     = new_domain (mm);
  d_ones_bw->lo = bzla_bv_ones (mm, bw);
  d_ones_bw->hi = bzla_bv_ones (mm, bw);
#endif

  tmp_one     = new_domain (mm);
  tmp_one->lo = bzla_bv_one (mm, 1);
  tmp_one->hi = bzla_bv_one (mm, 1);

  tmp_zero     = new_domain (mm);
  tmp_zero->lo = bzla_bv_zero (mm, 1);
  tmp_zero->hi = bzla_bv_zero (mm, 1);

  tmp_zero_bw     = new_domain (mm);
  tmp_zero_bw->lo = bzla_bv_zero (mm, bw);
  tmp_zero_bw->hi = bzla_bv_zero (mm, bw);

  tmp_ones_bw     = new_domain (mm);
  tmp_ones_bw->lo = bzla_bv_ones (mm, bw);
  tmp_ones_bw->hi = bzla_bv_ones (mm, bw);

  do
  {
    progress = false;

    /* m = y * z (no overflows) */
    if (!(res = decomp_step_binary_aux (mm,
                                        &tmp_y,
                                        &tmp_z,
                                        &tmp_m,
                                        res_d_x,
                                        res_d_y,
                                        res_d_z,
                                        true,
                                        bzla_bvprop_mul_aux,
                                        &progress)))
    {
      goto DONE;
    }

    /* x = m + r (no overflows) */
    if (!(res = decomp_step_ternary_aux (mm,
                                         &tmp_m,
                                         &tmp_r,
                                         &tmp_x,
                                         0,
                                         res_d_x,
                                         res_d_y,
                                         res_d_z,
                                         0,
                                         true,
                                         bvprop_add_aux,
                                         &progress)))
    {
      goto DONE;
    }

    /* eq_y = y == 0 */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_y,
                                    &tmp_zero_bw,
                                    &tmp_eq_y,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_eq,
                                    &progress)))
    {
      goto DONE;
    }
    assert (!bzla_bv_compare (d_zero_bw->lo, tmp_zero_bw->lo));
    assert (!bzla_bv_compare (d_zero_bw->hi, tmp_zero_bw->hi));

    /* ite = eq_y ? 0 : 1 */
    if (!(res = decomp_step_ternary (mm,
                                     &tmp_zero,
                                     &tmp_one,
                                     &tmp_ite,
                                     &tmp_eq_y,
                                     res_d_x,
                                     res_d_y,
                                     res_d_z,
                                     &res_d_c,
                                     bzla_bvprop_cond,
                                     &progress)))
    {
      goto DONE;
    }
    assert (!bzla_bv_compare (d_zero->lo, tmp_zero->lo));
    assert (!bzla_bv_compare (d_zero->hi, tmp_zero->hi));
    assert (!bzla_bv_compare (d_one->lo, tmp_one->lo));
    assert (!bzla_bv_compare (d_one->hi, tmp_one->hi));

    /* ite = r < y */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_r,
                                    &tmp_y,
                                    &tmp_ite,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_ult,
                                    &progress)))
    {
      goto DONE;
    }

    /* not_eq_y = ~eq */
    if (!(res = decomp_step_unary (mm,
                                   &tmp_eq_y,
                                   &tmp_not_eq_y,
                                   res_d_x,
                                   res_d_z,
                                   bzla_bvprop_not,
                                   &progress)))
    {
      goto DONE;
    }

    /* eq_z = z == ~0 */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_z,
                                    &tmp_ones_bw,
                                    &tmp_eq_z,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_eq,
                                    &progress)))
    {
      goto DONE;
    }
    assert (!bzla_bv_compare (d_ones_bw->lo, tmp_ones_bw->lo));
    assert (!bzla_bv_compare (d_ones_bw->hi, tmp_ones_bw->hi));

    /* 1 = not_eq_y | eq_z */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_not_eq_y,
                                    &tmp_eq_z,
                                    &tmp_one,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_or,
                                    &progress)))
    {
      goto DONE;
    }
    assert (!bzla_bv_compare (d_one->lo, tmp_one->lo));
    assert (!bzla_bv_compare (d_one->hi, tmp_one->hi));

  } while (progress);

  assert (bzla_bvdomain_is_valid (mm, tmp_x));
  assert (bzla_bvdomain_is_valid (mm, tmp_y));
  assert (bzla_bvdomain_is_valid (mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  bzla_bvdomain_free (mm, tmp_m);
  bzla_bvdomain_free (mm, tmp_r);
  bzla_bvdomain_free (mm, tmp_eq_y);
  bzla_bvdomain_free (mm, tmp_not_eq_y);
  bzla_bvdomain_free (mm, tmp_eq_z);
  bzla_bvdomain_free (mm, tmp_ite);
#ifndef NDEBUG
  bzla_bvdomain_free (mm, d_one);
  bzla_bvdomain_free (mm, d_zero);
  bzla_bvdomain_free (mm, d_zero_bw);
  bzla_bvdomain_free (mm, d_ones_bw);
#endif
  bzla_bvdomain_free (mm, tmp_one);
  bzla_bvdomain_free (mm, tmp_zero);
  bzla_bvdomain_free (mm, tmp_zero_bw);
  bzla_bvdomain_free (mm, tmp_ones_bw);

  return res;
}
#endif

static bool
bvprop_udiv_urem_aux(BzlaMemMgr *mm,
                     BzlaBvDomain *d_x,
                     BzlaBvDomain *d_y,
                     BzlaBvDomain *d_q, /* 0 if urem */
                     BzlaBvDomain *d_r, /* 0 if udiv */
                     BzlaBvDomain **res_d_x,
                     BzlaBvDomain **res_d_y,
                     BzlaBvDomain **res_d_q,
                     BzlaBvDomain **res_d_r)
{
  assert(mm);
  assert(d_x);
  assert(bzla_bvdomain_is_valid(mm, d_x));
  assert(d_y);
  assert(bzla_bvdomain_is_valid(mm, d_y));
  assert((d_r && !d_q) || (!d_r && d_q));
  assert(!d_q || bzla_bvdomain_is_valid(mm, d_q));
  assert(!d_r || bzla_bvdomain_is_valid(mm, d_r));
  assert(res_d_x);
  assert(res_d_y);
  assert(!d_q || res_d_q);
  assert(!d_r || res_d_r);

  /* q_[bw] = x_[bw] / y_[bw] with remainer r_[bw]
   * ---------------------------------------------
   *
   * r_init := 0_[bw] for udiv
   * q_init := 0_[bw] for urem
   * for i in bw-1...0:
   *   if i == bw-1:
   *     r_i = r_init << 1
   *   else:
   *     r_i = r_i-1 << 1
   *   r_i[0]     := x[i]
   *   ult_i      = r_i < y
   *   not_ult_i  = ~ult_i
   *   ite_r_i    = not_ult_i ? r_i - y : r_i
   *   q[i]       = not_ult_i ? 1_[1] : 0_[1]
   *
   * division by zero:
   *
   * udiv: x / 0 = ~0
   * ----------------
   * eq_y_zero     = y == 0
   * not_eq_y_zero = ~eq_y_zero
   * eq_q_ones     = q = ~0
   * 1_[1]         = not_eq_y_zero | eq_q_ones
   *
   * urem: x / 0 = x
   * ---------------
   * eq_y_zero     = y == 0
   * not_eq_y_zero = ~eq_y_zero
   * eq_r_ones     = r = x
   * 1_[1]         = not_eq_y_zero | eq_r_ones
   */

  bool res, progress;
  uint32_t i, bw, n;
  BzlaBvDomain *d;
#ifndef NDEBUG
  BzlaBvDomain *d_one, *d_zero, *d_zero_bw, *d_one_bw, *d_ones_bw;
#endif
  BzlaBvDomain *tmp_one, *tmp_zero, *tmp_zero_bw, *tmp_one_bw, *tmp_ones_bw;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_q;
  BzlaBvDomain *tmp_not_y, *tmp_neg_y;
  BzlaBvDomain *tmp_eq_y_zero, *tmp_not_eq_y_zero;
  BzlaBvDomain *tmp_r_init, *tmp_r_int;
  BzlaBvDomain *tmp_res_x, *tmp_res_y, *tmp_res_z, *tmp_res_c;
  BzlaBvDomain **tmp_r, **tmp_r_prev, **tmp_r_next, **tmp_r_shift;
  BzlaBvDomain **tmp_r_slice;
  BzlaBvDomain **tmp_sub, **tmp_ult;
  BzlaBvDomain **tmp_x_bit, **tmp_q_bit;
  BzlaBvDomainPtrStack d_x_stack, d_q_stack;
  BzlaBvDomainPtrStack d_r_stack, d_r_prev_stack;
  BzlaBvDomainPtrStack d_r_shift_stack, d_r_slice_stack, d_r_shift_slice_stack;
  BzlaBvDomainPtrStack d_sub_stack, d_ult_stack;
  BzlaBitVector *one;

  progress = false;

  BZLA_INIT_STACK(mm, d_r_stack);
  BZLA_INIT_STACK(mm, d_r_prev_stack);
  BZLA_INIT_STACK(mm, d_r_shift_stack);
  BZLA_INIT_STACK(mm, d_ult_stack);
  BZLA_INIT_STACK(mm, d_x_stack);
  BZLA_INIT_STACK(mm, d_r_slice_stack);
  BZLA_INIT_STACK(mm, d_r_shift_slice_stack);
  BZLA_INIT_STACK(mm, d_q_stack);
  BZLA_INIT_STACK(mm, d_sub_stack);

  bw = bzla_bvdomain_get_width(d_x);
  assert(bw == bzla_bvdomain_get_width(d_y));
  assert(!d_q || bw == bzla_bvdomain_get_width(d_q));
  assert(!d_r || bw == bzla_bvdomain_get_width(d_r));

  one = bzla_bv_one(mm, bw);

#ifndef NDEBUG
  d_zero        = new_domain(mm);
  d_zero->lo    = bzla_bv_zero(mm, 1);
  d_zero->hi    = bzla_bv_zero(mm, 1);
  d_zero_bw     = new_domain(mm);
  d_zero_bw->lo = bzla_bv_zero(mm, bw);
  d_zero_bw->hi = bzla_bv_zero(mm, bw);
  d_one         = new_domain(mm);
  d_one->lo     = bzla_bv_one(mm, 1);
  d_one->hi     = bzla_bv_one(mm, 1);
  d_one_bw      = new_domain(mm);
  d_one_bw->lo  = bzla_bv_one(mm, bw);
  d_one_bw->hi  = bzla_bv_one(mm, bw);
  d_ones_bw     = new_domain(mm);
  d_ones_bw->lo = bzla_bv_ones(mm, bw);
  d_ones_bw->hi = bzla_bv_ones(mm, bw);
#endif
  tmp_zero        = new_domain(mm);
  tmp_zero->lo    = bzla_bv_zero(mm, 1);
  tmp_zero->hi    = bzla_bv_zero(mm, 1);
  tmp_zero_bw     = new_domain(mm);
  tmp_zero_bw->lo = bzla_bv_zero(mm, bw);
  tmp_zero_bw->hi = bzla_bv_zero(mm, bw);
  tmp_one         = new_domain(mm);
  tmp_one->lo     = bzla_bv_one(mm, 1);
  tmp_one->hi     = bzla_bv_one(mm, 1);
  tmp_one_bw      = new_domain(mm);
  tmp_one_bw->lo  = bzla_bv_one(mm, bw);
  tmp_one_bw->hi  = bzla_bv_one(mm, bw);
  tmp_ones_bw     = new_domain(mm);
  tmp_ones_bw->lo = bzla_bv_ones(mm, bw);
  tmp_ones_bw->hi = bzla_bv_ones(mm, bw);

  tmp_x     = bzla_bvdomain_new_init(mm, bw);
  tmp_y     = bzla_bvdomain_new(mm, d_y->lo, d_y->hi);
  tmp_not_y = bzla_bvdomain_new_init(mm, bw);
  tmp_neg_y = bzla_bvdomain_new_init(mm, bw);

  if (d_q)
  {
    tmp_q = bzla_bvdomain_new(mm, d_q->lo, d_q->hi);
  }

  tmp_eq_y_zero     = bzla_bvdomain_new_init(mm, 1);
  tmp_not_eq_y_zero = bzla_bvdomain_new_init(mm, 1);

  /* r_init := 0_[bw] */
  tmp_r_init     = new_domain(mm);
  tmp_r_init->lo = bzla_bv_zero(mm, bw);
  tmp_r_init->hi = bzla_bv_zero(mm, bw);

  /* intermediate remainder result for zero division check */
  tmp_r_int = bzla_bvdomain_new_init(mm, bw);

  for (i = 0; i < bw; i++)
  {
    n = bw - 1 - i;
    /* slice x into bw bits */
    d     = new_domain(mm);
    d->lo = bzla_bv_slice(mm, d_x->lo, n, n);
    d->hi = bzla_bv_slice(mm, d_x->hi, n, n);
    BZLA_PUSH_STACK(d_x_stack, d);
    /* slice q into bw bits */
    if (d_q)
    {
      d     = new_domain(mm);
      d->lo = bzla_bv_slice(mm, tmp_q->lo, n, n);
      d->hi = bzla_bv_slice(mm, tmp_q->hi, n, n);
      BZLA_PUSH_STACK(d_q_stack, d);
    }
    /* domains for remainder r */
    d = bzla_bvdomain_new_init(mm, bw);
    BZLA_PUSH_STACK(d_r_stack, d);
    /* domains for prev remainder r */
    if (d_r && i == bw - 1)
    {
      d = bzla_bvdomain_copy(mm, d_r);
    }
    else
    {
      d = bzla_bvdomain_new_init(mm, bw);
    }
    BZLA_PUSH_STACK(d_r_prev_stack, d);
    /* ult propagators */
    d = bzla_bvdomain_new_init(mm, 1);
    BZLA_PUSH_STACK(d_ult_stack, d);
    if (bw > 1)
    {
      /* shift propagators for remainder r */
      d = bzla_bvdomain_new_init(mm, bw);
      BZLA_PUSH_STACK(d_r_shift_stack, d);
      /* r slice propagators */
      d = bzla_bvdomain_new_init(mm, bw - 1);
      BZLA_PUSH_STACK(d_r_slice_stack, d);
      /* r_shift slice propagators */
      d = bzla_bvdomain_new_init(mm, bw - 1);
      BZLA_PUSH_STACK(d_r_shift_slice_stack, d);
    }
    /* sub propagators */
    d = bzla_bvdomain_new_init(mm, bw);
    BZLA_PUSH_STACK(d_sub_stack, d);
  }

  BVPROP_LOG("\n############################\n");
  BVPROP_LOG_DOMAIN(mm, d_x);
  BVPROP_LOG_DOMAIN(mm, d_y);
  if (d_q)
  {
    BVPROP_LOG_DOMAIN(mm, d_q);
  }
  if (d_r)
  {
    BVPROP_LOG_DOMAIN(mm, d_r);
  }
  BVPROP_LOG("############################\n");
  do
  {
    progress = false;

    for (i = 0; i < bw; i++)
    {
      if (bw > 1)
      {
        /* if i == 0: r_i_shift = r_init << 1
         * else:      r_i_shift = r_i-1  << 1
         * Note: index bw - 1 is at stack index 0 */
        tmp_r_shift = &d_r_shift_stack.start[i];
        if (i == 0)
        {
          tmp_r_prev = &tmp_r_init;
          BVPROP_LOG("1 -----------------\n");
          BVPROP_LOG("r_i_shift = r_prev << 1\n");
          BVPROP_LOG_DOMAIN(mm, *tmp_r_prev);
          BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
          if (!(res = decomp_step_binary(mm,
                                         tmp_r_prev,
                                         tmp_r_shift,
                                         &tmp_one,
                                         &tmp_res_x,
                                         &tmp_res_y,
                                         &tmp_res_z,
                                         bzla_bvprop_eq,
                                         &progress)))
          {
            goto DONE;
          }
          assert(compare_fixed_domain(mm, tmp_one, d_one));
          BVPROP_LOG("...................\n");
          BVPROP_LOG_DOMAIN(mm, *tmp_r_prev);
          BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
        }
        else
        {
          tmp_r_prev = &d_r_prev_stack.start[i - 1];
          BVPROP_LOG("1 -----------------\n");
          BVPROP_LOG("r_i_shift = r_prev << 1\n");
          BVPROP_LOG_DOMAIN(mm, *tmp_r_prev);
          BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
          if (!(res = decomp_step_shiftc(mm,
                                         tmp_r_prev,
                                         tmp_r_shift,
                                         one,
                                         &tmp_res_x,
                                         &tmp_res_z,
                                         bzla_bvprop_sll_const,
                                         &progress)))
          {
            goto DONE;
          }
          BVPROP_LOG("...................\n");
          BVPROP_LOG_DOMAIN(mm, *tmp_r_prev);
          BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
        }
      }
      assert(compare_fixed_domain(mm, d_zero_bw, tmp_r_init));

      tmp_r = &d_r_stack.start[i];
      if (bw > 1)
      {
        /* r_i_slice = r_i[bw-1:1] */
        tmp_r_slice = &d_r_slice_stack.start[i];
        BVPROP_LOG("2 -----------------\n");
        BVPROP_LOG("r_i_slice = r_i[bw-1:1]\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_slice);
        if (!(res = decomp_step_slice(mm,
                                      tmp_r,
                                      tmp_r_slice,
                                      bw - 1,
                                      1,
                                      &tmp_res_x,
                                      &tmp_res_z,
                                      bzla_bvprop_slice,
                                      &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("...................\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_slice);

        /* r_i_shift_slice = r_i_shift[bw-1:1] */
        BVPROP_LOG("3 -----------------\n");
        BVPROP_LOG("r_i_slice = r_shift_i[bw-1:1]\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_slice);
        if (!(res = decomp_step_slice(mm,
                                      tmp_r_shift,
                                      tmp_r_slice,
                                      bw - 1,
                                      1,
                                      &tmp_res_x,
                                      &tmp_res_z,
                                      bzla_bvprop_slice,
                                      &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("...................\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r_shift);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_slice);
      }

      /* r_i[0] = x[i] */
      tmp_x_bit = &d_x_stack.start[i];
      BVPROP_LOG("5 -----------------\n");
      BVPROP_LOG("r_i[0] = x[i]\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, *tmp_x_bit);
      if (!(res = decomp_step_slice(mm,
                                    tmp_r,
                                    tmp_x_bit,
                                    0,
                                    0,
                                    &tmp_res_x,
                                    &tmp_res_z,
                                    bzla_bvprop_slice,
                                    &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("...................\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, *tmp_x_bit);

      if (d_r) /* we only need this for urem */
      {
        /* x_bit = x[i] */
        n = bw - i - 1;
        BVPROP_LOG("14 ---------------------------\n");
        BVPROP_LOG("x_bit = x[i]\n");
        BVPROP_LOG_DOMAIN(mm, tmp_x);
        BVPROP_LOG_DOMAIN(mm, *tmp_x_bit);
        if (!(res = decomp_step_slice(mm,
                                      &tmp_x,
                                      tmp_x_bit,
                                      n,
                                      n,
                                      &tmp_res_x,
                                      &tmp_res_z,
                                      bzla_bvprop_slice,
                                      &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, tmp_x);
        BVPROP_LOG_DOMAIN(mm, *tmp_x_bit);
      }

      /* ult_i = r_i < y */
      tmp_ult = &d_ult_stack.start[i];
      BVPROP_LOG("6 ----------------------------\n");
      BVPROP_LOG("ult = r < y\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, *tmp_ult);
      if (!(res = decomp_step_binary(mm,
                                     tmp_r,
                                     &tmp_y,
                                     tmp_ult,
                                     &tmp_res_x,
                                     &tmp_res_y,
                                     &tmp_res_z,
                                     bzla_bvprop_ult,
                                     &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, *tmp_ult);

      /* not_y = ~y */
      BVPROP_LOG("7 ----------------------------\n");
      BVPROP_LOG("not_y = ~y\n");
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, tmp_not_y);
      if (!(res = decomp_step_unary(mm,
                                    &tmp_y,
                                    &tmp_not_y,
                                    &tmp_res_x,
                                    &tmp_res_z,
                                    bzla_bvprop_not,
                                    &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, tmp_not_y);

      /* neg_y = not_y + 1 */
      BVPROP_LOG("8 ----------------------------\n");
      BVPROP_LOG("neq_y = not_y + 1\n");
      BVPROP_LOG_DOMAIN(mm, tmp_not_y);
      BVPROP_LOG_DOMAIN(mm, tmp_one_bw);
      BVPROP_LOG_DOMAIN(mm, tmp_neg_y);
      if (!(res = decomp_step_binary(mm,
                                     &tmp_not_y,
                                     &tmp_one_bw,
                                     &tmp_neg_y,
                                     &tmp_res_x,
                                     &tmp_res_y,
                                     &tmp_res_z,
                                     bzla_bvprop_add,
                                     &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, tmp_not_y);
      BVPROP_LOG_DOMAIN(mm, tmp_one_bw);
      BVPROP_LOG_DOMAIN(mm, tmp_neg_y);
      assert(compare_fixed_domain(mm, d_one_bw, tmp_one_bw));

      /* sub = r_i + neg_y */
      tmp_sub = &d_sub_stack.start[i];
      BVPROP_LOG("9 ----------------------------\n");
      BVPROP_LOG("sub = r + neg_y\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, tmp_neg_y);
      BVPROP_LOG_DOMAIN(mm, *tmp_sub);
      if (!(res = decomp_step_binary(mm,
                                     tmp_r,
                                     &tmp_neg_y,
                                     tmp_sub,
                                     &tmp_res_x,
                                     &tmp_res_y,
                                     &tmp_res_z,
                                     bzla_bvprop_add,
                                     &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, *tmp_r);
      BVPROP_LOG_DOMAIN(mm, tmp_neg_y);
      BVPROP_LOG_DOMAIN(mm, *tmp_sub);

      /* eq_y_zero = y == 0 */
      BVPROP_LOG("10 ---------------------------\n");
      BVPROP_LOG("eq_y_zero = y == 0\n");
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, tmp_zero_bw);
      BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);
      if (!(res = decomp_step_binary(mm,
                                     &tmp_y,
                                     &tmp_zero_bw,
                                     &tmp_eq_y_zero,
                                     &tmp_res_x,
                                     &tmp_res_y,
                                     &tmp_res_z,
                                     bzla_bvprop_eq,
                                     &progress)))
      {
        goto DONE;
      }
      assert(compare_fixed_domain(mm, d_zero_bw, tmp_zero_bw));
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, tmp_y);
      BVPROP_LOG_DOMAIN(mm, tmp_zero_bw);
      BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);

      /* we only need this for urem, for udiv we don't care about the
       * div-by-zero check for the remainder */
      if (d_r && i == bw - 1)
      {
        /* r_int = eq_y_zero ? x : sub */
        BVPROP_LOG("11 ----------------------------\n");
        BVPROP_LOG("r_int = y = 0 ? x : sub\n");
        BVPROP_LOG_DOMAIN(mm, tmp_x);
        BVPROP_LOG_DOMAIN(mm, *tmp_sub);
        BVPROP_LOG_DOMAIN(mm, tmp_r_int);
        BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);
        if (!(res = decomp_step_ternary(mm,
                                        &tmp_x,
                                        tmp_sub,
                                        &tmp_r_int,
                                        &tmp_eq_y_zero,
                                        &tmp_res_x,
                                        &tmp_res_y,
                                        &tmp_res_z,
                                        &tmp_res_c,
                                        bzla_bvprop_cond,
                                        &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, tmp_x);
        BVPROP_LOG_DOMAIN(mm, *tmp_sub);
        BVPROP_LOG_DOMAIN(mm, tmp_r_int);
        BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);

        /* r_next = ult_i ? r_i : r_int */
        tmp_r_next = &d_r_prev_stack.start[i];
        BVPROP_LOG("12 ----------------------------\n");
        BVPROP_LOG("r_next = ult ? r : r_int\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, tmp_r_int);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_next);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
        if (!(res = decomp_step_ternary(mm,
                                        tmp_r,
                                        &tmp_r_int,
                                        tmp_r_next,
                                        tmp_ult,
                                        &tmp_res_x,
                                        &tmp_res_y,
                                        &tmp_res_z,
                                        &tmp_res_c,
                                        bzla_bvprop_cond,
                                        &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, tmp_r_int);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_next);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
      }
      else
      {
        /* next_r_prev = ult_i ? r_i : r_i - y
         * ->
         * next_r_prev = ult_i ? r_i : sub       */
        tmp_r_next = &d_r_prev_stack.start[i];
        BVPROP_LOG("13 ----------------------------\n");
        BVPROP_LOG("r_next = ult ? r : sub\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, *tmp_sub);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_next);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
        if (!(res = decomp_step_ternary(mm,
                                        tmp_r,
                                        tmp_sub,
                                        tmp_r_next,
                                        tmp_ult,
                                        &tmp_res_x,
                                        &tmp_res_y,
                                        &tmp_res_z,
                                        &tmp_res_c,
                                        bzla_bvprop_cond,
                                        &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, *tmp_r);
        BVPROP_LOG_DOMAIN(mm, *tmp_sub);
        BVPROP_LOG_DOMAIN(mm, *tmp_r_next);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
      }

      BVPROP_LOG("15 ---------------------------\n");
      BVPROP_LOG("not_eq_y_zero = ~eq_y_zero\n");
      BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);
      BVPROP_LOG_DOMAIN(mm, tmp_not_eq_y_zero);
      /* not_eq_y_zero = ~eq_y_zero */
      if (!(res = decomp_step_unary(mm,
                                    &tmp_eq_y_zero,
                                    &tmp_not_eq_y_zero,
                                    &tmp_res_x,
                                    &tmp_res_z,
                                    bzla_bvprop_not,
                                    &progress)))
      {
        goto DONE;
      }
      BVPROP_LOG("..............................\n");
      BVPROP_LOG_DOMAIN(mm, tmp_eq_y_zero);
      BVPROP_LOG_DOMAIN(mm, tmp_not_eq_y_zero);

      /* we only need this for udiv, we don't care about the quotient for
       * urem */
      if (d_q)
      {
        /* q_bit = q[i] */
        n         = bw - i - 1;
        tmp_q_bit = &d_q_stack.start[i];
        BVPROP_LOG("14 ---------------------------\n");
        BVPROP_LOG("q_bit = q[i]\n");
        BVPROP_LOG_DOMAIN(mm, tmp_q);
        BVPROP_LOG_DOMAIN(mm, *tmp_q_bit);
        if (!(res = decomp_step_slice(mm,
                                      &tmp_q,
                                      tmp_q_bit,
                                      n,
                                      n,
                                      &tmp_res_x,
                                      &tmp_res_z,
                                      bzla_bvprop_slice,
                                      &progress)))
        {
          goto DONE;
        }
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, tmp_q);
        BVPROP_LOG_DOMAIN(mm, *tmp_q_bit);

        /* q_bit = ult_i ? 0_[1] : 1_[1] */
        BVPROP_LOG("17 ---------------------------\n");
        BVPROP_LOG("q_bit = ult ? 0 : 1\n");
        BVPROP_LOG_DOMAIN(mm, tmp_zero);
        BVPROP_LOG_DOMAIN(mm, tmp_one);
        BVPROP_LOG_DOMAIN(mm, *tmp_q_bit);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
        if (!(res = decomp_step_ternary(mm,
                                        &tmp_zero,
                                        &tmp_one,
                                        tmp_q_bit,
                                        tmp_ult,
                                        &tmp_res_x,
                                        &tmp_res_y,
                                        &tmp_res_z,
                                        &tmp_res_c,
                                        bzla_bvprop_cond,
                                        &progress)))
        {
          goto DONE;
        }
        assert(compare_fixed_domain(mm, d_zero, tmp_zero));
        assert(compare_fixed_domain(mm, d_one, tmp_one));
        BVPROP_LOG("..............................\n");
        BVPROP_LOG_DOMAIN(mm, tmp_zero);
        BVPROP_LOG_DOMAIN(mm, tmp_one);
        BVPROP_LOG_DOMAIN(mm, *tmp_q_bit);
        BVPROP_LOG_DOMAIN(mm, *tmp_ult);
      }
    }
  } while (progress);

  /* Collect x bits into the result for d_x. */
  for (i = 0; i < bw; i++)
  {
    n = bw - 1 - i;
    d = BZLA_PEEK_STACK(d_x_stack, i);
    assert(bzla_bvdomain_get_width(d) == 1);
    bzla_bv_set_bit(tmp_x->lo, n, bzla_bv_get_bit(d->lo, 0));
    bzla_bv_set_bit(tmp_x->hi, n, bzla_bv_get_bit(d->hi, 0));
  }

  assert(bzla_bvdomain_is_valid(mm, tmp_x));
  assert(bzla_bvdomain_is_valid(mm, tmp_y));
  assert(!d_q || bzla_bvdomain_is_valid(mm, tmp_q));
  assert(!d_r || bzla_bvdomain_is_valid(mm, d_r_prev_stack.start[bw - 1]));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  if (res_d_q) *res_d_q = tmp_q;
  if (res_d_r) *res_d_r = bzla_bvdomain_copy(mm, d_r_prev_stack.start[bw - 1]);

  bzla_bv_free(mm, one);

  bzla_bvdomain_free(mm, tmp_not_y);
  bzla_bvdomain_free(mm, tmp_neg_y);
  bzla_bvdomain_free(mm, tmp_r_init);
  bzla_bvdomain_free(mm, tmp_r_int);
  bzla_bvdomain_free(mm, tmp_eq_y_zero);
  bzla_bvdomain_free(mm, tmp_not_eq_y_zero);

#ifndef NDEBUG
  bzla_bvdomain_free(mm, d_one);
  bzla_bvdomain_free(mm, d_zero);
  bzla_bvdomain_free(mm, d_zero_bw);
  bzla_bvdomain_free(mm, d_one_bw);
  bzla_bvdomain_free(mm, d_ones_bw);
#endif
  bzla_bvdomain_free(mm, tmp_one);
  bzla_bvdomain_free(mm, tmp_zero);
  bzla_bvdomain_free(mm, tmp_zero_bw);
  bzla_bvdomain_free(mm, tmp_one_bw);
  bzla_bvdomain_free(mm, tmp_ones_bw);

  for (i = 0, n = BZLA_COUNT_STACK(d_r_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_x_stack));
    assert(!d_q || !BZLA_EMPTY_STACK(d_q_stack));
    assert(!BZLA_EMPTY_STACK(d_r_stack));
    assert(!BZLA_EMPTY_STACK(d_r_prev_stack));
    assert(!BZLA_EMPTY_STACK(d_sub_stack));
    assert(!BZLA_EMPTY_STACK(d_ult_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_x_stack));
    if (d_q) bzla_bvdomain_free(mm, BZLA_POP_STACK(d_q_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_r_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_r_prev_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_sub_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_ult_stack));
  }
  for (i = 0, n = BZLA_COUNT_STACK(d_r_slice_stack); i < n; i++)
  {
    assert(!BZLA_EMPTY_STACK(d_r_shift_stack));
    assert(!BZLA_EMPTY_STACK(d_r_slice_stack));
    assert(!BZLA_EMPTY_STACK(d_r_shift_slice_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_r_shift_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_r_slice_stack));
    bzla_bvdomain_free(mm, BZLA_POP_STACK(d_r_shift_slice_stack));
  }
  assert(BZLA_EMPTY_STACK(d_r_stack));
  BZLA_RELEASE_STACK(d_r_stack);
  assert(BZLA_EMPTY_STACK(d_r_shift_stack));
  BZLA_RELEASE_STACK(d_r_shift_stack);
  assert(BZLA_EMPTY_STACK(d_r_slice_stack));
  BZLA_RELEASE_STACK(d_r_slice_stack);
  assert(BZLA_EMPTY_STACK(d_r_shift_slice_stack));
  BZLA_RELEASE_STACK(d_r_shift_slice_stack);
  assert(BZLA_EMPTY_STACK(d_r_prev_stack));
  BZLA_RELEASE_STACK(d_r_prev_stack);
  assert(BZLA_EMPTY_STACK(d_x_stack));
  BZLA_RELEASE_STACK(d_x_stack);
  assert(BZLA_EMPTY_STACK(d_q_stack));
  BZLA_RELEASE_STACK(d_q_stack);
  assert(BZLA_EMPTY_STACK(d_sub_stack));
  BZLA_RELEASE_STACK(d_sub_stack);
  assert(BZLA_EMPTY_STACK(d_ult_stack));
  BZLA_RELEASE_STACK(d_ult_stack);

  BVPROP_LOG("res: %d ############################\n", res);
  BVPROP_LOG_DOMAIN(mm, *res_d_x);
  BVPROP_LOG_DOMAIN(mm, *res_d_y);
  if (res_d_q)
  {
    BVPROP_LOG_DOMAIN(mm, *res_d_q);
  }
  if (res_d_r)
  {
    BVPROP_LOG_DOMAIN(mm, *res_d_r);
  }
  return res;
}

bool
bzla_bvprop_udiv(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_y,
                 BzlaBvDomain **res_d_z)
{
  return bvprop_udiv_urem_aux(
      mm, d_x, d_y, d_z, 0, res_d_x, res_d_y, res_d_z, 0);
}

bool
bzla_bvprop_urem(BzlaMemMgr *mm,
                 BzlaBvDomain *d_x,
                 BzlaBvDomain *d_y,
                 BzlaBvDomain *d_z,
                 BzlaBvDomain **res_d_x,
                 BzlaBvDomain **res_d_y,
                 BzlaBvDomain **res_d_z)
{
  return bvprop_udiv_urem_aux(
      mm, d_x, d_y, 0, d_z, res_d_x, res_d_y, 0, res_d_z);
}

#if 0
bool
bzla_bvprop_urem (BzlaMemMgr *mm,
                  BzlaBvDomain *d_x,
                  BzlaBvDomain *d_y,
                  BzlaBvDomain *d_z,
                  BzlaBvDomain **res_d_x,
                  BzlaBvDomain **res_d_y,
                  BzlaBvDomain **res_d_z)
{
  assert (mm);
  assert (d_x);
  assert (bzla_bvdomain_is_valid (mm, d_x));
  assert (d_y);
  assert (bzla_bvdomain_is_valid (mm, d_y));
  assert (d_z);
  assert (bzla_bvdomain_is_valid (mm, d_z));

  bool progress, res;
  uint32_t bw;
  BzlaBvDomain *tmp_x, *tmp_y, *tmp_z;
  BzlaBvDomain *tmp_m, *tmp_q, *tmp_eq_y, *tmp_not_eq_y, *tmp_eq_z, *tmp_ite;
  BzlaBvDomain *res_d_c;
#ifndef NDEBUG
  BzlaBvDomain *d_one, *d_zero, *d_zero_bw;
#endif
  BzlaBvDomain *tmp_one, *tmp_zero, *tmp_zero_bw;

  res = true;

  bw = bzla_bvdomain_get_width (d_x);
  assert (bw == bzla_bvdomain_get_width (d_y));
  assert (bw == bzla_bvdomain_get_width (d_z));

  /**
   * z_[bw] = x_[bw] / y_[bw]
   * <->
   * m_[bw]   = y_[bw] * q_[bw]  (no overflows!)
   * x_[bw]   = m_[bw] + z_[bw]  (no overflows!)
   * eq_y_[1] = y_[bw] = 0_[bw]
   * ite_[1]  = eq_y_[1] ? 0_[1] : 1_[1]
   * ite_[1]  = z_[bw] <_u y_[bw]
   * 1_[1]    = ~eq_[1] | z_[bw] == x_[bw]
   *
   * Note: [1] does not interpret div-by-zero as defined by the standard,
   *       but treats the operation as undefined if divisor is 0.
   *       The propagator above is fixed w.r.t. to the standardized behavior.
   */

  tmp_x = bzla_bvdomain_new (mm, d_x->lo, d_x->hi);
  tmp_y = bzla_bvdomain_new (mm, d_y->lo, d_y->hi);
  tmp_z = bzla_bvdomain_new (mm, d_z->lo, d_z->hi);

  tmp_m = bzla_bvdomain_new_init (mm, bw);
  tmp_q = bzla_bvdomain_new_init (mm, bw);

  tmp_eq_y     = bzla_bvdomain_new_init (mm, 1);
  tmp_not_eq_y = bzla_bvdomain_new_init (mm, 1);
  tmp_eq_z     = bzla_bvdomain_new_init (mm, 1);
  tmp_ite      = bzla_bvdomain_new_init (mm, 1);

#ifndef NDEBUG
  d_one     = new_domain (mm);
  d_one->lo = bzla_bv_one (mm, 1);
  d_one->hi = bzla_bv_one (mm, 1);

  d_zero     = new_domain (mm);
  d_zero->lo = bzla_bv_zero (mm, 1);
  d_zero->hi = bzla_bv_zero (mm, 1);

  d_zero_bw     = new_domain (mm);
  d_zero_bw->lo = bzla_bv_zero (mm, bw);
  d_zero_bw->hi = bzla_bv_zero (mm, bw);
#endif
  tmp_one     = new_domain (mm);
  tmp_one->lo = bzla_bv_one (mm, 1);
  tmp_one->hi = bzla_bv_one (mm, 1);

  tmp_zero     = new_domain (mm);
  tmp_zero->lo = bzla_bv_zero (mm, 1);
  tmp_zero->hi = bzla_bv_zero (mm, 1);

  tmp_zero_bw     = new_domain (mm);
  tmp_zero_bw->lo = bzla_bv_zero (mm, bw);
  tmp_zero_bw->hi = bzla_bv_zero (mm, bw);

  do
  {
    progress = false;

    /* m = y * q (no overflows) */
    if (!(res = decomp_step_binary_aux (mm,
                                        &tmp_y,
                                        &tmp_q,
                                        &tmp_m,
                                        res_d_x,
                                        res_d_y,
                                        res_d_z,
                                        true,
                                        bzla_bvprop_mul_aux,
                                        &progress)))
    {
      goto DONE;
    }

    /* x = m + z (no overflows) */
    if (!(res = decomp_step_ternary_aux (mm,
                                         &tmp_m,
                                         &tmp_z,
                                         &tmp_x,
                                         0,
                                         res_d_x,
                                         res_d_y,
                                         res_d_z,
                                         0,
                                         true,
                                         bvprop_add_aux,
                                         &progress)))
    {
      goto DONE;
    }

    /* eq_y = y == 0 */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_y,
                                    &tmp_zero_bw,
                                    &tmp_eq_y,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_eq,
                                    &progress)))
    {
      goto DONE;
    }
    assert (compare_fixed_domain (mm, d_zero_bw, tmp_zero_bw));

    /* ite = eq_y ? 0 : 1 */
    if (!(res = decomp_step_ternary (mm,
                                     &tmp_zero,
                                     &tmp_one,
                                     &tmp_ite,
                                     &tmp_eq_y,
                                     res_d_x,
                                     res_d_y,
                                     res_d_z,
                                     &res_d_c,
                                     bzla_bvprop_cond,
                                     &progress)))
    {
      goto DONE;
    }
    assert (compare_fixed_domain (mm, d_zero, tmp_zero));
    assert (compare_fixed_domain (mm, d_one, tmp_one));

    /* ite = z < y */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_z,
                                    &tmp_y,
                                    &tmp_ite,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_ult,
                                    &progress)))
    {
      goto DONE;
    }

    /* not_eq_y = ~eq */
    if (!(res = decomp_step_unary (mm,
                                   &tmp_eq_y,
                                   &tmp_not_eq_y,
                                   res_d_x,
                                   res_d_z,
                                   bzla_bvprop_not,
                                   &progress)))
    {
      goto DONE;
    }

    /* eq_z = z == x */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_z,
                                    &tmp_x,
                                    &tmp_eq_z,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_eq,
                                    &progress)))
    {
      goto DONE;
    }

    /* 1 = not_eq_y | eq_z */
    if (!(res = decomp_step_binary (mm,
                                    &tmp_not_eq_y,
                                    &tmp_eq_z,
                                    &tmp_one,
                                    res_d_x,
                                    res_d_y,
                                    res_d_z,
                                    bzla_bvprop_or,
                                    &progress)))
    {
      goto DONE;
    }
    assert (compare_fixed_domain (mm, d_one, tmp_one));

  } while (progress);

  assert (bzla_bvdomain_is_valid (mm, tmp_x));
  assert (bzla_bvdomain_is_valid (mm, tmp_y));
  assert (bzla_bvdomain_is_valid (mm, tmp_z));

DONE:
  *res_d_x = tmp_x;
  *res_d_y = tmp_y;
  *res_d_z = tmp_z;

  bzla_bvdomain_free (mm, tmp_m);
  bzla_bvdomain_free (mm, tmp_q);
  bzla_bvdomain_free (mm, tmp_eq_y);
  bzla_bvdomain_free (mm, tmp_not_eq_y);
  bzla_bvdomain_free (mm, tmp_eq_z);
  bzla_bvdomain_free (mm, tmp_ite);
#ifndef NDEBUG
  bzla_bvdomain_free (mm, d_one);
  bzla_bvdomain_free (mm, d_zero);
  bzla_bvdomain_free (mm, d_zero_bw);
#endif
  bzla_bvdomain_free (mm, tmp_one);
  bzla_bvdomain_free (mm, tmp_zero);
  bzla_bvdomain_free (mm, tmp_zero_bw);

  return res;
}
#endif

/*----------------------------------------------------------------------------*/
