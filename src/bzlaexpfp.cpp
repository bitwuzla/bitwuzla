/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

extern "C" {

#include "bzlaexp.h"

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_fp_rne(Bzla *bzla)
{
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rna(Bzla *bzla)
{
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtp(Bzla *bzla)
{
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtn(Bzla *bzla)
{
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtz(Bzla *bzla)
{
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_pos_zero(Bzla *bzla, uint32_t eb, uint32_t sb)
{
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg_zero(Bzla *bzla, uint32_t eb, uint32_t sb)
{
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_pos_inf(Bzla *bzla, uint32_t eb, uint32_t sb)
{
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg_inf(Bzla *bzla, uint32_t eb, uint32_t sb)
{
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_nan(Bzla *bzla, uint32_t eb, uint32_t sb)
{
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_const(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_abs(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_normal(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_subnormal(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_zero(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_inf(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_nan(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_neg(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_pos(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  /// FP STUB
  (void) exp;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_leq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_geq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_gt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_round_to_int(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  assert(bzla == bzla_node_real_addr(e3)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  (void) e3;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp(Bzla *bzla, BzlaNode *exp, uint32_t eb, uint32_t sb)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) exp;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_signed(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, uint32_t eb, uint32_t sb)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_unsigned(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, uint32_t eb, uint32_t sb)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_real(
    Bzla *bzla, BzlaNode *exp, const char *real, uint32_t eb, uint32_t sb)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(real);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) exp;
  (void) real;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}
}
