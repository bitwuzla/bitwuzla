/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLACONSUTILS_H_INCLUDED
#define BZLACONSUTILS_H_INCLUDED

#include "bzlabv.h"

typedef struct BzlaPropInfo BzlaPropInfo;

bool bzla_is_cons_add_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_and_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_xor_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_eq_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_ult_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_slt_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_sll_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_srl_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_sra_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_mul_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_udiv_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_urem_const(Bzla *bzla, BzlaPropInfo *pi);
bool bzla_is_cons_concat_const(Bzla *bzla, BzlaPropInfo *pi);

#endif
