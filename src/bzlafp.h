/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "bzlasort.h"
#include "bzlatypes.h"
#include "utils/bzlanodemap.h"

#ifndef BZLAFP_H_INCLUDED
#define BZLAFP_H_INCLUDED

typedef struct BzlaFloatingPoint BzlaFloatingPoint;

BzlaFloatingPoint *bzla_fp_new(Bzla *bzla, BzlaSortId sort);
void bzla_fp_free(Bzla *bzla, BzlaFloatingPoint *fp);
BzlaFloatingPoint *bzla_fp_copy(Bzla *bzla, const BzlaFloatingPoint *fp);
uint32_t bzla_fp_get_exp_width(const BzlaFloatingPoint *fp);
uint32_t bzla_fp_get_sig_width(const BzlaFloatingPoint *fp);
BzlaFloatingPoint *bzla_fp_get_fp(BzlaNode *node);
size_t bzla_fp_get_bytes(BzlaNode *node);
uint32_t bzla_fp_hash(const BzlaFloatingPoint *fp);
int32_t bzla_fp_compare(const BzlaFloatingPoint *a, const BzlaFloatingPoint *b);
BzlaFloatingPoint *bzla_fp_make_zero(Bzla *bzla, BzlaSortId sort, bool sign);

void *bzla_fp_word_blaster_new(Bzla *bzla);
void *bzla_fp_word_blaster_clone(Bzla *bzla, Bzla *clone, BzlaNodeMap *exp_map);
void bzla_fp_word_blaster_delete(void *wblaster);
BzlaNode *bzla_fp_word_blast(Bzla *bzla, BzlaNode *node);

#endif
