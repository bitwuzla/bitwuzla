/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAREWRITE_H_INCLUDED
#define BZLAREWRITE_H_INCLUDED

#include "bzlanode.h"

/*------------------------------------------------------------------------*/

BzlaNode *bzla_rewrite_slice_exp(Bzla *bzla,
                                 BzlaNode *exp,
                                 uint32_t upper,
                                 uint32_t lower);

BzlaNode *bzla_rewrite_unary_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0);

BzlaNode *bzla_rewrite_binary_exp(Bzla *bzla,
                                  BzlaNodeKind kind,
                                  BzlaNode *e0,
                                  BzlaNode *e1);

BzlaNode *bzla_rewrite_ternary_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

BzlaNode *bzla_rewrite_fp_fma_exp(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3);

BzlaNode *bzla_rewrite_unary_to_fp_exp(Bzla *bzla,
                                       BzlaNodeKind kind,
                                       BzlaNode *e0,
                                       BzlaSortId sort);

BzlaNode *bzla_rewrite_binary_to_fp_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort);

bool bzla_rewrite_linear_bv_term(Bzla *bzla,
                                 BzlaNode *term,
                                 BzlaBitVector **fp,
                                 BzlaNode **lp,
                                 BzlaNode **rp);
#endif
