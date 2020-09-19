/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2014 Armin Biere.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *  Copyright (C) 2015 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAREWRITE_H_INCLUDED
#define BZLAREWRITE_H_INCLUDED

#include "bzlanode.h"

/*------------------------------------------------------------------------*/

BzlaNode *bzla_rewrite_slice_exp(Bzla *bzla,
                                 BzlaNode *exp,
                                 uint32_t upper,
                                 uint32_t lower);

BzlaNode *bzla_rewrite_binary_exp(Bzla *bzla,
                                  BzlaNodeKind kind,
                                  BzlaNode *e0,
                                  BzlaNode *e1);

BzlaNode *bzla_rewrite_ternary_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2);

bool bzla_rewrite_linear_term(Bzla *bzla,
                              BzlaNode *term,
                              BzlaBitVector **fp,
                              BzlaNode **lp,
                              BzlaNode **rp);
#endif
