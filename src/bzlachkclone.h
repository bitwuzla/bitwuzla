/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLACHKCLONE_H_INCLUDED
#define BZLACHKCLONE_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "bzlacore.h"
#include "bzlaopt.h"
#include "bzlasat.h"

void bzla_chkclone(Bzla *bzla, Bzla *clone);

void bzla_chkclone_exp(Bzla *bzla,
                       Bzla *clone,
                       const BzlaNode *exp,
                       const BzlaNode *cexp);

void bzla_chkclone_sort(Bzla *bzla,
                        Bzla *clone,
                        const BzlaSort *sort,
                        const BzlaSort *cexp);

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
