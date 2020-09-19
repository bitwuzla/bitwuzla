/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAPPUTILS_H_INCLUDED
#define BZLAPPUTILS_H_INCLUDED

#include "bzlanode.h"
#include "bzlatypes.h"

void bzla_pputils_collect_lambdas(Bzla *bzla, BzlaNodePtrStack *lambdas);

#endif
