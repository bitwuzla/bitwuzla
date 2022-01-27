/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAPPUTILS_H_INCLUDED
#define BZLAPPUTILS_H_INCLUDED

#include "bzlanode.h"
#include "bzlatypes.h"

void bzla_pputils_collect_lambdas(Bzla *bzla, BzlaNodePtrStack *lambdas);

#endif
