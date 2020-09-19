/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASUBST_H_INCLUDED
#define BZLASUBST_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashptr.h"

void bzla_substitute_and_rebuild(Bzla *bzla, BzlaPtrHashTable *substs);

#endif
