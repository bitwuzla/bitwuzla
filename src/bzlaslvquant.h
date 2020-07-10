/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASLVQUANT_H_INCLUDED
#define BZLASLVQUANT_H_INCLUDED

#include "bzlaslv.h"
#include "bzlatypes.h"

BzlaSolver* bzla_new_quantifier_solver(Bzla* bzla);

#endif
