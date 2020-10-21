/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASLVQUANTN_H_INCLUDED
#define BZLASLVQUANTN_H_INCLUDED

#include "bzlaslv.h"
#include "bzlatypes.h"

BzlaSolver* bzla_new_quantifier_solver(Bzla* bzla);

#endif
