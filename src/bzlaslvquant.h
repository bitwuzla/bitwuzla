/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASLVQUANT_H_INCLUDED
#define BZLASLVQUANT_H_INCLUDED

#include "bzlaslv.h"
#include "bzlatypes.h"

BzlaSolver* bzla_new_quantifier_solver(Bzla* bzla);

#endif
