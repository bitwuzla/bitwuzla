/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAPREPROCESS_H_INCLUDED
#define BZLAPREPROCESS_H_INCLUDED

#include <stdint.h>

#include "bzlatypes.h"

int32_t bzla_simplify(Bzla* bzla);

#endif
