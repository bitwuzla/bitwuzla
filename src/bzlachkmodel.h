/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLACHKMODEL_H_INCLUDED
#define BZLACHKMODEL_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashptr.h"

typedef struct BzlaCheckModelContext BzlaCheckModelContext;

BzlaCheckModelContext *bzla_check_model_init(Bzla *bzla);

void bzla_check_model_delete(BzlaCheckModelContext *ctx);

void bzla_check_model(BzlaCheckModelContext *ctx);

#endif
