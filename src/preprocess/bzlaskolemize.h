/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASKOLEMIZE_H_INCLUDED
#define BZLASKOLEMIZE_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"

void bzla_skolemize(Bzla* bzla);

BzlaNode* bzla_skolemize_node(Bzla* bzla,
                              BzlaNode* root,
                              BzlaIntHashTable* node_map,
                              BzlaPtrHashTable* skolem_consts);

#endif
