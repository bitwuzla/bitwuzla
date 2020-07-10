/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2016 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
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
