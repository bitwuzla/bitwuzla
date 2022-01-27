/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLANORMQUANT_H_INCLUDED
#define BZLANORMQUANT_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashint.h"

BzlaNode* bzla_normalize_quantifiers_node(Bzla* bzla, BzlaNode* root);

BzlaNode* bzla_normalize_quantifiers(Bzla* bzla);

#if 0
/* negates 'root' and inverts all quantifiers under 'root'. */
BzlaNode * bzla_invert_quantifiers (Bzla * bzla, BzlaNode * root,
				    BzlaIntHashTable * node_map);
#endif

#endif
