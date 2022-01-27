/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASUBST_H_INCLUDED
#define BZLASUBST_H_INCLUDED

#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodemap.h"

void bzla_substitute_and_rebuild(Bzla *bzla, BzlaPtrHashTable *substs);

/* Create a new node with 'node' substituted by 'subst' in root. */
BzlaNode *bzla_substitute_node(Bzla *bzla,
                               BzlaNode *root,
                               BzlaNode *node,
                               BzlaNode *subst);

/* Create a new node with 'substs' substituted in root. */
BzlaNode *bzla_substitute_nodes(Bzla *bzla,
                                BzlaNode *root,
                                BzlaNodeMap *substs);

/* Create a new term with 'substs' substituted in root. If 'node_map' is given
 * it creates an id map from old nodes to new nodes. */
BzlaNode *bzla_substitute_nodes_node_map(Bzla *bzla,
                                         BzlaNode *root,
                                         BzlaNodeMap *substs,
                                         BzlaIntHashTable *node_map);

void bzla_substitute_terms(Bzla *bzla,
                           size_t terms_size,
                           BzlaNode *terms[],
                           size_t map_size,
                           BzlaNode *map_keys[],
                           BzlaNode *map_values[]);
#endif
