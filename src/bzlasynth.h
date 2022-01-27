/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASYNTHFUN_H_INCLUDED
#define BZLASYNTHFUN_H_INCLUDED

#include <stdint.h>

#include "bzlaexp.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"

BzlaNode* bzla_synthesize_term(Bzla* bzla,
                               BzlaNode* params[],
                               uint32_t nparams,
                               BzlaBitVectorTuple* value_in[],
                               BzlaBitVector* value_out[],
                               uint32_t nvalues,
                               BzlaIntHashTable* value_in_map,
                               BzlaNode* constraints[],
                               uint32_t nconstraints,
                               BzlaNode* consts[],
                               uint32_t nconsts,
                               uint32_t max_checks,
                               uint32_t max_level,
                               BzlaNode* prev_synth);
#endif
