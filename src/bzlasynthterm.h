/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLASYNTHTERM_H_INCLUDED
#define BZLASYNTHTERM_H_INCLUDED

#include <cstdint>
#include <vector>

extern "C" {
struct Bzla;
struct BzlaNode;
struct BzlaBitVector;
struct BzlaBitVectorTuple;
struct BzlaIntHashTable;
}

namespace bzla {

BzlaNode* bzla_synthesize_term(Bzla* bzla,
                               std::vector<BzlaNode*>& params,
                               std::vector<BzlaBitVectorTuple*>& value_in,
                               std::vector<BzlaBitVector*>& value_out,
                               BzlaIntHashTable* value_in_map,
                               std::vector<BzlaNode*>& constraints,
                               std::vector<BzlaNode*>& consts,
                               uint32_t max_checks,
                               uint32_t max_level,
                               BzlaNode* prev_synth);
}
#endif
