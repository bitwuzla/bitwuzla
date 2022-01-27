/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLADUMPAIG_H_INCLUDED
#define BZLADUMPAIG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "bzlaaig.h"
#include "bzlatypes.h"

/* Dumps AIG in AIGER format to file. */
void bzla_dumpaig_dump_aig(BzlaAIGMgr* amgr,
                           bool is_binary,
                           FILE* output,
                           BzlaAIG* aig);

/* Dumps sequential AIGER model to file. */
void bzla_dumpaig_dump_seq(BzlaAIGMgr* amgr,
                           bool is_binary,
                           FILE* output,
                           int32_t naigs,
                           BzlaAIG** aigs,
                           int32_t nregs,
                           BzlaAIG** regs,
                           BzlaAIG** nexts,
                           BzlaPtrHashTable* back_annotation);

/* Dumps AIGs in AIGER format to file. */
void bzla_dumpaig_dump(Bzla* bzla,
                       bool is_binary,
                       FILE* output,
                       bool merge_roots);
#endif
