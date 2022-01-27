/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLADUMPSMT_H_INCLUDED
#define BZLADUMPSMT_H_INCLUDED

#include <stdio.h>

#include "bzlabv.h"
#include "bzlacore.h"

void bzla_dumpsmt_dump_node(Bzla* bzla,
                            FILE* file,
                            BzlaNode* node,
                            uint32_t depth);

void bzla_dumpsmt_dump(Bzla* bzla, FILE* file);

void bzla_dumpsmt_dump_const_bv_value(Bzla* bzla,
                                      const BzlaBitVector* bits,
                                      uint32_t base,
                                      FILE* file);

void bzla_dumpsmt_dump_const_fp_value(Bzla* bzla,
                                      const BzlaBitVector* bits,
                                      uint32_t esize,
                                      uint32_t ssize,
                                      FILE* file);

void bzla_dumpsmt_dump_const_rm_value(Bzla* bzla,
                                      const BzlaBitVector* bits,
                                      FILE* file);

void bzla_dumpsmt_dump_sort_node(BzlaNode* exp, FILE* file);
void bzla_dumpsmt_dump_sort(BzlaSort* sort, FILE* file);
#endif
