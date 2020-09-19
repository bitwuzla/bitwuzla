/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2013 Armin Biere.
 *  Copyright (C) 2012-2017 Aina Niemetz.
 *  Copyright (C) 2012-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
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

void bzla_dumpsmt_dump_const_value(Bzla* bzla,
                                   const BzlaBitVector* bits,
                                   uint32_t base,
                                   FILE* file);

void bzla_dumpsmt_dump_sort_node(BzlaNode* exp, FILE* file);
void bzla_dumpsmt_dump_sort(BzlaSort* sort, FILE* file);
#endif
