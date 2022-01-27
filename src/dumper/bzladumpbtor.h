/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLADUMPBTOR_H_INCLUDED
#define BZLADUMPBTOR_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "bzlatypes.h"

typedef struct BzlaDumpContext BzlaDumpContext;

BzlaDumpContext *bzla_dumpbtor_new_dump_context(Bzla *);
void bzla_dumpbtor_delete_dump_context(BzlaDumpContext *);

void bzla_dumpbtor_add_input_to_dump_context(BzlaDumpContext *, BzlaNode *);
void bzla_dumpbtor_add_state_to_dump_context(BzlaDumpContext *, BzlaNode *);
void bzla_dumpbtor_add_next_to_dump_context(BzlaDumpContext *,
                                            BzlaNode *,
                                            BzlaNode *);
void bzla_dumpbtor_add_init_to_dump_context(BzlaDumpContext *,
                                            BzlaNode *,
                                            BzlaNode *);
void bzla_dumpbtor_add_bad_to_dump_context(BzlaDumpContext *, BzlaNode *);
void bzla_dumpbtor_add_output_to_dump_context(BzlaDumpContext *, BzlaNode *);
void bzla_dumpbtor_add_constraint_to_dump_context(BzlaDumpContext *,
                                                  BzlaNode *);
void bzla_dumpbtor_add_root_to_dump_context(BzlaDumpContext *, BzlaNode *);

void bzla_dumpbtor_dump_bdc(BzlaDumpContext *, FILE *file);
void bzla_dumpbtor_dump_node(Bzla *, FILE *, BzlaNode *);
void bzla_dumpbtor_dump_nodes(Bzla *, FILE *, BzlaNode **, uint32_t);
void bzla_dumpbtor_dump(Bzla *, FILE *, uint32_t);

/* FIXME: right now we cannot dump UF in BTOR as the format does not support UF
 *        yet */
bool bzla_dumpbtor_can_be_dumped(Bzla *);

#endif
