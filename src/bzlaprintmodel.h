/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAPRINTMODEL_H_INCLUDED
#define BZLAPRINTMODEL_H_INCLUDED

#include "bzlanode.h"
#include "bzlatypes.h"

void bzla_print_model(Bzla* bzla, const char* format, FILE* file);
void bzla_print_node_model(Bzla* bzla,
                           BzlaNode* input,
                           BzlaNode* value,
                           const char* format,
                           FILE* file);
void bzla_print_model_aufbvfp(Bzla* bzla, const char* format, FILE* file);

void bzla_print_value_smt2(Bzla* bzla,
                           BzlaNode* exp,
                           char* symbol_str,
                           FILE* file);

#endif
