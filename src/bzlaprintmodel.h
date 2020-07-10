/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *  Copyright (C) 2014-2016 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
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
void bzla_print_fun_model(
    Bzla* bzla, BzlaNode* node, const char* format, uint32_t base, FILE* file);
void bzla_print_bv_model(
    Bzla* bzla, BzlaNode* node, const char* format, uint32_t base, FILE* file);
void bzla_print_model_aufbv(Bzla* bzla, const char* format, FILE* file);

void bzla_print_value_smt2(Bzla* bzla,
                           BzlaNode* exp,
                           char* symbol_str,
                           FILE* file);

#endif
