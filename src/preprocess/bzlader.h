/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLADER_H_INCLUDED
#define BZLADER_H_INCLUDED

#include "bzlatypes.h"

BzlaNode* bzla_der_node(Bzla* bzla, BzlaNode* root);

BzlaNode* bzla_cer_node(Bzla* bzla, BzlaNode* root);

#endif
