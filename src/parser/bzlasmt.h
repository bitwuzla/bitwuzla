/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLASMT_H_INCLUDED
#define BZLASMT_H_INCLUDED

#include <stdio.h>

#include "boolector.h"
#include "bzlaparse.h"

const BzlaParserAPI* bzla_parsesmt_parser_api();

#endif
