/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLABVSTRUCT_H_INCLUDED
#define BZLABVSTRUCT_H_INCLUDED

#include <memory>

#include "bitvector.h"

struct BzlaBitVector
{
  std::unique_ptr<bzla::BitVector> d_bv;
};

#endif
