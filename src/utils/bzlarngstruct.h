/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#ifndef BZLARNGSTRUCT_H_INCLUDED
#define BZLARNGSTRUCT_H_INCLUDED

#include <memory>

#include "rng/rng.h"

extern "C" {
#include "utils/bzlamem.h"
}

/** The RNG wrapper struct. */
struct BzlaRNG
{
  /** The memory manager. */
  BzlaMemMgr* mm;
  /** The random number generator instance. */
  std::unique_ptr<bzla::RNG> d_rng;
};

#endif
