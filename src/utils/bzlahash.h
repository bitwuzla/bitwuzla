/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLA_HASH_H_INCLUDED
#define BZLA_HASH_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "utils/bzlamem.h"

struct BzlaHashTableData
{
  bool flag;
  union
  {
    int32_t as_int;
    double as_dbl;
    void* as_ptr;
    char* as_str;
  };
};

typedef struct BzlaHashTableData BzlaHashTableData;

typedef uint32_t (*BzlaHashPtr)(const void* key);
typedef int32_t (*BzlaCmpPtr)(const void* a, const void* b);

typedef void (*BzlaCloneHashTableData)(BzlaMemMgr* mm,
                                       const void* map,
                                       BzlaHashTableData* data,
                                       BzlaHashTableData* cloned_data);
#endif
