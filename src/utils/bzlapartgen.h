/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAPARTGEN_H_INCLUDED
#define BZLAPARTGEN_H_INCLUDED

#define BZLA_PART_GEN_MAX_TUPLE_SIZE 3

#include <stdbool.h>
#include <stdint.h>

struct BzlaPartitionGenerator
{
  uint32_t n;
  int32_t cnt_1;
  int32_t cnt_2;
  int32_t cnt_3;
  uint32_t size;
  uint32_t tuple[BZLA_PART_GEN_MAX_TUPLE_SIZE];
  bool permutate;
  uint32_t perm_idx;
  uint32_t perm_cnt;
};

typedef struct BzlaPartitionGenerator BzlaPartitionGenerator;

void bzla_init_part_gen(BzlaPartitionGenerator* pg,
                        uint32_t n,
                        uint32_t size,
                        bool permutate);

uint32_t* bzla_next_part_gen(BzlaPartitionGenerator* pg);

bool bzla_has_next_part_gen(BzlaPartitionGenerator* pg);

#endif
