/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlapartgen.h"

#include <assert.h>
#include <string.h>

void
bzla_init_part_gen(BzlaPartitionGenerator* pg,
                   uint32_t n,
                   uint32_t size,
                   bool permutate)
{
  assert(size == 2 || size == 3);

  uint32_t max;
  pg->n         = n;
  pg->cnt_1     = 1;
  max           = n - size + 1;
  pg->cnt_2     = (size == 2) ? max : 1;
  pg->cnt_3     = (size == 3) ? max : 0;
  pg->size      = size;
  pg->permutate = permutate;
  pg->perm_idx  = 0;
  pg->perm_cnt  = 0;
  memset(pg->tuple, 0, sizeof(uint32_t) * BZLA_PART_GEN_MAX_TUPLE_SIZE);
}

uint32_t*
bzla_next_part_gen(BzlaPartitionGenerator* pg)
{
  assert(bzla_has_next_part_gen(pg));

  uint32_t tmp, perm_idx, swap_idx;

  /* permuatate current tuple until all permuatations are done */
  if (pg->permutate && pg->perm_cnt > 0)
  {
    do
    {
      perm_idx     = pg->perm_idx;
      swap_idx     = (pg->perm_idx + 1) % pg->size;
      pg->perm_idx = swap_idx;  //(pg->perm_idx + 1) % pg->size;
      assert(perm_idx < pg->size);
      assert(swap_idx < pg->size);
    }
    /* tuple does not change if values to be swapped are equal */
    while (pg->tuple[perm_idx] == pg->tuple[swap_idx]);

    tmp                 = pg->tuple[perm_idx];
    pg->tuple[perm_idx] = pg->tuple[swap_idx];
    pg->tuple[swap_idx] = tmp;
    pg->perm_cnt--;
    pg->perm_idx = swap_idx;
    //      printf ("swap (%u) %u -> %u\n", pg->perm_cnt, tmp_idx, tmp_idx + 1);
  }
  else if (pg->size == 2)
  {
    pg->tuple[0] = pg->cnt_1;
    pg->tuple[1] = pg->cnt_2;
    pg->cnt_1++;
    pg->cnt_2    = pg->n - pg->cnt_1;
    pg->perm_idx = 0;
    if (pg->tuple[0] == pg->tuple[1])
      pg->perm_cnt = 0;
    else
      pg->perm_cnt = 1;
    assert(pg->tuple[0] < pg->n);
    assert(pg->tuple[1] < pg->n);
  }
  else
  {
    assert(pg->size == 3);
    pg->tuple[0] = pg->cnt_1;
    pg->tuple[1] = pg->cnt_2;
    pg->tuple[2] = pg->cnt_3;
    pg->cnt_3--;
    pg->cnt_2 = pg->n - pg->cnt_1 - pg->cnt_3;
    if (pg->cnt_2 > pg->cnt_3)
    {
      pg->cnt_1++;
      pg->cnt_2 = pg->cnt_1;
      pg->cnt_3 = pg->n - pg->cnt_1 - pg->cnt_2;
    }
    pg->perm_idx = 0;
    if (pg->tuple[0] == pg->tuple[1] && pg->tuple[1] == pg->tuple[2])
      pg->perm_cnt = 0;
    else if (pg->tuple[0] == pg->tuple[1] || pg->tuple[0] == pg->tuple[2]
             || pg->tuple[1] == pg->tuple[2])
      pg->perm_cnt = 2;
    else
      pg->perm_cnt = 5;
    assert(pg->tuple[0] < pg->n);
    assert(pg->tuple[1] < pg->n);
    assert(pg->tuple[2] < pg->n);
  }
  return pg->tuple;
}

bool
bzla_has_next_part_gen(BzlaPartitionGenerator* pg)
{
  if (pg->size == 2) return pg->cnt_1 <= pg->cnt_2;
  return pg->cnt_1 <= pg->cnt_3 || (pg->permutate && pg->perm_cnt > 0);
}
