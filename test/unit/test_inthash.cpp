/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"
}

class TestIntHash : public TestMm
{
 protected:
  void SetUp() override
  {
    TestMm::SetUp();
    d_htable = bzla_hashint_table_new(d_mm);
  }

  void TearDown() override
  {
    if (d_htable)
    {
      uint32_t size = d_htable->size;
      std::vector<int32_t> keys;
      BzlaIntHashTableIterator it;
      bzla_iter_hashint_init(&it, d_htable);
      while (bzla_iter_hashint_has_next(&it))
      {
        keys.push_back(bzla_iter_hashint_next(&it));
      }
      bzla_hashint_table_clear(d_htable);
      ASSERT_EQ(d_htable->count, 0);
      ASSERT_EQ(d_htable->size, size);
      for (int32_t i : keys)
      {
        ASSERT_FALSE(bzla_hashint_table_contains(d_htable, i));
      }
      bzla_iter_hashint_init(&it, d_htable);
      ASSERT_FALSE(bzla_iter_hashint_has_next(&it));
      bzla_hashint_table_delete(d_htable);
      d_htable = nullptr;
    }
    TestMm::TearDown();
  }

  BzlaIntHashTable *d_htable = nullptr;
};

TEST_F(TestIntHash, new_delete)
{
  size_t allocated     = d_mm->allocated;
  BzlaIntHashTable *ht = bzla_hashint_table_new(d_mm);
  bzla_hashint_table_delete(ht);
  ASSERT_EQ(allocated, d_mm->allocated);
}

TEST_F(TestIntHash, add)
{
  size_t i;
  int32_t items[] = {
      123,       -1,     17,      5,       32,       64,      -1023,    101231,
      10,        11,     12,      13,      14,       -25,     43,       57,
      75,        51,     86,      -210,    1349,     1084,    -5860,    -1948,
      19548,     45802,  489501,  5810,    -85901,   4885,    28040,    -54801,
      185018,    -43019, 5801,    50185,   18501,    -60154,  105,      195,
      192,       1941,   -148702, -182491, 109581,   -51883,  12840918, -189203,
      -19128348, 129481, 184022,  875092,  19824192, 4913823, 0};

  for (i = 0; items[i] != 0; i++)
  {
    bzla_hashint_table_add(d_htable, items[i]);
    ASSERT_LT(bzla_hashint_table_get_pos(d_htable, items[i]), d_htable->size);
  }

  for (i = 0; items[i] != 0; i++)
    ASSERT_TRUE(bzla_hashint_table_contains(d_htable, items[i]));

  for (i = 0; items[i] != 0; i++)
  {
    bzla_hashint_table_remove(d_htable, items[i]);
    ASSERT_FALSE(bzla_hashint_table_contains(d_htable, items[i]));
    ASSERT_EQ(bzla_hashint_table_get_pos(d_htable, items[i]), d_htable->size);
  }
}
