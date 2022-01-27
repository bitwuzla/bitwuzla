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
#include "utils/bzlaqueue.h"
}

BZLA_DECLARE_QUEUE(BzlaUInt, uint32_t);

class TestQueue : public TestMm
{
};

TEST_F(TestQueue, init_release)
{
  BzlaUIntQueue queue;
  BZLA_INIT_QUEUE(d_mm, queue);
  BZLA_RELEASE_QUEUE(queue);
}

TEST_F(TestQueue, functionality)
{
  BzlaUIntQueue queue;

  BZLA_INIT_QUEUE(d_mm, queue);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 0u);
  ASSERT_TRUE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_EQ(BZLA_SIZE_QUEUE(queue), 0u);
  ASSERT_TRUE(BZLA_FULL_QUEUE(queue));

  BZLA_ENQUEUE(queue, 1);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 1u);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_TRUE(BZLA_FULL_QUEUE(queue));

  BZLA_ENQUEUE(queue, 2);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 2u);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_TRUE(BZLA_FULL_QUEUE(queue));

  BZLA_ENQUEUE(queue, 3);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 3u);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  ASSERT_EQ(BZLA_DEQUEUE(queue), 1u);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 2u);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  ASSERT_EQ(BZLA_DEQUEUE(queue), 2u);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 1u);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  ASSERT_EQ(BZLA_DEQUEUE(queue), 3u);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 0u);
  ASSERT_TRUE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  ASSERT_LE(BZLA_SIZE_QUEUE(queue), 4u);

  BZLA_RELEASE_QUEUE(queue);
}

TEST_F(TestQueue, reset)
{
  BzlaUIntQueue queue;
  uint32_t i, j, k;

  BZLA_INIT_QUEUE(d_mm, queue);

  for (i = 0; i < 10000; i++) BZLA_ENQUEUE(queue, i);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), i);
  ASSERT_FALSE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_EQ(BZLA_SIZE_QUEUE(queue), (uint32_t)(1 << 14));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  for (j = 0; j < 5000; j++)
  {
    ASSERT_EQ(BZLA_DEQUEUE(queue), j);
  }

  for (k = 0; k < 100; k++)
  {
    for (j = 0; j < 5000; j++) BZLA_ENQUEUE(queue, j);

    for (j = 0; j < 5000; j++) (void) BZLA_DEQUEUE(queue);
  }

  for (; i < (1 << 14); i++) BZLA_ENQUEUE(queue, i);

  BZLA_RESET_QUEUE(queue);

  ASSERT_EQ(BZLA_COUNT_QUEUE(queue), 0u);
  ASSERT_TRUE(BZLA_EMPTY_QUEUE(queue));
  ASSERT_EQ(BZLA_SIZE_QUEUE(queue), (uint32_t)(1 << 14));
  ASSERT_FALSE(BZLA_FULL_QUEUE(queue));

  BZLA_RELEASE_QUEUE(queue);
}
