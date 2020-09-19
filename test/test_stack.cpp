/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2017-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlastack.h"
}

class TestStack : public TestMm
{
};

TEST_F(TestStack, init_release)
{
  BzlaIntStack stack;
  BZLA_INIT_STACK(d_mm, stack);
  BZLA_RELEASE_STACK(stack);
}

TEST_F(TestStack, functionality)
{
  BzlaIntStack stack;
  BZLA_INIT_STACK(d_mm, stack);
  ASSERT_EQ(BZLA_COUNT_STACK(stack), 0u);
  ASSERT_TRUE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 0u);
  ASSERT_TRUE(BZLA_FULL_STACK(stack));

  BZLA_PUSH_STACK(stack, 1);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 1u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 1u);
  ASSERT_TRUE(BZLA_FULL_STACK(stack));

  BZLA_PUSH_STACK(stack, 2);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 2u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 2u);
  ASSERT_TRUE(BZLA_FULL_STACK(stack));

  BZLA_PUSH_STACK(stack, 3);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 3u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));

  ASSERT_EQ(BZLA_POP_STACK(stack), 3);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 2u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));

  ASSERT_EQ(BZLA_POP_STACK(stack), 2);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 1u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));

  ASSERT_EQ(BZLA_POP_STACK(stack), 1);

  ASSERT_EQ(BZLA_COUNT_STACK(stack), 0u);
  ASSERT_TRUE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));

  BZLA_RELEASE_STACK(stack);
}

TEST_F(TestStack, fit)
{
  BzlaIntStack stack;
  int32_t i;
  BZLA_INIT_STACK(d_mm, stack);
  for (i = 0; i < 100; i++)
  {
    BZLA_FIT_STACK(stack, i);
    stack.start[i] = i;
  }
  for (i = 0; i < 100; i++)
  {
    ASSERT_EQ(stack.start[i], i);
  }
  BZLA_FIT_STACK(stack, 999);
  for (i = 100; i < 1000; i++)
  {
    ASSERT_FALSE(stack.start[i]);
  }
  BZLA_RELEASE_STACK(stack);
}

TEST_F(TestStack, reset)
{
  BzlaIntStack stack;
  BZLA_INIT_STACK(d_mm, stack);
  BZLA_PUSH_STACK(stack, 1);
  BZLA_PUSH_STACK(stack, 2);
  BZLA_PUSH_STACK(stack, 3);
  ASSERT_EQ(BZLA_COUNT_STACK(stack), 3u);
  ASSERT_FALSE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));
  BZLA_RESET_STACK(stack);
  ASSERT_EQ(BZLA_COUNT_STACK(stack), 0u);
  ASSERT_TRUE(BZLA_EMPTY_STACK(stack));
  ASSERT_EQ(BZLA_SIZE_STACK(stack), 4u);
  ASSERT_FALSE(BZLA_FULL_STACK(stack));
  BZLA_RELEASE_STACK(stack);
}
