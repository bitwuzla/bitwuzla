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
#include "utils/bzlamem.h"
}

class TestMem : public TestMm
{
 protected:
};

TEST_F(TestMem, new_delete_mem_mgr) {}

TEST_F(TestMem, malloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) bzla_mem_malloc(d_mm, sizeof(int32_t));
  ASSERT_NE(test, nullptr);
  *test = 3;
  bzla_mem_free(d_mm, test, sizeof(int32_t));
}

TEST_F(TestMem, realloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) bzla_mem_malloc(d_mm, sizeof(int32_t));
  ASSERT_NE(test, nullptr);
  test[0] = 3;
  test    = (int32_t *) bzla_mem_realloc(
      d_mm, test, sizeof(int32_t), sizeof(int32_t) * 2);
  ASSERT_EQ(test[0], 3);
  test[1] = 5;
  ASSERT_EQ(test[0], 3);
  ASSERT_EQ(test[1], 5);
  bzla_mem_free(d_mm, test, sizeof(int32_t) * 2);
}

TEST_F(TestMem, calloc)
{
  int32_t *test = NULL;
  test          = (int32_t *) bzla_mem_calloc(d_mm, sizeof(int32_t), 4);
  ASSERT_NE(test, nullptr);
  ASSERT_EQ(test[0], 0);
  ASSERT_EQ(test[1], 0);
  ASSERT_EQ(test[2], 0);
  ASSERT_EQ(test[3], 0);
  bzla_mem_free(d_mm, test, sizeof(int32_t) * 4);
}

TEST_F(TestMem, strdup)
{
  char *test = bzla_mem_strdup(d_mm, "test");
  ASSERT_EQ(strcmp(test, "test"), 0);
  bzla_mem_freestr(d_mm, test);
}
