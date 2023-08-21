/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef TEST_H_INCLUDED
#define TEST_H_INCLUDED

#include <gtest/gtest.h>

#include <cmath>
#include <fstream>
#include <sstream>
#include <string>

class TestCommon : public ::testing::Test
{
};

// Debug only ASSERT_DEATH.
#ifdef NDEBUG
#define ASSERT_DEATH_DEBUG(statement, regex)                            \
  std::cout << "warning: " << #statement << " test in " << __FUNCTION__ \
            << " disabled for NDEBUG builds."
#else
#define ASSERT_DEATH_DEBUG(statement, regex) ASSERT_DEATH(statement, regex)
#endif

#endif
