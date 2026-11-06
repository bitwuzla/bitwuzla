/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_TEST_TEST_H_INCLUDED
#define BZLA_TEST_TEST_H_INCLUDED

#include <gtest/gtest.h>

#include <cmath>
#include <fstream>
#include <sstream>
#include <string>

namespace bzla::test {

/**
 * True if linked against our patched, bundled CaDiCaL and Kissat. Same as
 * config::cadical_patched and config::kissat_patched, which unit tests can not
 * include (see test/unit/meson.build).
 */
#ifdef BZLA_CADICAL_PATCHED
inline constexpr bool cadical_patched = true;
#else
inline constexpr bool cadical_patched = false;
#endif
#ifdef BZLA_KISSAT_PATCHED
inline constexpr bool kissat_patched = true;
#else
inline constexpr bool kissat_patched = false;
#endif

}  // namespace bzla::test

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
