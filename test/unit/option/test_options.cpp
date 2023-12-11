/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "gtest/gtest.h"
#include "option/option.h"
#include "test.h"

namespace bzla::test {

using namespace bzla::option;

class TestOptions : public ::testing::Test
{
 protected:
  Options d_opts;
};

TEST_F(TestOptions, opt_bool)
{
  ASSERT_EQ(d_opts.produce_models(), false);
  ASSERT_EQ(d_opts.get<bool>(Option::PRODUCE_MODELS), false);
  d_opts.set<bool>(Option::PRODUCE_MODELS, true);
  ASSERT_EQ(d_opts.produce_models(), true);
  ASSERT_EQ(d_opts.get<bool>(Option::PRODUCE_MODELS), true);
  ASSERT_DEATH_DEBUG(d_opts.get<uint64_t>(Option::PRODUCE_MODELS),
                     "is_numeric");
  ASSERT_DEATH_DEBUG(d_opts.get<std::string>(Option::PRODUCE_MODELS),
                     "is_mode");
}

TEST_F(TestOptions, opt_num)
{
  ASSERT_EQ(d_opts.log_level(), 0);
  ASSERT_EQ(d_opts.get<uint64_t>(Option::LOG_LEVEL), 0);
  d_opts.set<uint64_t>(Option::LOG_LEVEL, 2);
  ASSERT_EQ(d_opts.log_level(), 2);
  ASSERT_EQ(d_opts.get<uint64_t>(Option::LOG_LEVEL), 2);
  d_opts.set<uint64_t>(Option::LOG_LEVEL, 1);
  ASSERT_EQ(d_opts.log_level(), 1);
  ASSERT_EQ(d_opts.get<uint64_t>(Option::LOG_LEVEL), 1);
  ASSERT_DEATH_DEBUG(d_opts.get<bool>(Option::LOG_LEVEL), "is_bool");
  ASSERT_DEATH_DEBUG(d_opts.get<std::string>(Option::LOG_LEVEL), "is_mode");
}

TEST_F(TestOptions, opt_enum)
{
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::CADICAL);
  ASSERT_EQ(d_opts.get<std::string>(Option::SAT_SOLVER), "cadical");
#ifdef BZLA_USE_CMS
  d_opts.set<std::string>(Option::SAT_SOLVER, "cms");
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::CRYPTOMINISAT);
  ASSERT_EQ(d_opts.get<std::string>(Option::SAT_SOLVER), "cms");
#endif
#ifdef BZLA_USE_KISSAT
  d_opts.set<std::string>(Option::SAT_SOLVER, "kissat");
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::KISSAT);
  ASSERT_EQ(d_opts.get<std::string>(Option::SAT_SOLVER), "kissat");
#endif
  ASSERT_DEATH_DEBUG(d_opts.get<bool>(Option::SAT_SOLVER), "is_bool");
  ASSERT_DEATH_DEBUG(d_opts.get<uint64_t>(Option::SAT_SOLVER), "is_numeric");
}

TEST_F(TestOptions, opt_defaults)
{
  {
    Options opts;
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    opts.finalize();
    ASSERT_EQ(opts.prop_nprops(), 10000);
    ASSERT_EQ(opts.prop_nupdates(), 2000000);
  }
  {
    Options opts;
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    opts.set<uint64_t>(Option::PROP_NPROPS, 5);
    opts.finalize();
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    ASSERT_EQ(opts.prop_nprops(), 10000);
    ASSERT_EQ(opts.prop_nupdates(), 2000000);
    opts.set<uint64_t>(Option::PROP_NPROPS, 10);
    ASSERT_EQ(opts.prop_nprops(), 10);
  }
  {
    Options opts;
    opts.set<uint64_t>(Option::PROP_NPROPS, 5);
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    opts.finalize();
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    ASSERT_EQ(opts.prop_nprops(), 10000);
    ASSERT_EQ(opts.prop_nupdates(), 2000000);
    opts.set<uint64_t>(Option::PROP_NPROPS, 0);
    ASSERT_EQ(opts.prop_nprops(), 0);
  }
  {
    Options opts;
    opts.set<uint64_t>(Option::PROP_NPROPS, 5, true);
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    opts.finalize();
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    ASSERT_EQ(opts.prop_nprops(), 5);
    ASSERT_EQ(opts.prop_nupdates(), 2000000);
#ifndef NDEBUG
    ASSERT_DEATH(opts.set<uint64_t>(Option::PROP_NPROPS, 0), "is_user_set");
#endif
    opts.set<uint64_t>(Option::PROP_NPROPS, 0, true);
    ASSERT_EQ(opts.prop_nprops(), 0);
  }
  {
    Options opts;
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    opts.finalize();
    opts.set<uint64_t>(Option::PROP_NUPDATES, 5);
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    ASSERT_EQ(opts.prop_nprops(), 10000);
    ASSERT_EQ(opts.prop_nupdates(), 5);
  }
  {
    Options opts;
    opts.set<uint64_t>(Option::PROP_NUPDATES, 5, true);
    opts.set<std::string>(Option::BV_SOLVER, "preprop");
    opts.finalize();
    ASSERT_EQ(opts.bv_solver(), BvSolver::PREPROP);
    ASSERT_EQ(opts.prop_nprops(), 10000);
    ASSERT_EQ(opts.prop_nupdates(), 5);
  }
}

}  // namespace bzla::test
