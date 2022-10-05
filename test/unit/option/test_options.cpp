#include "gtest/gtest.h"
#include "option/option.h"

namespace bzla::test {

using namespace bzla::options;

class TestOptions : public ::testing::Test
{
 protected:
  Options d_opts;
};

TEST_F(TestOptions, opt_bool)
{
  ASSERT_EQ(d_opts.incremental(), false);
  ASSERT_EQ(d_opts.get_option_bool(Option::INCREMENTAL), false);
  d_opts.set_option_bool(Option::INCREMENTAL, true);
  ASSERT_EQ(d_opts.incremental(), true);
  ASSERT_EQ(d_opts.get_option_bool(Option::INCREMENTAL), true);
  ASSERT_DEATH(d_opts.get_option_numeric(Option::INCREMENTAL), "is_numeric");
  ASSERT_DEATH(d_opts.get_option_enum(Option::INCREMENTAL), "is_enum");
}

TEST_F(TestOptions, opt_num)
{
  ASSERT_EQ(d_opts.log_level(), 0);
  ASSERT_EQ(d_opts.get_option_numeric(Option::LOG_LEVEL), 0);
  d_opts.set_option_numeric(Option::LOG_LEVEL, 2);
  ASSERT_EQ(d_opts.log_level(), 2);
  ASSERT_EQ(d_opts.get_option_numeric(Option::LOG_LEVEL), 2);
  d_opts.set_option_numeric(Option::LOG_LEVEL, 1);
  ASSERT_EQ(d_opts.log_level(), 1);
  ASSERT_EQ(d_opts.get_option_numeric(Option::LOG_LEVEL), 1);
  ASSERT_DEATH(d_opts.get_option_bool(Option::LOG_LEVEL), "is_bool");
  ASSERT_DEATH(d_opts.get_option_enum(Option::LOG_LEVEL), "is_enum");
}

TEST_F(TestOptions, opt_enum)
{
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::CADICAL);
  ASSERT_EQ(d_opts.get_option_enum(Option::SAT_SOLVER), "cadical");
#ifdef BZLA_USE_CMS
  d_opts.set_option_enum(Option::SAT_SOLVER, "cms");
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::CRYPTOMINISAT);
  ASSERT_EQ(d_opts.get_option_enum(Option::SAT_SOLVER), "cms");
#endif
#ifdef BZLA_USE_KISSAT
  d_opts.set_option_enum(Option::SAT_SOLVER, "kissat");
  ASSERT_EQ(d_opts.sat_solver(), SatSolver::KISSAT);
  ASSERT_EQ(d_opts.get_option_enum(Option::SAT_SOLVER), "kissat");
#endif
  ASSERT_DEATH(d_opts.get_option_bool(Option::SAT_SOLVER), "is_bool");
  ASSERT_DEATH(d_opts.get_option_numeric(Option::SAT_SOLVER), "is_numeric");
}
};  // namespace bzla::test
