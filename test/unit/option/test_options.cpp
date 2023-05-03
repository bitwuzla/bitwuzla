#include "gtest/gtest.h"
#include "option/option.h"

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
  ASSERT_DEATH(d_opts.get<uint64_t>(Option::PRODUCE_MODELS), "is_numeric");
  ASSERT_DEATH(d_opts.get<std::string>(Option::PRODUCE_MODELS), "is_mode");
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
  ASSERT_DEATH(d_opts.get<bool>(Option::LOG_LEVEL), "is_bool");
  ASSERT_DEATH(d_opts.get<std::string>(Option::LOG_LEVEL), "is_mode");
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
  ASSERT_DEATH(d_opts.get<bool>(Option::SAT_SOLVER), "is_bool");
  ASSERT_DEATH(d_opts.get<uint64_t>(Option::SAT_SOLVER), "is_numeric");
}
};  // namespace bzla::test
