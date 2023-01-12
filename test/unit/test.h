/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef TEST_H_INCLUDED
#define TEST_H_INCLUDED

#include <cmath>
#include <fstream>
#include <sstream>
#include <string>

#include "gtest/gtest.h"

extern "C" {
#include "api/c/bitwuzla.h"
#include "bzlaconfig.h"
}

class TestCommon : public ::testing::Test
{
 protected:
  void TearDown() override
  {
    if (d_log_file)
    {
      fclose(d_log_file);
      d_log_file = nullptr;
      if (d_check_log_file) check_log_file();
    }
  }

  void open_log_file(std::string name)
  {
    std::stringstream ss_log, ss_out;
    ss_log << BZLA_REGRESS_OUT_DIR << name << ".log";
    ss_out << BZLA_REGRESS_DIR << name << ".expect";

    d_log_file_name = ss_log.str();
    d_out_file_name = ss_out.str();
    d_log_file      = fopen(d_log_file_name.c_str(), "w");
  }

  void check_log_file()
  {
    std::ifstream log_file(d_log_file_name,
                           std::ifstream::binary | std::ifstream::ate);
    std::ifstream out_file(d_out_file_name,
                           std::ifstream::binary | std::ifstream::ate);

    ASSERT_TRUE(!log_file.fail() && !out_file.fail());

    std::streampos log_file_size = log_file.tellg();
    std::streampos out_file_size = out_file.tellg();
    ASSERT_NE(log_file_size, 0);
    ASSERT_NE(out_file_size, 0);
    ASSERT_EQ(log_file_size, out_file_size);

    log_file.seekg(0, log_file.beg);
    out_file.seekg(0, out_file.beg);
    ASSERT_TRUE(std::equal(std::istreambuf_iterator<char>(log_file.rdbuf()),
                           std::istreambuf_iterator<char>(),
                           std::istreambuf_iterator<char>(out_file.rdbuf())));
  }

  void log(const std::string &msg)
  {
    std::cerr << "\033[0;32m"
              << "[          ] "
              << "\033[0;0m" << msg << std::endl;
  }

  std::string d_log_file_name;
  std::string d_out_file_name;
  FILE *d_log_file      = nullptr;
  bool d_check_log_file = true;
};

class TestBitwuzla : public TestCommon
{
 protected:
  void SetUp() override { d_options = bitwuzla_options_new(); }

  void TearDown() override
  {
    if (d_options)
    {
      bitwuzla_options_delete(d_options);
    }

    TestCommon::TearDown();
  }
  BitwuzlaOptions *d_options = nullptr;
};

class TestFile : public TestBitwuzla
{
 protected:
  void run_test(const char *name, int32_t expected, uint32_t verbosity = 0u)
  {
    (void) expected;
    if (!d_log_file)
    {
      std::string s(name);
      size_t pos = s.rfind('.');
      assert(pos != std::string::npos);
      std::string base_name = s.substr(0, pos);
      open_log_file(base_name);
    }

    std::stringstream ss_in;
    FILE *f_in;
    // BitwuzlaResult parsed_status;
    // char *parse_err;
    // int32_t sat_res;
    // bool parsed_smt2;

    ss_in << BZLA_REGRESS_DIR << name;
    f_in = fopen(ss_in.str().c_str(), "r");
    assert(f_in);

    bitwuzla_set_option(d_options, BITWUZLA_OPT_VERBOSITY, verbosity);
    // Bitwuzla *bitwuzla = bitwuzla_new(d_options);

    // TODO refactor
#if 0
    sat_res = bitwuzla_parse(bitwuzla,
                             f_in,
                             ss_in.str().c_str(),
                             d_log_file,
                             &parse_err,
                             &parsed_status,
                             &parsed_smt2);
    if (d_expect_parse_error)
    {
      ASSERT_NE(parse_err, nullptr);
      std::string err_msg = parse_err;
      size_t pos          = err_msg.find("log/");
      fprintf(d_log_file, "%s\n", err_msg.substr(pos).c_str());
    }
    else
    {
      ASSERT_EQ(parse_err, nullptr);
    }

    if (d_dump)
    {
      assert(d_log_file);
      bitwuzla_simplify(bitwuzla);
      bitwuzla_dump_formula(bitwuzla, d_dump_format.c_str(), d_log_file);
    }

    if (d_check_sat && sat_res == BITWUZLA_UNKNOWN)
    {
      sat_res = bitwuzla_check_sat(bitwuzla);
      fprintf(d_log_file,
              "%s\n",
              sat_res == BITWUZLA_SAT
                  ? "sat"
                  : (sat_res == BITWUZLA_UNSAT ? "unsat" : "unknown"));
    }

    if (d_get_model)
    {
      // bitwuzla_print_model(d_bzla, (char *) d_model_format.c_str(),
      // d_log_file);
    }

    if (expected != BITWUZLA_UNKNOWN)
    {
      ASSERT_EQ(sat_res, expected);
    }

    fclose(f_in);
#endif
  }

  void run_test(const char *name,
                const char *ext,
                int32_t expected,
                uint32_t verbosity = 0u)
  {
    open_log_file(name);
    std::stringstream ss;
    ss << name << ext;
    run_test(ss.str().c_str(), expected, verbosity);
  }

  bool d_check_sat = true;

  bool d_expect_parse_error = false;

  bool d_get_model           = false;
  std::string d_model_format = "btor";

  bool d_dump               = false;
  std::string d_dump_format = "btor";
};

class TestPropCommon : public TestCommon
{
 public:
  static void gen_all_combinations(size_t size,
                                   const std::vector<char> &bits,
                                   std::vector<std::string> &values)
  {
    size_t num_values;
    size_t num_bits = bits.size();
    std::vector<size_t> psizes;

    num_values = pow(num_bits, size);
    for (size_t i = 0; i < size; ++i)
    {
      psizes.push_back(num_values / pow(num_bits, i + 1));
    }

    /* Generate all combinations of 'bits'. */
    for (size_t row = 0; row < num_values; ++row)
    {
      std::string val;
      for (size_t col = 0; col < size; ++col)
      {
        val += bits[(row / psizes[col]) % num_bits];
      }
      values.push_back(val);
    }
  }

  static void gen_xvalues(uint32_t bw, std::vector<std::string> &values)
  {
    gen_all_combinations(bw, {'x', '0', '1'}, values);
  }

  static void gen_values(uint32_t bw, std::vector<std::string> &values)
  {
    gen_all_combinations(bw, {'0', '1'}, values);
  }
};

#endif
