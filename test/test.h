/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *  Copyright (C) 2020 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef TEST_H_INCLUDED
#define TEST_H_INCLUDED

#include <fstream>
#include <sstream>
#include <string>

#include "gtest/gtest.h"

extern "C" {
#include "boolector.h"
#include "bzlaconfig.h"
#include "bzlacore.h"
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
    ss_log << BZLA_LOG_DIR << name << ".log";
    ss_out << BZLA_OUT_DIR << name << ".out";

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

  std::string d_log_file_name;
  std::string d_out_file_name;
  FILE* d_log_file      = nullptr;
  bool d_check_log_file = true;
};

class TestMm : public TestCommon
{
 protected:
  void SetUp() override { d_mm = bzla_mem_mgr_new(); }

  void TearDown() override
  {
    if (d_mm)
    {
      bzla_mem_mgr_delete(d_mm);
      d_mm = nullptr;
    }

    TestCommon::TearDown();
  }

  BzlaMemMgr* d_mm = nullptr;
};

class TestBzla : public TestCommon
{
 protected:
  void SetUp() override { d_bzla = bzla_new(); }

  void TearDown() override
  {
    if (d_bzla)
    {
      bzla_delete(d_bzla);
      d_bzla = nullptr;
    }

    TestCommon::TearDown();
  }

  Bzla* d_bzla = nullptr;
};

class TestBoolector : public TestCommon
{
 protected:
  void SetUp() override { d_bzla = boolector_new(); }

  void TearDown() override
  {
    if (d_bzla)
    {
      boolector_delete(d_bzla);
    }

    TestCommon::TearDown();
  }

  Bzla* d_bzla = nullptr;
};

class TestFile : public TestBoolector
{
 protected:
  void run_test(const char* name, int32_t expected, uint32_t verbosity = 0u)
  {
    if (!d_log_file)
    {
      std::string s(name);
      size_t pos = s.rfind('.');
      assert(pos != std::string::npos);
      std::string base_name = s.substr(0, pos);
      open_log_file(base_name);
    }

    std::stringstream ss_in;
    FILE* f_in;
    int32_t parse_status;
    char* parse_err;
    int32_t sat_res;
    bool parsed_smt2;

    ss_in << BZLA_OUT_DIR << name;
    f_in = fopen(ss_in.str().c_str(), "r");
    assert(f_in);

    boolector_set_opt(d_bzla, BZLA_OPT_VERBOSITY, verbosity);

    sat_res = boolector_parse(d_bzla,
                              f_in,
                              ss_in.str().c_str(),
                              d_log_file,
                              &parse_err,
                              &parse_status,
                              &parsed_smt2);
    if (d_expect_parse_error)
    {
      ASSERT_EQ(sat_res, BOOLECTOR_PARSE_ERROR);
      std::string err_msg = parse_err;
      size_t pos          = err_msg.find("log/");
      fprintf(d_log_file, "%s\n", err_msg.substr(pos).c_str());
    }
    else
    {
      ASSERT_NE(sat_res, BOOLECTOR_PARSE_ERROR);
    }

    if (d_dump)
    {
      assert(d_log_file);
      if (d_dump_format == "btor")
      {
        boolector_simplify(d_bzla);
        boolector_dump_btor(d_bzla, d_log_file);
      }
      else
      {
        assert(d_dump_format == "smt2");
        boolector_simplify(d_bzla);
        boolector_dump_smt2(d_bzla, d_log_file);
      }
    }

    if (d_check_sat && sat_res == BOOLECTOR_PARSE_UNKNOWN)
    {
      sat_res = boolector_sat(d_bzla);
      fprintf(d_log_file,
              "%s\n",
              sat_res == BOOLECTOR_SAT
                  ? "sat"
                  : (sat_res == BOOLECTOR_UNSAT ? "unsat" : "unknown"));
    }

    if (d_get_model)
    {
      boolector_print_model(d_bzla, (char*) d_model_format.c_str(), d_log_file);
    }

    if (expected != BOOLECTOR_UNKNOWN)
    {
      ASSERT_EQ(sat_res, expected);
    }

    fclose(f_in);
  }

  void run_test(const char* name,
                const char* ext,
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

#endif
