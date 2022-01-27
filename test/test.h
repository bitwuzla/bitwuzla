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
#include "bzlabvprop.h"
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

  BzlaMemMgr *d_mm = nullptr;
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

  Bzla *d_bzla = nullptr;
};

class TestBitwuzla : public TestCommon
{
 protected:
  void SetUp() override { d_bzla = bitwuzla_new(); }

  void TearDown() override
  {
    if (d_bzla)
    {
      bitwuzla_delete(d_bzla);
    }

    TestCommon::TearDown();
  }

  Bitwuzla *d_bzla = nullptr;
};

class TestFile : public TestBitwuzla
{
 protected:
  void run_test(const char *name, int32_t expected, uint32_t verbosity = 0u)
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
    FILE *f_in;
    BitwuzlaResult parsed_status;
    char *parse_err;
    int32_t sat_res;
    bool parsed_smt2;

    ss_in << BZLA_OUT_DIR << name;
    f_in = fopen(ss_in.str().c_str(), "r");
    assert(f_in);

    bitwuzla_set_option(d_bzla, BITWUZLA_OPT_VERBOSITY, verbosity);

    sat_res = bitwuzla_parse(d_bzla,
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
      bitwuzla_simplify(d_bzla);
      bitwuzla_dump_formula(d_bzla, d_dump_format.c_str(), d_log_file);
    }

    if (d_check_sat && sat_res == BITWUZLA_UNKNOWN)
    {
      sat_res = bitwuzla_check_sat(d_bzla);
      fprintf(d_log_file,
              "%s\n",
              sat_res == BITWUZLA_SAT
                  ? "sat"
                  : (sat_res == BITWUZLA_UNSAT ? "unsat" : "unknown"));
    }

    if (d_get_model)
    {
      bitwuzla_print_model(d_bzla, (char *) d_model_format.c_str(), d_log_file);
    }

    if (expected != BITWUZLA_UNKNOWN)
    {
      ASSERT_EQ(sat_res, expected);
    }

    fclose(f_in);
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

class TestBvDomainCommon : public TestMm
{
 protected:
  /* Initialize all possible values for 3-valued constants of bit-width bw */
  uint32_t generate_consts(uint32_t bw, char ***res)
  {
    assert(bw);
    assert(res);

    uint32_t psize, num_consts = 1;
    char bit = '0';

    for (uint32_t i = 0; i < bw; i++) num_consts *= 3;
    psize = num_consts;

    BZLA_NEWN(d_mm, *res, num_consts);
    for (uint32_t i = 0; i < num_consts; i++)
      BZLA_CNEWN(d_mm, (*res)[i], bw + 1);

    for (uint32_t i = 0; i < bw; i++)
    {
      psize = psize / 3;
      for (uint32_t j = 0; j < num_consts; j++)
      {
        (*res)[j][i] = bit;
        if ((j + 1) % psize == 0)
        {
          bit = bit == '0' ? '1' : (bit == '1' ? 'x' : '0');
        }
      }
    }
    return num_consts;
  }

  void free_consts(uint32_t bw, uint32_t num_consts, char **consts)
  {
    assert(bw);
    assert(consts);
    for (uint32_t i = 0; i < num_consts; i++)
      BZLA_DELETEN(d_mm, consts[i], bw + 1);
    BZLA_DELETEN(d_mm, consts, num_consts);
  }

  void to_str(BzlaBvDomain *d, char **res_lo, char **res_hi, bool print_short)
  {
    assert(d);

    if (print_short)
    {
      assert(res_lo);
      char *lo = bzla_bv_to_char(d_mm, d->lo);
      char *hi = bzla_bv_to_char(d_mm, d->hi);
      for (size_t i = 0, len = strlen(lo); i < len; i++)
      {
        if (lo[i] != hi[i])
        {
          if (lo[i] == '0' && hi[i] == '1')
          {
            lo[i] = 'x';
          }
          else
          {
            assert(lo[i] == '1' && hi[i] == '0');
            lo[i] = '?';
          }
        }
      }
      bzla_mem_freestr(d_mm, hi);
      *res_lo = lo;
      if (res_hi) *res_hi = 0;
    }
    else
    {
      assert(res_hi);
      *res_lo = bzla_bv_to_char(d_mm, d->lo);
      *res_hi = bzla_bv_to_char(d_mm, d->hi);
    }
  }

  void print_domain(BzlaBvDomain *d, bool print_short)
  {
    bzla_bvdomain_print(d_mm, d, print_short);
  }

  /* Create 3-valued bit-vector from domain 'd'. */
  char *from_domain(BzlaMemMgr *mm, BzlaBvDomain *d)
  {
    assert(bzla_bvdomain_is_valid(mm, d));
    char *lo = bzla_bv_to_char(mm, d->lo);
    char *hi = bzla_bv_to_char(mm, d->hi);

    size_t len = strlen(lo);
    for (size_t i = 0; i < len; i++)
    {
      if (lo[i] != hi[i])
      {
        /* lo[i] == '1' && hi[i] == '0' would be an invalid domain. */
        assert(lo[i] == '0');
        assert(hi[i] == '1');
        lo[i] = 'x';
      }
    }
    bzla_mem_freestr(mm, hi);
    return lo;
  }

  bool is_xxx_domain(BzlaMemMgr *mm, BzlaBvDomain *d)
  {
    assert(mm);
    assert(d);
    char *str_d = from_domain(mm, d);
    bool res    = strchr(str_d, '1') == NULL && strchr(str_d, '0') == NULL;
    bzla_mem_freestr(mm, str_d);
    return res;
  }

  bool is_valid(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain *d_c)
  {
    return (!d_x || bzla_bvdomain_is_valid(mm, d_x))
           && (!d_y || bzla_bvdomain_is_valid(mm, d_y))
           && (!d_z || bzla_bvdomain_is_valid(mm, d_z))
           && (!d_c || bzla_bvdomain_is_valid(mm, d_c));
  }

  bool is_fixed(BzlaMemMgr *mm,
                BzlaBvDomain *d_x,
                BzlaBvDomain *d_y,
                BzlaBvDomain *d_z,
                BzlaBvDomain *d_c)
  {
    return (!d_x || bzla_bvdomain_is_fixed(mm, d_x))
           && (!d_y || bzla_bvdomain_is_fixed(mm, d_y))
           && (!d_z || bzla_bvdomain_is_fixed(mm, d_z))
           && (!d_c || bzla_bvdomain_is_fixed(mm, d_c));
  }
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
