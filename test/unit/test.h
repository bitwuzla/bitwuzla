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

#include <gtest/gtest.h>

extern "C" {
#include <bitwuzla/c/bitwuzla.h>
}

class TestCommon : public ::testing::Test
{
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
