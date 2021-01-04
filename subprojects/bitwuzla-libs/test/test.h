#ifndef BZLALS__TEST__TEST_H
#define BZLALS__TEST__TEST_H

#include <cmath>
#include <string>

#include "bitvector.h"
#include "bitvector_domain.h"
#include "gmpmpz.h"
#include "gtest/gtest.h"

namespace bzlals {
namespace test {

/* -------------------------------------------------------------------------- */

class TestCommon : public ::testing::Test
{
 protected:
  enum Kind
  {
    ADD,
    AND,
    ASHR,
    CONCAT,
    DEC,
    EQ,
    IMPLIES,
    ITE,
    INC,
    MUL,
    NAND,
    NE,
    NEG,
    NOR,
    NOT,
    OR,
    REDAND,
    REDOR,
    SDIV,
    SEXT,
    SGT,
    SGE,
    SHL,
    SHR,
    SLT,
    SLE,
    SREM,
    SUB,
    UDIV,
    UGT,
    UGE,
    ULT,
    ULE,
    UREM,
    XNOR,
    XOR,
    ZEXT,
  };
};

/* -------------------------------------------------------------------------- */

class TestBvDomainCommon : public TestCommon
{
 protected:
  static void gen_all_combinations(size_t size,
                                   const std::vector<char> &bits,
                                   std::vector<std::string> &values);
  static void gen_xvalues(uint32_t bw, std::vector<std::string> &values);
  static void gen_values(uint32_t bw, std::vector<std::string> &values);
};

void
TestBvDomainCommon::gen_all_combinations(size_t size,
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

void
TestBvDomainCommon::gen_xvalues(uint32_t bw, std::vector<std::string> &values)
{
  gen_all_combinations(bw, {'x', '0', '1'}, values);
}

void
TestBvDomainCommon::gen_values(uint32_t bw, std::vector<std::string> &values)
{
  gen_all_combinations(bw, {'0', '1'}, values);
}

/* -------------------------------------------------------------------------- */

}  // namespace test
}  // namespace bzlals
#endif
