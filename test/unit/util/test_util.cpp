#include <gtest/gtest.h>

#include <string>

#include "test.h"
#include "util/util.h"

using namespace bzla::util;

class TestUtil : public TestCommon
{
};

TEST_F(TestUtil, is_valid_bv_str)
{
  ASSERT_TRUE(is_valid_bv_str("0101", 2));
  ASSERT_FALSE(is_valid_bv_str("0102", 2));
  ASSERT_TRUE(is_valid_bv_str("1234567890", 10));
  ASSERT_TRUE(is_valid_bv_str("-123", 10));
  ASSERT_FALSE(is_valid_bv_str("12a", 10));
  ASSERT_TRUE(is_valid_bv_str("0123456789abcdefABCDEF", 16));
  ASSERT_FALSE(is_valid_bv_str("12g", 16));
}

TEST_F(TestUtil, is_valid_real_str)
{
  ASSERT_TRUE(is_valid_real_str("123"));
  ASSERT_TRUE(is_valid_real_str("-123"));
  ASSERT_TRUE(is_valid_real_str("1.5"));
  ASSERT_TRUE(is_valid_real_str("-1.5"));
  ASSERT_FALSE(is_valid_real_str("1.5.6"));
  ASSERT_FALSE(is_valid_real_str("1a"));
  // A leading '-' is only valid at position 0.
  ASSERT_FALSE(is_valid_real_str("1-2"));
}

// Regression: is_valid_real_str() must not invoke isdigit() with a (signed)
// char that is negative. Bytes >= 0x80 reach this function via user-supplied
// real strings; passing them to isdigit() is undefined behavior. They are not
// digits and must be rejected.
TEST_F(TestUtil, is_valid_real_str_high_byte)
{
  ASSERT_FALSE(is_valid_real_str(std::string(1, static_cast<char>(0x80))));
  ASSERT_FALSE(is_valid_real_str(std::string(1, static_cast<char>(0xff))));
  ASSERT_FALSE(is_valid_real_str(std::string("12") + static_cast<char>(0xc3)
                                 + std::string("3")));
}
