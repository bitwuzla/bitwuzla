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

TEST_F(TestUtil, is_digit)
{
  for (char c = '0'; c <= '9'; ++c)
  {
    ASSERT_TRUE(is_digit(c));
  }
  ASSERT_FALSE(is_digit('/'));  // just before '0'
  ASSERT_FALSE(is_digit(':'));  // just after '9'
  ASSERT_FALSE(is_digit('a'));
  ASSERT_FALSE(is_digit('A'));
  ASSERT_FALSE(is_digit(' '));
  // High-bit bytes (negative on platforms where char is signed) are not digits
  // and must not trigger undefined behavior.
  ASSERT_FALSE(is_digit(static_cast<char>(0x80)));
  ASSERT_FALSE(is_digit(static_cast<char>(0xff)));
}

TEST_F(TestUtil, is_xdigit)
{
  for (char c = '0'; c <= '9'; ++c)
  {
    ASSERT_TRUE(is_xdigit(c));
  }
  for (char c = 'a'; c <= 'f'; ++c)
  {
    ASSERT_TRUE(is_xdigit(c));
  }
  for (char c = 'A'; c <= 'F'; ++c)
  {
    ASSERT_TRUE(is_xdigit(c));
  }
  ASSERT_FALSE(is_xdigit('g'));
  ASSERT_FALSE(is_xdigit('G'));
  ASSERT_FALSE(is_xdigit(' '));
  ASSERT_FALSE(is_xdigit(static_cast<char>(0x80)));
  ASSERT_FALSE(is_xdigit(static_cast<char>(0xff)));
}

TEST_F(TestUtil, is_space)
{
  ASSERT_TRUE(is_space(' '));
  ASSERT_TRUE(is_space('\t'));
  ASSERT_TRUE(is_space('\n'));
  ASSERT_TRUE(is_space('\v'));
  ASSERT_TRUE(is_space('\f'));
  ASSERT_TRUE(is_space('\r'));
  ASSERT_FALSE(is_space('a'));
  ASSERT_FALSE(is_space('0'));
  ASSERT_FALSE(is_space(static_cast<char>(0x80)));
  // Latin-1 non-breaking space is not an ASCII whitespace character.
  ASSERT_FALSE(is_space(static_cast<char>(0xa0)));
  ASSERT_FALSE(is_space(static_cast<char>(0xff)));
}

TEST_F(TestUtil, to_lower)
{
  for (char c = 'A'; c <= 'Z'; ++c)
  {
    ASSERT_EQ(to_lower(c), c - 'A' + 'a');
  }
  // Characters that are not upper-case ASCII letters are returned unchanged.
  ASSERT_EQ(to_lower('a'), 'a');
  ASSERT_EQ(to_lower('z'), 'z');
  ASSERT_EQ(to_lower('0'), '0');
  ASSERT_EQ(to_lower(' '), ' ');
  ASSERT_EQ(to_lower(static_cast<char>(0x80)), static_cast<char>(0x80));
  ASSERT_EQ(to_lower(static_cast<char>(0xff)), static_cast<char>(0xff));
}
