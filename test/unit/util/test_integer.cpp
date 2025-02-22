#include "test.h"
#include "util/integer.h"

using namespace bzla::util;


class TestInteger : public TestCommon
{
};

TEST_F(TestInteger, constructors)
{
  Integer a, ui(1u), si(-1), lu((uint64_t) 1), l((int64_t) -1);
  Integer str(std::string("1")), cc("1"), b(ui);

  ASSERT_EQ(b, ui);
  ASSERT_EQ(str, ui);
  ASSERT_EQ(lu, ui);
  ASSERT_EQ(cc, ui);
}

TEST_F(TestInteger, comparisons)
{
  Integer a(0), b(1), c(2), d;

  ASSERT_TRUE(a == d);
  ASSERT_TRUE(a == 0);
  ASSERT_TRUE(b == 1);
  ASSERT_TRUE(a != b);
  ASSERT_TRUE(a < b);
  ASSERT_TRUE(a <= b);
  ASSERT_TRUE(c > b);
  ASSERT_TRUE(c >= b);
  ASSERT_TRUE(a < 1);
  ASSERT_TRUE(b != 0);
  ASSERT_TRUE(!a.is_odd());
  ASSERT_TRUE(b.is_odd());
  ASSERT_TRUE(!c.is_odd());
}

TEST_F(TestInteger, arithmetic)
{
  Integer a(1), b(2), c(3), d(-2);

  ASSERT_EQ(d, (int64_t) -2l);
  ASSERT_EQ(b, (uint64_t) 2ul);
  ASSERT_EQ(a + b, c);
  ASSERT_EQ(c - b, a);
  ASSERT_EQ(-b, d);
  ASSERT_EQ(b * c, 6);
  ASSERT_EQ(b / d, -1);
  ASSERT_EQ(c / b, 1);
  ASSERT_EQ(a++, 1);
  ASSERT_EQ(a, 2);
  ASSERT_EQ(a--, 2);
  ASSERT_EQ(a, 1);
}

TEST_F(TestInteger, arithmetic_inplace)
{
  Integer a(1), b(4);

  ASSERT_EQ(--a, 0);
  ASSERT_EQ(++a, 1);
  ASSERT_EQ(----a, -1);
  ASSERT_EQ(a -= 5, -6);
  ASSERT_EQ(a += b, -2);
  ASSERT_EQ(a *= -b, 8);
  ASSERT_EQ(a += "123", 131);
  ASSERT_EQ(a /= 3, 43);
}

TEST_F(TestInteger, hash)
{
  Integer a(0), b(10), c(0);

  ASSERT_NE(std::hash<Integer>{}(a), std::hash<Integer>{}(b));
  ASSERT_EQ(std::hash<Integer>{}(a), std::hash<Integer>{}(c));
}
