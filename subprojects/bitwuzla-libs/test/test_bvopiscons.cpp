#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpIsCons : public TestBvOp
{
};

TEST_F(TestBvOpIsCons, add)
{
  test_binary<BitVectorAdd>(IS_CONS, ADD, 0, false);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 1, false);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 0, true);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 1, true);
}

}
}
