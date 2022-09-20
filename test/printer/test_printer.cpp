#include <sstream>

#include "bitvector.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test.h"

namespace bzla::test {

using namespace node;

class TestPrinter : public TestCommon
{
};

TEST_F(TestPrinter, print_value)
{
  NodeManager& nm = NodeManager::get();

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_value(true));
    ASSERT_EQ(ss.str(), "true");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_value(false));
    ASSERT_EQ(ss.str(), "false");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_value(BitVector(4, 2)));
    ASSERT_EQ(ss.str(), "#b0010");
  }

  {
    std::stringstream ss;
    Printer::print(
        ss, nm.mk_value(FloatingPoint(nm.mk_fp_type(3, 5), BitVector(8, 2))));
    ASSERT_EQ(ss.str(), "(fp #b0 #b000 #b0010)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_value(RoundingMode::RNA));
    ASSERT_EQ(ss.str(), "RNA");
  }
}

TEST_F(TestPrinter, print_const)
{
  NodeManager& nm = NodeManager::get();

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_const(nm.mk_bool_type(), "x"));
    ASSERT_EQ(ss.str(), "x");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_const(nm.mk_bool_type(), ""));
    ASSERT_EQ(ss.str(), "");
  }

  {
    std::stringstream ss, expected;
    Node n = nm.mk_const(nm.mk_bool_type());
    Printer::print(ss, n);
    expected << "@bzla.const_" << n.id();
    ASSERT_EQ(ss.str(), expected.str());
  }
}

TEST_F(TestPrinter, print_var)
{
  NodeManager& nm = NodeManager::get();

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_var(nm.mk_bool_type(), "x"));
    ASSERT_EQ(ss.str(), "x");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_var(nm.mk_bool_type(), ""));
    ASSERT_EQ(ss.str(), "");
  }

  {
    std::stringstream ss, expected;
    Node n = nm.mk_var(nm.mk_bool_type());
    Printer::print(ss, n);
    expected << "@bzla.var_" << n.id();
    ASSERT_EQ(ss.str(), expected.str());
  }
}

TEST_F(TestPrinter, print_binder)
{
  NodeManager& nm = NodeManager::get();

  Node w = nm.mk_var(nm.mk_bool_type(), "w");
  Node x = nm.mk_var(nm.mk_bv_type(32), "x");
  Node y = nm.mk_var(nm.mk_rm_type(), "y");
  Node z = nm.mk_var(nm.mk_fp_type(8, 24), "z");

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_node(Kind::FORALL, {w, nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((w Bool)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_node(Kind::FORALL, {x, nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((x (_ BitVec 32))) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_node(Kind::FORALL, {y, nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((y RoundingMode)) true)");
  }

  {
    std::stringstream ss;
    Printer::print(ss, nm.mk_node(Kind::FORALL, {z, nm.mk_value(true)}));
    ASSERT_EQ(ss.str(), "(forall ((z (_ FloatingPoint 8 24))) true)");
  }

  {
    Node v = nm.mk_var(nm.mk_bv_type(8), "v");
    std::stringstream ss;
    Printer::print(ss, nm.mk_node(Kind::LAMBDA, {v, v}));
    ASSERT_EQ(ss.str(), "(lambda ((v (_ BitVec 8))) v)");
  }
}

TEST_F(TestPrinter, print_apply)
{
  NodeManager& nm = NodeManager::get();

  Type type = nm.mk_fun_type({nm.mk_bv_type(32), nm.mk_bool_type()});
  Node f    = nm.mk_const(type, "f");
  Node x    = nm.mk_const(nm.mk_bv_type(32), "x");

  std::stringstream ss;
  Printer::print(ss, nm.mk_node(Kind::APPLY, {f, x}));
  ASSERT_EQ(ss.str(), "(f x)");
}

TEST_F(TestPrinter, print_let1)
{
  NodeManager& nm = NodeManager::get();

  Type type    = nm.mk_bool_type();
  Node x       = nm.mk_const(type, "x");
  Node y       = nm.mk_const(type, "y");
  Node x_and_y = nm.mk_node(Kind::AND, {x, y});
  Node or_and  = nm.mk_node(Kind::OR, {x_and_y, x_and_y});

  std::stringstream ss;
  Printer::print(ss, or_and);
  ASSERT_EQ(ss.str(), "(let ((_let0 (and x y))) (or _let0 _let0))");
}

TEST_F(TestPrinter, print_let2)
{
  NodeManager& nm = NodeManager::get();

  Type type       = nm.mk_bool_type();
  Node x          = nm.mk_const(type, "x");
  Node y          = nm.mk_const(type, "y");
  Node x_and_y    = nm.mk_node(Kind::AND, {x, y});
  Node or_and     = nm.mk_node(Kind::OR, {x_and_y, x_and_y});
  Node and_or_and = nm.mk_node(Kind::AND, {or_and, or_and});

  std::stringstream ss;
  Printer::print(ss, and_or_and);
  ASSERT_EQ(
      ss.str(),
      "(let ((_let0 (and x y)) (_let1 (or _let0 _let0))) (and _let1 _let1))");
}

TEST_F(TestPrinter, print_let3)
{
  NodeManager& nm = NodeManager::get();

  Type type    = nm.mk_bool_type();
  Node a       = nm.mk_const(type, "a");
  Node b       = nm.mk_const(type, "b");
  Node a_and_b = nm.mk_node(Kind::AND, {a, b});
  Node forall  = nm.mk_node(Kind::FORALL, {nm.mk_var(type, "x"), a_and_b});
  Node or_and  = nm.mk_node(Kind::OR, {a_and_b, forall});

  std::stringstream ss;
  Printer::print(ss, or_and);
  ASSERT_EQ(ss.str(),
            "(let ((_let0 (and a b))) (or _let0 (forall ((x Bool)) _let0)))");
}

TEST_F(TestPrinter, print_let4)
{
  NodeManager& nm = NodeManager::get();

  Type type       = nm.mk_bool_type();
  Node x          = nm.mk_var(type, "x");
  Node y          = nm.mk_var(type, "y");
  Node x_and_y    = nm.mk_node(Kind::AND, {x, y});
  Node or_and     = nm.mk_node(Kind::OR, {x_and_y, x_and_y});
  Node and_or_and = nm.mk_node(Kind::AND, {or_and, or_and});
  Node forall =
      nm.mk_node(Kind::FORALL, {x, nm.mk_node(Kind::FORALL, {y, and_or_and})});

  std::stringstream ss;
  Printer::print(ss, forall);
  ASSERT_EQ(ss.str(),
            "(forall ((x Bool)) (forall ((y Bool)) (let ((_let0 (and x y)) "
            "(_let1 (or _let0 _let0))) (and _let1 _let1))))");
}

TEST_F(TestPrinter, print_nested)
{
  NodeManager& nm = NodeManager::get();
  Node bvand0     = nm.mk_node(
      Kind::BV_AND,
      {nm.mk_value(BitVector(4, "1001")), nm.mk_value(BitVector(4, "1110"))});
  Node bvand1 =
      nm.mk_node(Kind::BV_AND, {nm.mk_value(BitVector(4, "1001")), bvand0});
  std::stringstream ss;
  Printer::print(ss, bvand1);
  // ASSERT_EQ(ss.str(), "(bvand #b1001 (bvand #b1001 #b1110)");
}

}  // namespace bzla::test
