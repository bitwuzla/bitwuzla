/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <sstream>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "printer/btor2_printer.h"
#include "test/unit/test.h"
#include "util/printer.h"

namespace bzla::test {

using namespace node;

class TestBtor2Printer : public TestCommon
{
 protected:
  NodeManager d_nm;
};

TEST_F(TestBtor2Printer, assert_bv1)
{
  auto x = d_nm.mk_const(d_nm.mk_bool_type(), "x");

  std::stringstream ss;

  Btor2Printer::print_formula(ss, {x});
  ASSERT_EQ(ss.str(),
            "1 sort bitvec 1\n"
            "2 input 1 x\n"
            "3 constraint 2\n");
}

TEST_F(TestBtor2Printer, assert_array_bin)
{
  auto bv2 = d_nm.mk_bv_type(2);
  auto bv4 = d_nm.mk_bv_type(4);
  auto a24 = d_nm.mk_array_type(bv2, bv4);
  auto a   = d_nm.mk_const(a24, "a");
  auto i   = d_nm.mk_const(bv2, "i");
  auto ra  = d_nm.mk_node(Kind::SELECT, {a, i});
  auto c8  = d_nm.mk_value(BitVector::from_ui(4, 8));
  auto eq  = d_nm.mk_node(Kind::BV_ULT, {ra, c8});

  std::stringstream ss;

  Btor2Printer::print_formula(ss, {eq});
  ASSERT_EQ(ss.str(),
            "1 sort bitvec 2\n"
            "2 sort bitvec 4\n"
            "3 sort array 1 2\n"
            "4 sort bitvec 1\n"
            "5 input 3 a\n"
            "6 input 1 i\n"
            "7 read 2 5 6\n"
            "8 const 2 1000\n"
            "9 ult 4 7 8\n"
            "10 constraint 9\n");
}

TEST_F(TestBtor2Printer, assert_array_dec)
{
  auto bv2 = d_nm.mk_bv_type(2);
  auto bv4 = d_nm.mk_bv_type(4);
  auto a24 = d_nm.mk_array_type(bv2, bv4);
  auto a   = d_nm.mk_const(a24, "a");
  auto i   = d_nm.mk_const(bv2, "i");
  auto ra  = d_nm.mk_node(Kind::SELECT, {a, i});
  auto c8  = d_nm.mk_value(BitVector::from_ui(4, 8));
  auto eq  = d_nm.mk_node(Kind::BV_ULT, {ra, c8});

  std::stringstream ss;

  ss << util::set_bv_format(10);
  Btor2Printer::print_formula(ss, {eq});
  ASSERT_EQ(ss.str(),
            "1 sort bitvec 2\n"
            "2 sort bitvec 4\n"
            "3 sort array 1 2\n"
            "4 sort bitvec 1\n"
            "5 input 3 a\n"
            "6 input 1 i\n"
            "7 read 2 5 6\n"
            "8 constd 2 8\n"
            "9 ult 4 7 8\n"
            "10 constraint 9\n");
}

TEST_F(TestBtor2Printer, assert_array_hex)
{
  auto bv2 = d_nm.mk_bv_type(2);
  auto bv4 = d_nm.mk_bv_type(4);
  auto a24 = d_nm.mk_array_type(bv2, bv4);
  auto a   = d_nm.mk_const(a24, "a");
  auto i   = d_nm.mk_const(bv2, "i");
  auto ra  = d_nm.mk_node(Kind::SELECT, {a, i});
  auto c8  = d_nm.mk_value(BitVector::from_ui(4, 8));
  auto eq  = d_nm.mk_node(Kind::BV_ULT, {ra, c8});

  std::stringstream ss;

  ss << util::set_bv_format(16);
  Btor2Printer::print_formula(ss, {eq});
  ASSERT_EQ(ss.str(),
            "1 sort bitvec 2\n"
            "2 sort bitvec 4\n"
            "3 sort array 1 2\n"
            "4 sort bitvec 1\n"
            "5 input 3 a\n"
            "6 input 1 i\n"
            "7 read 2 5 6\n"
            "8 consth 2 8\n"
            "9 ult 4 7 8\n"
            "10 constraint 9\n");
}

}  // namespace bzla::test
