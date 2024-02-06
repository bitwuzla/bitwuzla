/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitwuzla/cpp/bitwuzla.h>
#include <bitwuzla/cpp/parser.h>

#include <cassert>
#include <iostream>

using namespace bitwuzla;

int
main()
{
  // First, create a Bitwuzla options instance.
  Options options;

  // We will parse example file `smt2/quickstart.smt2`.
  // Create parser instance.
  parser::Parser parser(options);

  try
  {
    // Now parse the input file.
    std::cout << "Expect: sat" << std::endl;
    std::cout << "Bitwuzla: ";
    parser.parse("../smt2/quickstart.smt2");

    // Now we retrieve the set of asserted formulas and print them.
    auto assertions = parser.bitwuzla()->get_assertions();
    std::cout << "Assertions:" << std::endl << "{" << std::endl;
    for (const auto& a : assertions)
    {
      std::cout << "  " << a << std::endl;
    }
    std::cout << "}" << std::endl;

    // Now we add an assertion via parsing from string.
    parser.parse("(assert (distinct (select a x) y))", true, false);
    // Now the formula is unsat.
    Result result = parser.bitwuzla()->check_sat();

    std::cout << "Expect: unsat" << std::endl;
    std::cout << "Bitwuzla: " << result << std::endl;

    // For illustration purposes, we now parse in some declarations from string
    // and parse in terms and sorts from string.

    // Declare bit-vector sort of size 16.
    Sort bv16 = parser.parse_sort("(_ BitVec 16)");
    // Create bit-vector sort of size 16 and show that it corresponds to
    // its string representation '(_ BitVec16)'.
    assert(bv16 == mk_bv_sort(16));

    // Declare Boolean constant 'c'.
    // Note: Declarations are commands (not terms) in the SMT-LIB language.
    //       Commands must be parsed in via Parser::parse(),
    //       Parser::parse_term() only supports parsing SMT-LIB terms.
    parser.parse("(declare-const c Bool)", true, false);
    // Retrieve term reprsenting 'c'.
    Term c = parser.parse_term("c");
    // Declare bit-vector constant 'b'.
    parser.parse("(declare-const b (_ BitVec 16))", true, false);
    // Retrieve term reprsenting 'b'.
    Term b = parser.parse_term("b");
    // Declare Boolean constant 'd'.
    parser.parse("(declare-const d Bool)", true, false);
    // Retrieve term reprsenting 'd'.
    Term d = parser.parse_term("d");
    // Create xor over 'c' and 'd' and show that it corresponds to term
    // parsed in from its string representation '(xor c d)'.
    assert(parser.parse_term("(xor c d)") == mk_term(Kind::XOR, {c, d}));
    // Create bit-vector addition over 'b' and bit-vector value
    // '1011111010001010' and show that it corresponds to the term parsed in
    // from its string representation '(bvadd b #b1011111010001010)'.
    assert(parser.parse_term("(bvadd b #b1011111010001010)")
           == mk_term(Kind::BV_ADD,
                      {b, mk_bv_value(bv16, "1011111010001010", 2)}));
  }
  catch (bitwuzla::parser::Exception& e)
  {
    // We expect no error to occur.
    std::cout << "unexpected parser exception" << std::endl;
  }
  return 0;
}
