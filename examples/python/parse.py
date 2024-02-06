###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https:#github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https:#github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import sys

from bitwuzla import *

if __name__ == '__main__':

    # First, create a Bitwuzla options instance.
    options = Options()

    # We will parse example file `smt2/quickstart.smt2`.
    # Create parser instance.
    parser = Parser(options)

    # Now parse the input file.
    print('Expect: sat')
    print('Bitwuzla: ', end='')
    sys.stdout.flush()
    res = parser.parse("../smt2/quickstart.smt2")
    # We expect no error to occur.
    assert not res

    # Now we retrieve the set of asserted formulas and print them.
    assertions = parser.bitwuzla().get_assertions()
    print('Assertions:')
    print('{')
    for a in assertions:
        print(f' {a}')
    print('}')

    # Now we add an assertion via parsing from string.
    parser.parse('(assert (distinct (select a x) y))', True, False)
    # Now the formula is unsat.
    print('Expect: unsat')
    print(f'Bitwuzla: {parser.bitwuzla().check_sat()}')

    # For illustration purposes, we now parse in some declarations from string
    # and parse in terms and sorts from string.

    # Declare bit-vector sort of size 16.
    bv16 = parser.parse_sort('(_ BitVec 16)')
    # Create bit-vector sort of size 16 and show that it corresponds to
    # its string representation '(_ BitVec16)'.
    assert bv16 == mk_bv_sort(16)

    # Declare Boolean constant 'a'.
    # Note: Declarations are commands (not terms) in the SMT-LIB language.
    #       Commands must be parsed in via Parser::parse(),
    #       Parser::parse_term() only supports parsing SMT-LIB terms.
    parser.parse("(declare-const c Bool)", True, False)
    # Retrieve term reprsenting 'c'.
    c = parser.parse_term('c')
    # Declare bit-vector constant 'b'.
    parser.parse('(declare-const b (_ BitVec 16))', True, False)
    # Retrieve term reprsenting 'b'.
    b = parser.parse_term('b')
    # Declare Boolean constant 'c'.
    parser.parse('(declare-const d Bool)', True, False)
    # Retrieve term reprsenting 'd'.
    d = parser.parse_term('d')
    # Create xor over 'c' and 'd' and show that it corresponds to term
    # parsed in from its string representation '(xor c d)'.
    assert parser.parse_term('(xor c d)') == mk_term(Kind.XOR, [c, d])
    # Create bit-vector addition over 'b' and bit-vector value
    # '1011111010001010' and show that it corresponds to the term parsed in
    # from its string representation '(bvadd b #b1011111010001010)'.
    assert parser.parse_term('(bvadd b #b1011111010001010)') \
           == mk_term(Kind.BV_ADD,
                      [b, mk_bv_value(bv16, '1011111010001010', 2)])
