#
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https:#github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https:#github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import pytest

from bitwuzla import *

if __name__ == "__main__":

    # First, create a Bitwuzla options instance.
    options = Options()
    # Then, enable model generation.
    options.set(Option.PRODUCE_MODELS, True)
    # Now, for illustration purposes, we enable CaDiCaL as SAT solver
    # (CaDiCaL is already configured by default).
    # Note: This will silently fall back to one of the compiled in SAT solvers
    #       if the selected solver is not compiled in.
    options.set(Option.SAT_SOLVER, 'cadical')
    # Then, create a Bitwuzla instance.
    bitwuzla = Bitwuzla(options)

    # Create bit-vector sorts of size 4 and 8.
    sortbv4 = mk_bv_sort(4)
    sortbv8 = mk_bv_sort(8)
    # Create function sort.
    sortfun = mk_fun_sort([sortbv8, sortbv4], sortbv8)
    # Create array sort.
    sortarr = mk_array_sort(sortbv8, sortbv8)

    # Create two bit-vector constants of that sort.
    x = mk_const(sortbv8, "x")
    y = mk_const(sortbv8, "y")
    # Create fun const.
    f = mk_const(sortfun, "f")
    # Create array const.
    a = mk_const(sortarr, "a")
    # Create bit-vector values one and two of the same sort.
    one = mk_bv_one(sortbv8)
    # Alternatively, you can create bit-vector value one with:
    # one = mk_bv_value(sortbv8, "1", 2)
    # one = mk_bv_value(sortbv8, 1)
    two = mk_bv_value(sortbv8, 2)

    # (bvsdiv x (_ bv2 8))
    sdiv = mk_term(Kind.BV_SDIV, [x, two])
    # (bvashr y (_ bv1 8))
    ashr = mk_term(Kind.BV_ASHR, [y, one])
    # ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    sdive = mk_term(Kind.BV_EXTRACT, [sdiv], [3, 0])
    # ((_ extract 3 0) (bvashr x (_ bv1 8)))
    ashre = mk_term(Kind.BV_EXTRACT, [ashr], [3, 0])

    # (assert
    #     (distinct
    #         ((_ extract 3 0) (bvsdiv x (_ bv2 8)))
    #         ((_ extract 3 0) (bvashr y (_ bv1 8)))))
    bitwuzla.assert_formula(mk_term(Kind.DISTINCT, [sdive, ashre]))
    # (assert (= (f x ((_ extract 6 3) x)) y))
    bitwuzla.assert_formula(mk_term(
        Kind.EQUAL,
        [mk_term(Kind.APPLY, [f, x, mk_term(Kind.BV_EXTRACT, [x], [6, 3])]),
         y]))
    # (assert (= (select a x) y))
    bitwuzla.assert_formula(
        mk_term(Kind.EQUAL, [mk_term(Kind.ARRAY_SELECT, [a, x]), y]))

    # (check-sat)
    result = bitwuzla.check_sat()
    print('Expect: sat')
    print(f'Bitwuzla: {result}')

    # Print model in SMT-LIBv2 format.
    print('Model:\n(')
    for term in [x, y, f, a]:
        sort = term.sort()
        symbol = term.symbol()
        print(f'  (define-fun {symbol if symbol else "@t" + term.id()} (',
              end = '')
        if sort.is_fun():
            value = bitwuzla.get_value(term)
            assert value.kind() == Kind.LAMBDA
            assert value.num_children() == 2
            while value[1].kind() == Kind.LAMBDA:
                assert value[0].is_variable()
                print(f'({value[0]} {value[0].sort()}) ',
                      end = '')
                value = value[1]
            assert value[0].is_variable()
            print(f'({value[0]} {value[0].sort()})) ' \
                  + f'{sort.fun_codomain()} {value[1]})')
        else:
            print(f') {sort} {bitwuzla.get_value(term)})')
    print(')')
    print()

    # Print value for x, y, f and a.
    # Both x and y are bit-vector terms and their value is a bit-vector
    # value that can be printed via Term.value().
    print(f'value of x: {bitwuzla.get_value(x).value(2)}')
    print(f'value of y: {bitwuzla.get_value(y).value(2)}')
    print()
    # f and a, on the other hand, are a function and array term, respectively.
    # The value of these terms is not a value term: for f, it is a lambda term,
    # and the value of a is represented as a store term. Thus we cannot use
    # Term.value(), but we can print the value of the terms via Term.str().
    print('str() representation of value of f:')
    print(bitwuzla.get_value(f))
    print()
    print('str() representation of value of a:')
    print(bitwuzla.get_value(a))
    print()
    # Note that the assignment string of bit-vector terms is given as the
    # pure assignment string, either in binary, hexadecimal or decimal format,
    # whereas Term.str() prints the value in SMT-LIB2 format (in the given
    # bit-vector output number format, binary by default).
    print(f'str() representation of value of x: {bitwuzla.get_value(x)}')
    print(f'str() representation of value of y: {bitwuzla.get_value(y)}')
    print()

    # Query value of bit-vector term that does not occur in the input formula
    v = bitwuzla.get_value(mk_term(Kind.BV_MUL, [x, x]))
    print(f'value of v = x * x: {v.value(2)}')
