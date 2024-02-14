###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

from bitwuzla import *

if __name__ == "__main__":

    # First, create a term manager instance.
    tm = TermManager()
    # Create a Bitwuzla options instance.
    options = Options()
    options.set(Option.PRODUCE_MODELS, True)
    # Then, create a Bitwuzla instance.
    bitwuzla = Bitwuzla(tm, options)
    # Create some sorts.
    bv8  = tm.mk_bv_sort(8)
    bv32 = tm.mk_bv_sort(32)
    fp16 = tm.mk_fp_sort(5, 11)
    # Create terms.
    b     = tm.mk_const(tm.mk_bool_sort(), "b")
    bv    = tm.mk_const(bv8, "bv")
    fp    = tm.mk_const(fp16, "fp")
    rm    = tm.mk_const(tm.mk_rm_sort(), "rm")
    fun   = tm.mk_const(tm.mk_fun_sort([bv8, fp16, bv32], fp16), "fun")
    zero  = tm.mk_bv_zero(bv8)
    ones  = tm.mk_bv_ones(tm.mk_bv_sort(23))
    z     = tm.mk_var(bv8, "z")
    q     = tm.mk_var(bv8, "q")
    lambd = tm.mk_term(Kind.LAMBDA, [z, tm.mk_term(Kind.BV_ADD, [z, bv])])
    fpleq = tm.mk_term(
        Kind.FP_LEQ,
        [tm.mk_term(Kind.APPLY,
                  [fun, bv, fp, tm.mk_term(Kind.BV_ZERO_EXTEND, [ones], [9])]),
          fp])
    exists = tm.mk_term(
        Kind.EXISTS,
        [q, tm.mk_term(Kind.EQUAL, [zero, tm.mk_term(Kind.BV_MUL, [bv, q])])])
    # Assert formulas.
    bitwuzla.assert_formula(b)
    bitwuzla.assert_formula(
        tm.mk_term(Kind.EQUAL, [tm.mk_term(Kind.APPLY, [lambd, bv]), zero]))
    bitwuzla.assert_formula(exists)
    bitwuzla.assert_formula(fpleq)

    # Print sort.
    print('Print bit-vector sort of size 32:')
    print('---------------------------------')
    print(f'str(): {bv32}')
    print()

    # Print terms.
    # Note: Hexadecimal bv output format is ignored if the value is not of size
    #       divisible by 4.
    print('Print term:')
    print('-----------')
    print(f'str()      [default]:       {rm}')
    print(f'str()      [bin (ignored)]: {rm.str(2)}')
    print(f'str()      [dec (ignored)]: {rm.str(10)}')
    print(f'str(16)    [hex (ignored)]: {rm.str(16)}')
    print()
    print(f'str()      [default]: {zero}')
    print(f'str()      [bin]:     {zero.str(2)}')
    print(f'str(10)    [dec]:     {zero.str(10)}')
    print(f'str(16)    [hex]:     {zero.str(16)}')
    print()
    print(f'str()      [default]:       {fpleq}')
    print(f'str()      [bin]:           {fpleq.str()}')
    print(f'str(10)    [dec]:           {fpleq.str(10)}')
    print(f'str(16)    [hex (ignored)]: {fpleq.str(16)}')
    print()

    # Print asserted formulas.
    # Note: This uses the default bit-vector output format (binary).
    expected_smt2 = \
            '(set-logic UFBVFP)\n' \
            + '(declare-const b Bool)\n' \
            + '(declare-const bv (_ BitVec 8))\n' \
            + '(declare-const fp (_ FloatingPoint 5 11))\n' \
            + '(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
            + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
            + '(assert b)\n' \
            + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) ' \
            + '#b00000000))\n' \
            + '(assert (exists ((q (_ BitVec 8))) (= #b00000000 ' \
            + '(bvmul bv q))))\n' \
            + '(assert (fp.leq (fun bv fp ((_ zero_extend 9) ' \
            + '#b11111111111111111111111)) fp))\n' \
            + '(check-sat)\n' \
            + '(exit)\n'
    res = bitwuzla.print_formula()
    assert res == expected_smt2
    print('Print formula [default (binary) bv output format]:')
    print('--------------------------------------------------')
    print(res)

    # Print asserted formulas using hexadecimal bit-vector output format.
    expected_smt2 = \
            '(set-logic UFBVFP)\n' \
            + '(declare-const b Bool)\n' \
            + '(declare-const bv (_ BitVec 8))\n' \
            + '(declare-const fp (_ FloatingPoint 5 11))\n' \
            + '(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
            + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
            + '(assert b)\n' \
            + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) ' \
            + '#x00))\n' \
            + '(assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv q))))\n' \
            + '(assert (fp.leq (fun bv fp ((_ zero_extend 9) ' \
            + '#b11111111111111111111111)) fp))\n' \
            + '(check-sat)\n' \
            + '(exit)\n'
    res = bitwuzla.print_formula("smt2", 16)
    assert res == expected_smt2
    print('Print formula [hexadecimal bv output format]:')
    print('--------------------------------------------------')
    print(res)

    # Print asserted formulas using decimal bit-vector output format.
    expected_smt2 = \
            '(set-logic UFBVFP)\n' \
            + '(declare-const b Bool)\n' \
            + '(declare-const bv (_ BitVec 8))\n' \
            + '(declare-const fp (_ FloatingPoint 5 11))\n' \
            + '(declare-fun fun ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
            + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
            + '(assert b)\n' \
            + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv)) bv) ' \
            + '(_ bv0 8)))\n' \
            + '(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) ' \
            + '(bvmul bv q))))\n' \
            + '(assert (fp.leq (fun bv fp ((_ zero_extend 9) ' \
            + '(_ bv8388607 23))) fp))\n' \
            + '(check-sat)\n' \
            + '(exit)\n'
    res = bitwuzla.print_formula("smt2", 10)
    assert res == expected_smt2
    print('Print formula [decimal bv output format]:')
    print('---------------------------------------------')
    print(res)

    bitwuzla.check_sat()

    # Print values.
    print('Print value of Boolean predicate:')
    print('---------------------------------')
    fpleq_val = bitwuzla.get_value(fpleq).value()
    print(f'{fpleq}: {fpleq_val} [bool]')
    print()

    print('Print value of bv const:')
    print('------------------------')
    print(f'{bv}: {bitwuzla.get_value(bv).value():>8} [str] (bin)')
    print(f'{bv}: {bitwuzla.get_value(bv).value(10):>8} [str] (dec)')
    print(f'{bv}: {bitwuzla.get_value(bv).value(16):>8} [str] (hex)')
    print()

    print('Print value of RoundingMode const:')
    print('----------------------------------')
    print(f'{rm}: {bitwuzla.get_value(rm).value()} [RoundingMode]')
    print()

    fp_val = bitwuzla.get_value(fp)

    print('Print value of fp const as single bit-vector (base ignored):')
    print('------------------------------------------------------------')
    assert fp_val.value(2, False) == fp_val.value(10, False)
    assert fp_val.value(2, False) == fp_val.value(16, False)
    print(f'{fp}: {fp_val.value(2, False):>16} [str] (bin)')
    print(f'{fp}: {fp_val.value(10, False):>16} [str] (dec [ignored])')
    print(f'{fp}: {fp_val.value(16, False):>16} [str] (hex [ignored])')
    print()

    print('Print value of fp const as list of component bit-vectors:')
    print('---------------------------------------------------------')
    val = fp_val.value(2)
    print(f'{fp}: [{val[0]}, {val[1]:>5}, {val[2]:>11}] [str] (bin)')
    val = fp_val.value(10)
    print(f'{fp}: [{val[0]}, {val[1]:>5}, {val[2]:>11}] [str] (dec)')
    val = fp_val.value(16)
    print(f'{fp}: [{val[0]}, {val[1]:>5}, {val[2]:>11}] [str] (hex)')
    print()
