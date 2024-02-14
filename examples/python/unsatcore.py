###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https:#github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https:#github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

from bitwuzla import *

if __name__ == '__main__':

    # First, create a term manager instance.
    tm = TermManager()
    # Create a Bitwuzla options instance.
    options = Options()
    # Then, enable unsat core extraction.
    # Note: Unsat core extraction is disabled by default.
    options.set(Option.PRODUCE_UNSAT_CORES, True)

    # Then, create a Bitwuzla instance.
    bitwuzla = Bitwuzla(tm, options)

    # Create a bit-vector sort of size 2.
    sortbv2 = tm.mk_bv_sort(2)
    # Create a bit-vector sort of size 4.
    sortbv4 = tm.mk_bv_sort(4)
    # Create Float16 floatinf-point sort.
    sortfp16 = tm.mk_fp_sort(5, 11)

    # Create bit-vector variables.
    # (declare-const x0 (_ BitVec 4))
    x0 = tm.mk_const(sortbv4, 'x0')
    # (declare-const x1 (_ BitVec 2))
    x1 = tm.mk_const(sortbv2, 'x1')
    # (declare-const x2 (_ BitVec 2))
    x2 = tm.mk_const(sortbv2, 'x2')
    # (declare-const x3 (_ BitVec 2))
    x3 = tm.mk_const(sortbv2, 'x3')
    # (declare-const x4 Float16)
    x4 = tm.mk_const(sortfp16, 'x4')

    # Create FP positive zero.
    fpzero = tm.mk_fp_pos_zero(sortfp16)
    # Create BV zero of size 4.
    bvzero = tm.mk_bv_zero(sortbv4)

    # (define-fun f0 ((a Float16)) Bool (fp.gt a (_ +zero 5 11)))
    a_f0 = tm.mk_var(sortfp16, 'a_f0')
    f0 = tm.mk_term(Kind.LAMBDA, [a_f0, tm.mk_term(Kind.FP_GT, [a_f0, fpzero])])

    # (define-fun f1 ((a Float16)) (_ BitVec 4) (ite (f0 a) x0 #b0000))
    a_f1 = tm.mk_var(sortfp16, 'a_f1')
    f1   = tm.mk_term(
        Kind.LAMBDA,
        [a_f1,
           tm.mk_term(Kind.ITE, [tm.mk_term(Kind.APPLY, [f0, a_f1]), x0, bvzero])])

    # (define-fun f2 ((a Float16)) (_ BitVec 2) ((_ extract 1 0) (f1 a)))
    a_f2 = tm.mk_var(sortfp16, 'a_f2')
    f2   = tm.mk_term(
        Kind.LAMBDA,
        [a_f2,
           tm.mk_term(Kind.BV_EXTRACT, [tm.mk_term(Kind.APPLY, [f1, a_f2])], [1, 0])])

    # (assert (! (bvult x2 (f2 (_ +zero 5 11))) :named a0))
    a0 = tm.mk_term(Kind.BV_ULT, [x2, tm.mk_term(Kind.APPLY, [f2, fpzero])])
    bitwuzla.assert_formula(a0)

    # (assert (! (= x1 x2 x3) :named a1))
    a1 = tm.mk_term(Kind.EQUAL, [x1, x2, x3])
    bitwuzla.assert_formula(a1)

    # (assert (!(= x4 ((_ to_fp_unsigned 5 11) RNE x3)) :named a2))
    a2 = tm.mk_term(Kind.EQUAL,
                      [x4,
                       tm.mk_term(Kind.FP_TO_FP_FROM_UBV,
                               [tm.mk_rm_value(RoundingMode.RNE), x3],
                               [5, 11])])
    bitwuzla.assert_formula(a2)

    # (check-sat)
    result = bitwuzla.check_sat()
    print('Expect: unsat')
    print(f'Bitwuzla: {result}')

    # (get-unsat-core)
    unsat_core = bitwuzla.get_unsat_core()
    print('Unsat Core:')
    print('{')
    for t in unsat_core:
        print(f' {t}')
    print('}')
