###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2021 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import pytest
import os
import time

from bitwuzla import *

# ----------------------------------------------------------------------------
# Kind
# ----------------------------------------------------------------------------

def test_kind_to_string():
    assert str(Kind.CONSTANT) == 'CONSTANT'
    assert str(Kind.CONST_ARRAY) == 'CONST_ARRAY'
    assert str(Kind.VARIABLE) == 'VARIABLE'
    assert str(Kind.VALUE) == 'VALUE'
    assert str(Kind.AND) == 'AND'
    assert str(Kind.APPLY) == 'APPLY'
    assert str(Kind.ARRAY_SELECT) == 'SELECT'
    assert str(Kind.ARRAY_STORE) == 'STORE'
    assert str(Kind.BV_ADD) == 'BV_ADD'
    assert str(Kind.BV_AND) == 'BV_AND'
    assert str(Kind.BV_ASHR) == 'BV_ASHR'
    assert str(Kind.BV_COMP) == 'BV_COMP'
    assert str(Kind.BV_CONCAT) == 'BV_CONCAT'
    assert str(Kind.BV_DEC) == 'BV_DEC'
    assert str(Kind.BV_INC) == 'BV_INC'
    assert str(Kind.BV_MUL) == 'BV_MUL'
    assert str(Kind.BV_NAND) == 'BV_NAND'
    assert str(Kind.BV_NEG) == 'BV_NEG'
    assert str(Kind.BV_NOR) == 'BV_NOR'
    assert str(Kind.BV_NOT) == 'BV_NOT'
    assert str(Kind.BV_OR) == 'BV_OR'
    assert str(Kind.BV_REDAND) == 'BV_REDAND'
    assert str(Kind.BV_REDOR) == 'BV_REDOR'
    assert str(Kind.BV_REDXOR) == 'BV_REDXOR'
    assert str(Kind.BV_ROL) == 'BV_ROL'
    assert str(Kind.BV_ROR) == 'BV_ROR'
    assert str(Kind.BV_SADD_OVERFLOW) == 'BV_SADDO'
    assert str(Kind.BV_SDIV_OVERFLOW) == 'BV_SDIVO'
    assert str(Kind.BV_SDIV) == 'BV_SDIV'
    assert str(Kind.BV_SGE) == 'BV_SGE'
    assert str(Kind.BV_SGT) == 'BV_SGT'
    assert str(Kind.BV_SHL) == 'BV_SHL'
    assert str(Kind.BV_SHR) == 'BV_SHR'
    assert str(Kind.BV_SLE) == 'BV_SLE'
    assert str(Kind.BV_SLT) == 'BV_SLT'
    assert str(Kind.BV_SMOD) == 'BV_SMOD'
    assert str(Kind.BV_SMUL_OVERFLOW) == 'BV_SMULO'
    assert str(Kind.BV_SREM) == 'BV_SREM'
    assert str(Kind.BV_SSUB_OVERFLOW) == 'BV_SSUBO'
    assert str(Kind.BV_SUB) == 'BV_SUB'
    assert str(Kind.BV_UADD_OVERFLOW) == 'BV_UADDO'
    assert str(Kind.BV_UDIV) == 'BV_UDIV'
    assert str(Kind.BV_UGE) == 'BV_UGE'
    assert str(Kind.BV_UGT) == 'BV_UGT'
    assert str(Kind.BV_ULE) == 'BV_ULE'
    assert str(Kind.BV_ULT) == 'BV_ULT'
    assert str(Kind.BV_UMUL_OVERFLOW) == 'BV_UMULO'
    assert str(Kind.BV_UREM) == 'BV_UREM'
    assert str(Kind.BV_USUB_OVERFLOW) == 'BV_USUBO'
    assert str(Kind.BV_XNOR) == 'BV_XNOR'
    assert str(Kind.BV_XOR) == 'BV_XOR'
    assert str(Kind.DISTINCT) == 'DISTINCT'
    assert str(Kind.EQUAL) == 'EQUAL'
    assert str(Kind.EXISTS) == 'EXISTS'
    assert str(Kind.FORALL) == 'FORALL'
    assert str(Kind.FP_ABS) == 'FP_ABS'
    assert str(Kind.FP_ADD) == 'FP_ADD'
    assert str(Kind.FP_DIV) == 'FP_DIV'
    assert str(Kind.FP_EQUAL) == 'FP_EQUAL'
    assert str(Kind.FP_FMA) == 'FP_FMA'
    assert str(Kind.FP_FP) == 'FP_FP'
    assert str(Kind.FP_GEQ) == 'FP_GEQ'
    assert str(Kind.FP_GT) == 'FP_GT'
    assert str(Kind.FP_IS_INF) == 'FP_IS_INF'
    assert str(Kind.FP_IS_NAN) == 'FP_IS_NAN'
    assert str(Kind.FP_IS_NEG) == 'FP_IS_NEG'
    assert str(Kind.FP_IS_NORMAL) == 'FP_IS_NORMAL'
    assert str(Kind.FP_IS_POS) == 'FP_IS_POS'
    assert str(Kind.FP_IS_SUBNORMAL) == 'FP_IS_SUBNORMAL'
    assert str(Kind.FP_IS_ZERO) == 'FP_IS_ZERO'
    assert str(Kind.FP_LEQ) == 'FP_LEQ'
    assert str(Kind.FP_LT) == 'FP_LT'
    assert str(Kind.FP_MAX) == 'FP_MAX'
    assert str(Kind.FP_MIN) == 'FP_MIN'
    assert str(Kind.FP_MUL) == 'FP_MUL'
    assert str(Kind.FP_NEG) == 'FP_NEG'
    assert str(Kind.FP_REM) == 'FP_REM'
    assert str(Kind.FP_RTI) == 'FP_RTI'
    assert str(Kind.FP_SQRT) == 'FP_SQRT'
    assert str(Kind.FP_SUB) == 'FP_SUB'
    assert str(Kind.IFF) == 'IFF'
    assert str(Kind.IMPLIES) == 'IMPLIES'
    assert str(Kind.ITE) == 'ITE'
    assert str(Kind.LAMBDA) == 'LAMBDA'
    assert str(Kind.NOT) == 'NOT'
    assert str(Kind.OR) == 'OR'
    assert str(Kind.XOR) == 'XOR'
    assert str(Kind.BV_EXTRACT) == 'BV_EXTRACT'
    assert str(Kind.BV_REPEAT) == 'BV_REPEAT'
    assert str(Kind.BV_ROLI) == 'BV_ROLI'
    assert str(Kind.BV_RORI) == 'BV_RORI'
    assert str(Kind.BV_SIGN_EXTEND) == 'BV_SIGN_EXTEND'
    assert str(Kind.BV_ZERO_EXTEND) == 'BV_ZERO_EXTEND'
    assert str(Kind.FP_TO_FP_FROM_BV) == 'FP_TO_FP_FROM_BV'
    assert str(Kind.FP_TO_FP_FROM_FP) == 'FP_TO_FP_FROM_FP'
    assert str(Kind.FP_TO_FP_FROM_SBV) == 'FP_TO_FP_FROM_SBV'
    assert str(Kind.FP_TO_FP_FROM_UBV) == 'FP_TO_FP_FROM_UBV'
    assert str(Kind.FP_TO_SBV) == 'FP_TO_SBV'
    assert str(Kind.FP_TO_UBV) == 'FP_TO_UBV'

# ----------------------------------------------------------------------------
# RoundingMode
# ----------------------------------------------------------------------------

def test_rm_to_string():
  assert str(RoundingMode.RNA) == 'RNA'
  assert str(RoundingMode.RNE) == 'RNE'
  assert str(RoundingMode.RTN) == 'RTN'
  assert str(RoundingMode.RTP) == 'RTP'
  assert str(RoundingMode.RTZ) == 'RTZ'

# ----------------------------------------------------------------------------
# Result
# ----------------------------------------------------------------------------

def test_result_to_string():
  assert str(Result.SAT) == 'sat'
  assert str(Result.UNSAT) == 'unsat'
  assert str(Result.UNKNOWN) == 'unknown'

# ----------------------------------------------------------------------------
# Bitwuzla
# ----------------------------------------------------------------------------

def test_options_set():
    options = Options()
    with pytest.raises(BitwuzlaException):
        options.set("incremental", True)
    with pytest.raises(BitwuzlaException):
        options.set(Option.VERBOSITY, 5)
    with pytest.raises(BitwuzlaException):
        options.set("VERBOSITY", 5)

    options.set(Option.PRODUCE_MODELS, True)

    assert options.get(Option.PRODUCE_UNSAT_CORES) == 0
    options.set(Option.PRODUCE_UNSAT_CORES, 1)
    assert options.get(Option.PRODUCE_UNSAT_CORES) == 1

    assert options.get(Option.VERBOSITY) == 0
    options.set(Option.VERBOSITY, 2)
    assert options.get(Option.VERBOSITY) == 2
    options.set("verbosity", 3)
    assert options.get(Option.VERBOSITY) == 3
    with pytest.raises(BitwuzlaException):
        options.set("verbositi", "3")

    assert options.get(Option.BV_SOLVER) == "bitblast"
    options.set(Option.BV_SOLVER, "prop")
    assert options.get(Option.BV_SOLVER) == "prop"
    options.set(Option.BV_SOLVER, "bitblast")
    assert options.get(Option.BV_SOLVER) == "bitblast"
    options.set(Option.SAT_SOLVER, "cadical")
    assert options.get(Option.SAT_SOLVER) == "cadical"
    options.set("sat-solver", "kissat")
    assert options.get(Option.SAT_SOLVER) == "kissat"

    with pytest.raises(BitwuzlaException):
        options.set("sat--solver", "kissat")
    with pytest.raises(BitwuzlaException):
        options.set(Option.BV_SOLVER, "asdf")


def test_options_set_args():
    options = Options()
    options.set_args("-v", "-v")
    assert options.get(Option.VERBOSITY) == 2
    options.set_args("-v", 3)
    assert options.get(Option.VERBOSITY) == 3
    options.set_args("-v=4")
    assert options.get(Option.VERBOSITY) == 4
    with pytest.raises(BitwuzlaException):
        options.set_args("-v=100")
    options.set_args("-S=cadical")
    assert options.get(Option.SAT_SOLVER), "cadical"
    with pytest.raises(BitwuzlaException):
        options.set_args("--no-verbosity")


def test_option_info():
    options = Options()
    for opt in Option:
        info = OptionInfo(options, opt)
        if info.kind() == OptionInfoKind.BOOL:
            assert info.cur() == True or info.cur() == False
        elif info.kind() == OptionInfoKind.NUMERIC:
            assert info.cur() >= info.min() and info.cur() <= info.max()
        else:
            assert info.cur() in info.modes()
        assert info.cur() == info.dflt()
        assert info.description()

def test_option_is_valid():
    options = Options()
    assert not options.is_valid("incremental")
    assert options.is_valid("produce-models")

# ----------------------------------------------------------------------------
# Create Sorts
# ----------------------------------------------------------------------------

def test_mk_bool_sort():
    sort = mk_bool_sort()
    assert sort.is_bool()


def test_mk_array_sort():
    bsort = mk_bool_sort()
    sort = mk_array_sort(bsort, bsort)
    assert sort.is_array()
    mk_array_sort(bsort, sort)

    with pytest.raises(BitwuzlaException):
        mk_array_sort(Sort(), bsort)
    with pytest.raises(BitwuzlaException):
        mk_array_sort(bsort, Sort())


def test_mk_bv_sort():
    sort = mk_bv_sort(8)
    assert sort.is_bv()
    assert sort.bv_size() == 8
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(0)


def test_mk_fp_sort():
    sort = mk_fp_sort(5, 11)
    assert sort.is_fp()
    assert sort.fp_exp_size() == 5
    assert sort.fp_sig_size() == 11
    with pytest.raises(BitwuzlaException):
        mk_fp_sort(0, 11)
    with pytest.raises(BitwuzlaException):
        mk_fp_sort(5, 0)


def test_mk_fun_sort():
    with pytest.raises(BitwuzlaException):
        mk_fun_sort([], mk_bool_sort())
    with pytest.raises(BitwuzlaException):
        mk_fun_sort([mk_bool_sort(), mk_bool_sort()], Sort())


def test_mk_uninterpreted_sort():
    s1 = mk_uninterpreted_sort()
    s2 = mk_uninterpreted_sort("foo")
    s3 = mk_uninterpreted_sort("foo")
    assert s1.is_uninterpreted()
    assert s2.is_uninterpreted()
    assert s3.is_uninterpreted()
    assert s1 != s2
    assert s1 != s3
    assert s2 != s3
    assert str(s2) == "foo"
    assert str(s3) == "foo"


# ----------------------------------------------------------------------------
# Create Terms
# ----------------------------------------------------------------------------

def test_mk_true():
    val = mk_true()
    assert val.is_true()
    assert val.value() == True


def test_mk_true():
    val = mk_false()
    assert val.is_false()
    assert val.value() == False


def test_mk_bv_zero():
    val = mk_bv_zero(mk_bv_sort(8))
    assert val.is_bv_value_zero()
    assert val.value() == "00000000"
    assert val.value(10) == "0"
    assert val.value(16) == "0"
    with pytest.raises(BitwuzlaException):
        mk_bv_zero(Sort())
    with pytest.raises(BitwuzlaException):
        mk_bv_zero(mk_fp_sort(5, 11))


def test_mk_bv_one():
    val = mk_bv_one(mk_bv_sort(8))
    assert val.is_bv_value_one()
    assert val.value() == "00000001"
    assert val.value(10) == "1"
    assert val.value(16) == "1"
    with pytest.raises(BitwuzlaException):
        mk_bv_one(Sort())
    with pytest.raises(BitwuzlaException):
        mk_bv_one(mk_fp_sort(5, 11))


def test_mk_bv_ones():
    val = mk_bv_ones(mk_bv_sort(8))
    assert val.is_bv_value_ones()
    assert val.value() == "11111111"
    assert val.value(10) == "255"
    assert val.value(16) == "ff"
    with pytest.raises(BitwuzlaException):
        mk_bv_ones(Sort())
    with pytest.raises(BitwuzlaException):
        mk_bv_ones(mk_fp_sort(5, 11))


def test_mk_bv_min_signed():
    val = mk_bv_min_signed(mk_bv_sort(8))
    assert val.is_bv_value_min_signed()
    assert val.value() == "10000000"
    assert val.value(10) == "128"
    assert val.value(16) == "80"
    with pytest.raises(BitwuzlaException):
        mk_bv_min_signed(Sort())
    with pytest.raises(BitwuzlaException):
        mk_bv_min_signed(mk_fp_sort(5, 11))


def test_mk_bv_max_signed():
    val = mk_bv_max_signed(mk_bv_sort(8))
    assert val.is_bv_value_max_signed()
    assert val.value() == "01111111"
    assert val.value(10) == "127"
    assert val.value(16) == "7f"
    with pytest.raises(BitwuzlaException):
        mk_bv_max_signed(Sort())
    with pytest.raises(BitwuzlaException):
        mk_bv_max_signed(mk_fp_sort(5, 11))

def test_mk_fp_pos_zero():
    val = mk_fp_pos_zero(mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_zero()
    assert val.value(2, False) == "0000000000000000"
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_zero(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_zero(mk_bv_sort(8))

def test_mk_fp_neg_zero():
    val = mk_fp_neg_zero(mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_zero()
    assert val.value(2, False) == "1000000000000000"
    with pytest.raises(BitwuzlaException):
        mk_fp_neg_zero(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_neg_zero(mk_bv_sort(8))

def test_mk_fp_pos_inf():
    val = mk_fp_pos_inf(mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_inf()
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_inf(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_inf(mk_bv_sort(8))

def test_mk_fp_neg_inf():
    val = mk_fp_neg_inf(mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_inf()
    with pytest.raises(BitwuzlaException):
        mk_fp_neg_inf(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_neg_inf(mk_bv_sort(8))

def test_mk_fp_nan():
    val = mk_fp_nan(mk_fp_sort(5, 11))
    assert val.is_fp_value_nan()
    with pytest.raises(BitwuzlaException):
        mk_fp_nan(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_nan(mk_bv_sort(8))

def test_mk_bv_value():
    val = mk_bv_value(mk_bv_sort(4), "1101", 2)
    assert val.value() == "1101"
    assert val.value(10) == "13"
    assert val.value(16) == "d"
    mk_bv_value(mk_bv_sort(8), "127", 10)
    mk_bv_value(mk_bv_sort(8), 127)
    mk_bv_value(mk_bv_sort(8), "-128", 10)
    mk_bv_value(mk_bv_sort(8), -128)
    with pytest.raises(BitwuzlaException):
        mk_bv_value(mk_bv_sort(8), "256", 10)
    with pytest.raises(BitwuzlaException):
        mk_bv_value(mk_bv_sort(8), "-129", 10)
        mk_bv_value(Sort(), "010", 2)
    with pytest.raises(BitwuzlaException):
      mk_bv_value(mk_bv_sort(8), "", 2)

def test_mk_fp_value():
    val = mk_fp_value(mk_bv_value(mk_bv_sort(1), 1),
                      mk_bv_value(mk_bv_sort(5), 0),
                      mk_bv_value(mk_bv_sort(10), 0))
    assert val.is_fp_value_neg_zero()

    with pytest.raises(BitwuzlaException):
        mk_fp_value(Term(),
                    mk_bv_value(mk_bv_sort(5), 0),
                    mk_bv_value(mk_bv_sort(10), 0))
    with pytest.raises(BitwuzlaException):
        mk_fp_value(mk_bv_value(mk_bv_sort(1), 1),
                    Term(),
                    mk_bv_value(mk_bv_sort(10), 0))
    with pytest.raises(BitwuzlaException):
        mk_fp_value(mk_bv_value(mk_bv_sort(1), 1),
                    mk_bv_value(mk_bv_sort(5), 0),
                    Term())

    val1 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), "1.2")
    val2 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), 1.2)
    assert val1 == val2

    val2 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), "6", "5")
    assert val1 == val2

    val1 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), "1", "3")
    val2 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), "1", 3)
    assert val1 == val2
    val2 = mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), 1, 3)
    assert val1 == val2

    with pytest.raises(ValueError):
        mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), 1.2, 3)
    with pytest.raises(ValueError):
        mk_fp_value(mk_fp_sort(5, 11), mk_rm_value(RoundingMode.RNE), 1, 3.3)


def test_mk_rm_value():
    rne = mk_rm_value(RoundingMode.RNE)
    assert rne.value() == RoundingMode.RNE
    rna = mk_rm_value(RoundingMode.RNA)
    assert rna.value() == RoundingMode.RNA
    rtz = mk_rm_value(RoundingMode.RTZ)
    assert rtz.value() == RoundingMode.RTZ
    rtp = mk_rm_value(RoundingMode.RTP)
    assert rtp.value() == RoundingMode.RTP
    rtn = mk_rm_value(RoundingMode.RTN)
    assert rtn.value() == RoundingMode.RTN


def test_mk_const():
    a = mk_const(mk_bv_sort(8), "a")
    assert a.symbol() == "a"
    assert mk_const(mk_bool_sort()).symbol() == None


def test_mk_const_array():
    a = mk_const_array(mk_array_sort(mk_bool_sort(), mk_bool_sort()), mk_true())
    assert a[0].is_value()
    assert a[0].value() == True


def test_mk_var():
    x = mk_var(mk_bv_sort(8), "x")
    assert x.symbol() == "x"
    assert mk_var(mk_bool_sort()).symbol() == None


# ----------------------------------------------------------------------------
# Bitwuzla
# ----------------------------------------------------------------------------

def test_push():
    bitwuzla = Bitwuzla()
    bitwuzla.push(0)
    bitwuzla.push(2)


def test_pop():
    bitwuzla = Bitwuzla()
    bitwuzla.pop(0)
    with pytest.raises(BitwuzlaException):
        bitwuzla.pop(2)
    bitwuzla.push(2)
    bitwuzla.pop(2)


def test_assert_formula():
  bitwuzla = Bitwuzla()
  with pytest.raises(BitwuzlaException):
      bitwuzla.assert_formula(Term())
  bitwuzla.assert_formula(mk_true())
  bitwuzla.assert_formula(mk_false())


def test_get_assertions():
  bitwuzla = Bitwuzla()
  bitwuzla.assert_formula(mk_true())
  bitwuzla.assert_formula(mk_false())
  assert bitwuzla.get_assertions() == [mk_true(), mk_false()]


def test_is_unsat_assumption():
    options = Options()
    options.set(Option.PRODUCE_UNSAT_ASSUMPTIONS, True)
    bitwuzla = Bitwuzla(options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.is_unsat_assumption(mk_false())

    a = mk_const(mk_bool_sort(), "a")
    not_a = mk_term(Kind.NOT, [a])
    bitwuzla.assert_formula(mk_true())
    bitwuzla.check_sat(a, not_a)
    assert not bitwuzla.is_unsat_assumption(mk_true())
    assert bitwuzla.is_unsat_assumption(a)
    assert bitwuzla.is_unsat_assumption(not_a)


def test_get_unsat_assumption():
    options = Options()
    options.set(Option.PRODUCE_UNSAT_ASSUMPTIONS, True)
    bitwuzla = Bitwuzla(options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_unsat_assumptions()

    a = mk_const(mk_bool_sort(), "a")
    not_a = mk_term(Kind.NOT, [a])
    bitwuzla.assert_formula(mk_true())
    bitwuzla.check_sat(a, not_a)
    assert set(bitwuzla.get_unsat_assumptions()) == set([a, not_a])


def test_get_unsat_core():
    options = Options()
    options.set(Option.PRODUCE_UNSAT_CORES, True)
    bitwuzla = Bitwuzla(options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_unsat_core()

    a = mk_const(mk_bool_sort(), "a")
    b = mk_const(mk_bool_sort(), "b")
    not_a = mk_term(Kind.NOT, [a])
    not_b = mk_term(Kind.NOT, [b])
    bitwuzla.assert_formula(mk_true())
    bitwuzla.assert_formula(a, not_a)
    bitwuzla.assert_formula(b, not_b)
    bitwuzla.check_sat()
    assert set(bitwuzla.get_unsat_core()) == set([a, not_a])

    bitwuzla = Bitwuzla(options)
    bitwuzla.assert_formula(a)
    bitwuzla.check_sat(not_a)
    assert set(bitwuzla.get_unsat_core()) == set([a, not_a])


def test_simplify():
    bitwuzla = Bitwuzla()
    bitwuzla.assert_formula(mk_const(mk_bool_sort(), 'b'));
    bv_one1 = mk_bv_one(mk_bv_sort(1))
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [bv_one1,
       mk_term(Kind.BV_AND, [bv_one1, mk_const(mk_bv_sort(1), 'bv')])]))
    bitwuzla.simplify();


def test_check_sat():
    bitwuzla = Bitwuzla()
    bitwuzla.check_sat()
    bitwuzla.check_sat()


def test_get_value():
    bv8 = mk_bv_sort(8)
    bvconst8 = mk_const(bv8)
    bitwuzla = Bitwuzla()
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(bvconst8)

    options = Options()
    options.set(Option.PRODUCE_MODELS, True)
    bitwuzla = Bitwuzla(options)
    bitwuzla.assert_formula(mk_true());
    assert bitwuzla.check_sat(mk_false()) == Result.UNSAT
    b = mk_const(mk_bool_sort())
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(b)
    bitwuzla.check_sat()
    bitwuzla.get_value(b)
    bitwuzla.get_value(mk_false())

    bitwuzla = Bitwuzla(options)
    var = mk_var(bv8, 'q')
    exists = mk_term(Kind.EXISTS, [
        var,
        mk_term(Kind.EQUAL, [
            mk_bv_zero(bv8),
            mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(exists);
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(bvconst8)
    assert bitwuzla.check_sat() == Result.SAT
    bitwuzla.assert_formula(
            mk_term(Kind.EQUAL, [bvconst8, bitwuzla.get_value(bvconst8)]))
    assert bitwuzla.check_sat() == Result.SAT

    bitwuzla = Bitwuzla(options)
    a = mk_const(mk_bool_sort())
    b = mk_const(mk_bool_sort())
    bitwuzla.assert_formula(a)
    bitwuzla.assert_formula(mk_term(Kind.NOT, [b]))
    bitwuzla.check_sat()
    assert bitwuzla.get_value(a).value() == True
    assert bitwuzla.get_value(b).value() == False


def test_get_bool_value():
    assert mk_true().value() == True
    assert mk_false().value() == False
    assert str(mk_true().value()) == 'True'
    assert str(mk_false().value()) == 'False'


def test_get_bv_value():
    fun_sort = mk_fun_sort(
            [mk_bv_sort(8), mk_fp_sort(5, 11), mk_bv_sort(32)], mk_bv_sort(8))
    fun = mk_const(fun_sort)
    with pytest.raises(BitwuzlaException):
        fun.value()

    assert mk_bv_one(mk_bv_sort(1)).value() == '1'

    bv_maxs32 = mk_bv_max_signed(mk_bv_sort(32))
    assert bv_maxs32.value() == '01111111111111111111111111111111'
    assert bv_maxs32.value(10) == '2147483647'
    assert bv_maxs32.value(16) == '7fffffff'

    bv8 = mk_bv_sort(8)
    assert mk_bv_value(bv8, '-1', 10).value() == '11111111'
    assert mk_bv_value(bv8, '-1', 10).value(10) == '255'
    assert mk_bv_value(bv8, '-1', 10).value(16) == 'ff'

    assert mk_bv_value(bv8, '-123', 10).value() == '10000101'
    print(mk_bv_value(bv8, '-123', 10))
    assert mk_bv_value(bv8, '-123', 10).value(10) == '133'
    assert mk_bv_value(bv8, '-123', 10).value(16) == '85'

    assert mk_bv_value(bv8, '-128', 10).value() == '10000000'
    assert mk_bv_value(bv8, '-128', 10).value(10) == '128'
    assert mk_bv_value(bv8, '-128', 10).value(16) == '80'


def test_get_fp_value():
    # single bit-vector string
    fp32 = mk_fp_sort(8, 24)
    fpnan32 = mk_fp_nan(fp32)
    fpnzero32 = mk_fp_neg_zero(fp32)
    assert fpnan32.value(2, False) == '01111111110000000000000000000000'
    assert fpnzero32.value(2, False) == '10000000000000000000000000000000'
    # component bit-vector strings
    assert fpnan32.value() == ['0', '11111111', '10000000000000000000000']
    assert fpnzero32.value() == ['1', '00000000', '00000000000000000000000']


def test_get_rm_value():
    assert mk_rm_value(RoundingMode.RNA).value() == RoundingMode.RNA
    assert mk_rm_value(RoundingMode.RNE).value() == RoundingMode.RNE
    assert mk_rm_value(RoundingMode.RTN).value() == RoundingMode.RTN
    assert mk_rm_value(RoundingMode.RTP).value() == RoundingMode.RTP
    assert mk_rm_value(RoundingMode.RTZ).value() == RoundingMode.RTZ
    assert str(mk_rm_value(RoundingMode.RNA).value()) == 'RNA'
    assert str(mk_rm_value(RoundingMode.RNE).value()) == 'RNE'
    assert str(mk_rm_value(RoundingMode.RTN).value()) == 'RTN'
    assert str(mk_rm_value(RoundingMode.RTP).value()) == 'RTP'
    assert str(mk_rm_value(RoundingMode.RTZ).value()) == 'RTZ'


# ----------------------------------------------------------------------------
# Printing
# ----------------------------------------------------------------------------

def test_print_formula():
    bitwuzla = Bitwuzla()
    with pytest.raises(BitwuzlaException):
        bitwuzla.print_formula('')
    with pytest.raises(BitwuzlaException):
        bitwuzla.print_formula('asdf')

    b = mk_const(mk_bool_sort(), 'b')
    bv8 = mk_bv_sort(8)
    var = mk_var(bv8, 'z')
    bvconst8 = mk_const(bv8, 'bv8')
    lambd = mk_term(Kind.LAMBDA, [
        var, mk_term(Kind.BV_ADD, [var, bvconst8])])
    bitwuzla.assert_formula(b)
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [
        mk_term(Kind.APPLY, [lambd, bvconst8]), mk_bv_zero(bv8)]))

    expected_smt2 = \
        '(set-logic QF_BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#b00000000))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula()

    expected_smt2 = \
        '(set-logic QF_BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '(_ bv0 8)))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 10)

    expected_smt2 = \
        '(set-logic QF_BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#x00))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 16)

    var = mk_var(bv8, 'q')
    exists = mk_term(Kind.EXISTS, [
        var,
        mk_term(Kind.EQUAL, [
            mk_bv_zero(bv8),
            mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(exists);

    expected_smt2 = \
        '(set-logic BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#b00000000))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n'\
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula()

    expected_smt2 = \
        '(set-logic BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '(_ bv0 8)))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))\n'\
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 10)

    expected_smt2 = \
        '(set-logic BV)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#x00))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))\n'\
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 16)

    fpconst16 = mk_const(mk_fp_sort(5, 11), 'fp16')
    funfp = mk_const(
            mk_fun_sort(
                [mk_bv_sort(8), mk_fp_sort(5, 11), mk_bv_sort(32)],
                mk_fp_sort(5, 11)),
            'fun_fp')
    apply = mk_term(Kind.APPLY, [
            funfp,
            bvconst8,
            fpconst16,
            mk_term(Kind.BV_ZERO_EXTEND, [mk_bv_ones(mk_bv_sort(23))], [9])])
    bitwuzla.assert_formula(mk_term(Kind.FP_LEQ, [apply, fpconst16]))

    expected_smt2 = \
        '(set-logic UFBVFP)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(declare-const fp16 (_ FloatingPoint 5 11))\n' \
        + '(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
        + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#b00000000))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n'\
        + '(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) ' \
        + '#b11111111111111111111111)) fp16))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula()

    expected_smt2 = \
        '(set-logic UFBVFP)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(declare-const fp16 (_ FloatingPoint 5 11))\n' \
        + '(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
        + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '(_ bv0 8)))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q))))\n'\
        + '(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) ' \
        + '(_ bv8388607 23))) fp16))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 10)

    expected_smt2 = \
        '(set-logic UFBVFP)\n' \
        + '(declare-const b Bool)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(declare-const fp16 (_ FloatingPoint 5 11))\n' \
        + '(declare-fun fun_fp ((_ BitVec 8) (_ FloatingPoint 5 11) ' \
        + '(_ BitVec 32)) (_ FloatingPoint 5 11))\n' \
        + '(assert b)\n' \
        + '(assert (= ((lambda ((z (_ BitVec 8))) (bvadd z bv8)) bv8) ' \
        + '#x00))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q))))\n'\
        + '(assert (fp.leq (fun_fp bv8 fp16 ((_ zero_extend 9) ' \
        + '#b11111111111111111111111)) fp16))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula('smt2', 16)


def test_print_formula2():
    bitwuzla = Bitwuzla()
    bv1      = mk_bv_sort(1)
    bv8      = mk_bv_sort(8)
    bvconst8 = mk_const(bv8, 'bv8')
    ar1_1    = mk_array_sort(bv1, bv1)
    a        = mk_const(ar1_1, "a")
    b        = mk_const(ar1_1, "b")
    z        = mk_bv_zero(bv1)
    e        = mk_term(Kind.ARRAY_SELECT, [a, z])
    c        = mk_term(Kind.EQUAL, [a, b])
    var = mk_var(bv8, 'q')
    exists = mk_term(Kind.EXISTS, [
        var,
        mk_term(Kind.EQUAL, [
            mk_bv_zero(bv8),
            mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [e, z]))
    bitwuzla.assert_formula(c)
    bitwuzla.assert_formula(exists)

    expected_smt2 = \
        '(set-logic ABV)\n' \
        + '(declare-const bv8 (_ BitVec 8))\n' \
        + '(declare-const a (Array (_ BitVec 1) (_ BitVec 1)))\n' \
        + '(declare-const b (Array (_ BitVec 1) (_ BitVec 1)))\n' \
        + '(assert (= (select a #b0) #b0))\n' \
        + '(assert (= a b))\n' \
        + '(assert (exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q))))\n'\
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula()


def test_print_formula3():
    bitwuzla = Bitwuzla()
    bv32 = mk_bv_sort(32)
    n    = mk_const(bv32, 'n')
    sim  = mk_const(bv32, '~')
    zero = mk_bv_zero(bv32)
    two  = mk_bv_value(bv32, 2)
    bitwuzla.assert_formula(mk_term(Kind.DISTINCT, [
         zero, mk_term(Kind.BV_ADD, [n, sim])]))
    bitwuzla.push(1)
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [
        mk_term(Kind.BV_ADD, [n, two]),
        mk_term(Kind.BV_NEG, [
            mk_term(Kind.BV_ADD, [sim, mk_term(Kind.BV_MUL, [n, two])])])]))
    bitwuzla.push(1)
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [
        zero, mk_term(Kind.BV_ADD, [n, mk_bv_one(bv32)])]))

    expected_smt2 = \
        '(set-logic QF_BV)\n' \
        + '(declare-const n (_ BitVec 32))\n' \
        + '(declare-const ~ (_ BitVec 32))\n' \
        + '(assert (distinct #b00000000000000000000000000000000 (bvadd n ~)))\n'\
        + '(push 1)\n' \
        + '(assert (= (bvadd n #b00000000000000000000000000000010) (bvneg ' \
        + '(bvadd ~ (bvmul n ' \
        + '#b00000000000000000000000000000010)))))\n' \
        + '(push 1)\n' \
        + '(assert (= #b00000000000000000000000000000000 (bvadd n ' \
        + '#b00000000000000000000000000000001)))\n' \
        + '(check-sat)\n' \
        + '(exit)\n'
    assert expected_smt2 == bitwuzla.print_formula()

# ----------------------------------------------------------------------------
# Statistics
# ----------------------------------------------------------------------------

def test_statistics():
    bitwuzla = Bitwuzla()
    bitwuzla.assert_formula(mk_const(mk_bool_sort()))
    stats = bitwuzla.statistics()
    for name, val in stats.items():
        print(f'{name}: {val}')

# ----------------------------------------------------------------------------
# Sort
# ----------------------------------------------------------------------------

def test_sort_hash():
    hash(mk_bv_sort(8))


def test_sort_bv_size():
    with pytest.raises(BitwuzlaException):
        mk_fp_sort(5, 11).bv_size()
    assert mk_bv_sort(8).bv_size() == 8


def test_sort_fp_exp_size():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).fp_exp_size()
    assert mk_fp_sort(5, 11).fp_exp_size() == 5


def test_sort_fp_sig_size():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).fp_sig_size()
    assert mk_fp_sort(5, 11).fp_sig_size() == 11


def test_sort_array_index():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(23).array_index()
    assert mk_array_sort(mk_bv_sort(8), mk_fp_sort(5, 11)).array_index().\
            is_bv()


def test_sort_array_element():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(23).array_element()
    assert mk_array_sort(mk_bv_sort(8), mk_fp_sort(5, 11)).array_element().\
            is_fp()


def test_sort_fun_domain_sorts():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).fun_domain()
    fun_sort = mk_fun_sort(
            [mk_bv_sort(8), mk_fp_sort(5, 11), mk_bv_sort(32)], mk_bv_sort(8))
    domain = fun_sort.fun_domain()
    assert len(domain) == 3
    assert domain[0] == mk_bv_sort(8)
    assert domain[1] == mk_fp_sort(5, 11)
    assert domain[2] == mk_bv_sort(32)


def test_sort_fun_codomain():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).fun_codomain()
    fun_sort = mk_fun_sort(
            [mk_bv_sort(8), mk_fp_sort(5, 11), mk_bv_sort(32)], mk_bv_sort(8))
    assert fun_sort.fun_codomain() == mk_bv_sort(8)


def test_sort_fun_arity():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).fun_arity()
    fun_sort = mk_fun_sort(
            [mk_bv_sort(8), mk_fp_sort(5, 11), mk_bv_sort(32)], mk_bv_sort(8))
    assert fun_sort.fun_arity() == 3


def test_sort_uninterpreted_symbol():
    with pytest.raises(BitwuzlaException):
        mk_bv_sort(8).uninterpreted_symbol()
        s1 = mk_uninterpreted_sort()
        s2 = mk_uninterpreted_sort('foo')
        s3 = mk_uninterpreted_sort('foo')
        s4 = mk_uninterpreted_sort('bar')
        assert not s1.uninterpreted_symbol()
        assert s2.uninterpreted_symbol() == 'foo'
        assert s3.uninterpreted_symbol() == 'foo'
        assert s4.uninterpreted_symbol() == 'bar'


def test_sort_is_equal():
    bv8 = mk_bv_sort(8)
    assert mk_bv_sort(8) == bv8
    assert mk_bv_sort(9) != bv8


def test_sort_is_array():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = mk_uninterpreted_sort()
    assert arr_sort_bv.is_array()
    assert arr_sort_bvfp.is_array()
    assert arr_sort_fpbv.is_array()
    assert not fun_sort.is_array()
    assert not fun_sort_fp.is_array()
    assert not bv_sort8.is_array()
    assert not fp_sort16.is_array()
    assert not un_sort.is_array()


def test_sort_is_bv():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    un_sort = mk_uninterpreted_sort()
    assert mk_bv_sort(1).is_bv()
    assert mk_bv_sort(8).is_bv()
    assert mk_bv_sort(23).is_bv()
    assert mk_bv_sort(32).is_bv()
    assert not mk_fp_sort(5, 11).is_bv()
    assert not arr_sort_bv.is_bv()
    assert not arr_sort_bvfp.is_bv()
    assert not arr_sort_fpbv.is_bv()
    assert not fun_sort.is_bv()
    assert not un_sort.is_bv()


def test_sort_is_fp():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    fp_sort32 = mk_fp_sort(8, 24)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    un_sort = mk_uninterpreted_sort()
    assert fp_sort16.is_fp()
    assert fp_sort32.is_fp()
    assert not bv_sort8.is_fp()
    assert not arr_sort_bv.is_fp()
    assert not arr_sort_bvfp.is_fp()
    assert not arr_sort_fpbv.is_fp()
    assert not fun_sort.is_fp()
    assert not un_sort.is_fp()


def test_sort_is_fun():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = mk_uninterpreted_sort()
    assert fun_sort.is_fun()
    assert fun_sort_fp.is_fun()
    assert not arr_sort_bv.is_fun()
    assert not arr_sort_bvfp.is_fun()
    assert not arr_sort_fpbv.is_fun()
    assert not bv_sort8.is_fun()
    assert not fp_sort16.is_fun()
    assert not un_sort.is_fun()


def test_sort_is_rm():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = mk_uninterpreted_sort()
    assert mk_rm_sort().is_rm()
    assert not fun_sort.is_rm()
    assert not fun_sort_fp.is_rm()
    assert not arr_sort_bv.is_rm()
    assert not arr_sort_bvfp.is_rm()
    assert not arr_sort_fpbv.is_rm()
    assert not bv_sort8.is_rm()
    assert not fp_sort16.is_rm()
    assert not un_sort.is_rm()


def test_sort_is_uninterpreted():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    fp_sort16 = mk_fp_sort(5, 11)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = mk_uninterpreted_sort()
    assert un_sort.is_uninterpreted()
    assert not mk_rm_sort().is_uninterpreted()
    assert not fun_sort.is_uninterpreted()
    assert not fun_sort_fp.is_uninterpreted()
    assert not arr_sort_bv.is_uninterpreted()
    assert not arr_sort_bvfp.is_uninterpreted()
    assert not arr_sort_fpbv.is_uninterpreted()
    assert not bv_sort8.is_uninterpreted()
    assert not fp_sort16.is_uninterpreted()


def test_sort_str():
    assert f'{mk_bv_sort(1)}{mk_bv_sort(8)}{mk_rm_sort()}{mk_fp_sort(8, 24)}' \
            == '(_ BitVec 1)(_ BitVec 8)RoundingMode(_ FloatingPoint 8 24)'


def test_regr1():
    bv_sort8 = mk_bv_sort(8)
    fun_sort = mk_fun_sort([bv_sort8], bv_sort8)
    arr_sort = mk_array_sort(bv_sort8, bv_sort8)
    args = [mk_const(bv_sort8, 'x'), mk_const(fun_sort, 'f')]
    with pytest.raises(BitwuzlaException):
        mk_term(Kind.APPLY, args)


def test_regr2():
    bv_sort8 = mk_bv_sort(8)
    fun_sort = mk_fun_sort([bv_sort8], bv_sort8)
    arr_sort = mk_array_sort(bv_sort8, bv_sort8)
    assert fun_sort != arr_sort
    fun = mk_const(fun_sort)
    array = mk_const(arr_sort)
    assert arr_sort == array.sort()
    assert fun_sort == fun.sort()
    assert fun.sort() != array.sort()
    assert fun.sort().is_fun()
    assert array.sort().is_array()


# ----------------------------------------------------------------------------
# Term
# ----------------------------------------------------------------------------

def test_term_hash():
    hash(mk_const(mk_bv_sort(8)))


def test_term_sort():
    assert mk_const(mk_bv_sort(8)).sort() == mk_bv_sort(8)


def test_term_symbol():
    x = mk_const(mk_bv_sort(8), 'x')
    assert x.symbol() and x.symbol() == 'x'
    x = mk_const(mk_bv_sort(8))
    assert not x.symbol()


def test_term_is_const():
    bv_sort8 = mk_bv_sort(8)
    bv_sort32 = mk_bv_sort(32)
    arr_sort_bv = mk_array_sort(bv_sort32, bv_sort8)
    fp_sort16 = mk_fp_sort(5, 11)
    fun_sort = mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    assert mk_const(arr_sort_bv).is_const()
    assert mk_const(fun_sort).is_const()
    assert mk_const(mk_bv_sort(1)).is_const()
    assert mk_const(fp_sort16).is_const()
    assert mk_const(mk_rm_sort()).is_const()
    assert not mk_bv_one(mk_bv_sort(1)).is_const()
    assert not mk_term(
            Kind.ARRAY_STORE,
            [
                mk_const(arr_sort_bv),
                mk_const(bv_sort32), mk_bv_zero(bv_sort8)
            ]).is_const()


def test_term_is_var():
    assert mk_var(mk_bv_sort(1)).is_variable()
    assert mk_var(mk_bv_sort(8)).is_variable()
    assert not mk_fp_pos_zero(mk_fp_sort(8, 24)).is_variable()


def test_term_is_value():
    assert mk_bv_one(mk_bv_sort(1)).is_value()
    assert mk_fp_nan(mk_fp_sort(8, 24)).is_value()
    assert not mk_const(mk_fp_sort(5, 11)).is_value()
    var = mk_var(mk_bv_sort(8))
    exists = mk_term(Kind.EXISTS, [
        var,
        mk_term(Kind.EQUAL, [
            mk_bv_zero(mk_bv_sort(8)),
            mk_term(Kind.BV_MUL, [mk_const(mk_bv_sort(8)), var])])])
    assert not exists.is_value()


def test_term_is_true():
    assert mk_true().is_true()
    assert not mk_false().is_true()
    assert not mk_bv_one(mk_bv_sort(1)).is_true()


def test_term_is_false():
    assert mk_false().is_false()
    assert not mk_true().is_false()
    assert not mk_bv_zero(mk_bv_sort(1)).is_false()


def test_term_is_bv_value_zero():
    assert mk_bv_zero(mk_bv_sort(8)).is_bv_value_zero()
    assert not mk_bv_one(mk_bv_sort(1)).is_bv_value_zero()
    assert not mk_bv_ones(mk_bv_sort(23)).is_bv_value_zero()
    assert not mk_bv_min_signed(mk_bv_sort(8)).is_bv_value_zero()
    assert not mk_bv_max_signed(mk_bv_sort(8)).is_bv_value_zero()


def test_term_is_bv_value_one():
    assert mk_bv_one(mk_bv_sort(1)).is_bv_value_one()
    assert not mk_bv_zero(mk_bv_sort(8)).is_bv_value_one()
    assert not mk_bv_ones(mk_bv_sort(23)).is_bv_value_one()
    assert not mk_bv_min_signed(mk_bv_sort(8)).is_bv_value_one()
    assert not mk_bv_max_signed(mk_bv_sort(8)).is_bv_value_one()


def test_term_is_bv_value_ones():
    assert mk_bv_ones(mk_bv_sort(23)).is_bv_value_ones()
    assert not mk_bv_zero(mk_bv_sort(8)).is_bv_value_ones()
    assert mk_bv_one(mk_bv_sort(1)).is_bv_value_ones()
    assert not mk_bv_min_signed(mk_bv_sort(8)).is_bv_value_ones()
    assert not mk_bv_max_signed(mk_bv_sort(8)).is_bv_value_ones()


def test_term_is_bv_value_min_signed():
    assert mk_bv_min_signed(mk_bv_sort(8)).is_bv_value_min_signed()
    assert not mk_bv_zero(mk_bv_sort(8)).is_bv_value_min_signed()
    assert mk_bv_one(mk_bv_sort(1)).is_bv_value_min_signed()
    assert not mk_bv_ones(mk_bv_sort(23)).is_bv_value_min_signed()
    assert not mk_bv_max_signed(mk_bv_sort(8)).is_bv_value_min_signed()


def test_term_is_bv_value_max_signed():
    assert mk_bv_max_signed(mk_bv_sort(8)).is_bv_value_max_signed()
    assert not mk_bv_zero(mk_bv_sort(8)).is_bv_value_max_signed()
    assert not mk_bv_one(mk_bv_sort(1)).is_bv_value_max_signed()
    assert not mk_bv_ones(mk_bv_sort(23)).is_bv_value_max_signed()
    assert not mk_bv_min_signed(mk_bv_sort(8)).is_bv_value_max_signed()


def test_term_is_fp_value_pos_zero():
    assert mk_fp_pos_zero(mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not mk_fp_neg_zero(mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not mk_fp_pos_inf(mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not mk_fp_neg_inf(mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not mk_fp_nan(mk_fp_sort(8, 24)).is_fp_value_pos_zero()


def test_term_is_fp_value_neg_zero():
    assert mk_fp_neg_zero(mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not mk_fp_pos_zero(mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not mk_fp_pos_inf(mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not mk_fp_neg_inf(mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not mk_fp_nan(mk_fp_sort(8, 24)).is_fp_value_neg_zero()


def test_term_is_fp_value_pos_inf():
    assert mk_fp_pos_inf(mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not mk_fp_pos_zero(mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not mk_fp_neg_zero(mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not mk_fp_neg_inf(mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not mk_fp_nan(mk_fp_sort(8, 24)).is_fp_value_pos_inf()


def test_term_is_fp_value_neg_inf():
    assert mk_fp_neg_inf(mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not mk_fp_pos_zero(mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not mk_fp_neg_zero(mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not mk_fp_pos_inf(mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not mk_fp_nan(mk_fp_sort(8, 24)).is_fp_value_neg_inf()


def test_term_is_fp_value_nan():
    assert mk_fp_nan(mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not mk_fp_pos_zero(mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not mk_fp_neg_zero(mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not mk_fp_pos_inf(mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not mk_fp_neg_inf(mk_fp_sort(8, 24)).is_fp_value_nan()


def test_term_is_rm_value_rna():
    assert mk_rm_value(RoundingMode.RNA).is_rm_value_rna()
    assert not mk_rm_value(RoundingMode.RNE).is_rm_value_rna()
    assert not mk_rm_value(RoundingMode.RTN).is_rm_value_rna()
    assert not mk_rm_value(RoundingMode.RTP).is_rm_value_rna()
    assert not mk_rm_value(RoundingMode.RTZ).is_rm_value_rna()


def test_term_is_rm_value_rne():
    assert not mk_rm_value(RoundingMode.RNA).is_rm_value_rne()
    assert mk_rm_value(RoundingMode.RNE).is_rm_value_rne()
    assert not mk_rm_value(RoundingMode.RTN).is_rm_value_rne()
    assert not mk_rm_value(RoundingMode.RTP).is_rm_value_rne()
    assert not mk_rm_value(RoundingMode.RTZ).is_rm_value_rne()


def test_term_is_rm_value_rtn():
    assert not mk_rm_value(RoundingMode.RNA).is_rm_value_rtn()
    assert not mk_rm_value(RoundingMode.RNE).is_rm_value_rtn()
    assert mk_rm_value(RoundingMode.RTN).is_rm_value_rtn()
    assert not mk_rm_value(RoundingMode.RTP).is_rm_value_rtn()
    assert not mk_rm_value(RoundingMode.RTZ).is_rm_value_rtn()


def test_term_is_rm_value_rtp():
    assert not mk_rm_value(RoundingMode.RNA).is_rm_value_rtp()
    assert not mk_rm_value(RoundingMode.RNE).is_rm_value_rtp()
    assert not mk_rm_value(RoundingMode.RTN).is_rm_value_rtp()
    assert mk_rm_value(RoundingMode.RTP).is_rm_value_rtp()
    assert not mk_rm_value(RoundingMode.RTZ).is_rm_value_rtp()


def test_term_is_rm_value_rtz():
    assert not mk_rm_value(RoundingMode.RNA).is_rm_value_rtz()
    assert not mk_rm_value(RoundingMode.RNE).is_rm_value_rtz()
    assert not mk_rm_value(RoundingMode.RTN).is_rm_value_rtz()
    assert not mk_rm_value(RoundingMode.RTP).is_rm_value_rtz()
    assert mk_rm_value(RoundingMode.RTZ).is_rm_value_rtz()


def test_term_print():
    bv1  = mk_bv_sort(1)
    and_bv_const1 = mk_term(
            Kind.EQUAL,
            [
                mk_bv_one(bv1),
                mk_term(
                    Kind.BV_AND,
                    [mk_bv_one(bv1), mk_const(bv1, 'bv1')])
            ])
    var = mk_var(mk_bv_sort(8), 'q')
    exists = mk_term(Kind.EXISTS, [
        var,
        mk_term(Kind.EQUAL, [
            mk_bv_zero(mk_bv_sort(8)),
            mk_term(Kind.BV_MUL, [mk_const(mk_bv_sort(8), 'bv8'), var])])])
    expected = '(= #b1 (bvand #b1 bv1))' \
               + '(exists ((q (_ BitVec 8))) (= #b00000000 (bvmul bv8 q)))' \
               + '(= (_ bv1 1) (bvand (_ bv1 1) bv1))' \
               + '(exists ((q (_ BitVec 8))) (= (_ bv0 8) (bvmul bv8 q)))' \
               + '(= #b1 (bvand #b1 bv1))' \
               + '(exists ((q (_ BitVec 8))) (= #x00 (bvmul bv8 q)))'
    res = and_bv_const1.str() + exists.str() \
          + and_bv_const1.str(10) + exists.str(10) \
          + and_bv_const1.str(16) +  exists.str(16)
    assert res == expected

    bv5  = mk_bv_sort(5)
    bv10 = mk_bv_sort(10)
    bv4  = mk_bv_sort(4)
    bv8  = mk_bv_sort(8)

    t = mk_fp_value(mk_bv_one(bv1),
                    mk_bv_value(bv5, 3),
                    mk_bv_value(bv10, 23))

    expected = '(fp #b1 #b00011 #b0000010111)' \
               + '(fp (_ bv1 1) (_ bv3 5) (_ bv23 10))' \
               + '(fp #b1 #b00011 #b0000010111)'
    res = t.str() + t.str(10) + t.str(16)
    assert res == expected

    t = mk_fp_value(mk_bv_one(bv1),
                    mk_bv_value(bv4, 3),
                    mk_bv_value(bv8, 23))

    expected = '(fp #b1 #b0011 #b00010111)' \
               + '(fp (_ bv1 1) (_ bv3 4) (_ bv23 8))' \
               + '(fp #b1 #b0011 #b00010111)'
    res = t.str() + t.str(10) + t.str(16)
    assert res == expected


def test_term_print_regr0():
    res = mk_rm_value(RoundingMode.RNA).str() + '\n' \
          + mk_rm_value(RoundingMode.RNE).str() + '\n' \
          + mk_rm_value(RoundingMode.RTN).str() + '\n' \
          + mk_rm_value(RoundingMode.RTP).str() + '\n' \
          + mk_rm_value(RoundingMode.RTZ).str()
    assert res == "RNA\nRNE\nRTN\nRTP\nRTZ"


def test_term_print_regr1():
    bv_sort1  = mk_bv_sort(1)
    bv_sort5  = mk_bv_sort(5)
    bv_sort10 = mk_bv_sort(10)

    fp_val = mk_fp_value(mk_bv_zero(bv_sort1),
                         mk_bv_zero(bv_sort5),
                         mk_bv_zero(bv_sort10))
    assert fp_val.str() == '(fp #b0 #b00000 #b0000000000)'

    fp_val = mk_fp_value(mk_bv_one(bv_sort1),
                         mk_bv_zero(bv_sort5),
                         mk_bv_zero(bv_sort10))
    assert fp_val.str() == '(fp #b1 #b00000 #b0000000000)'

    fp_val = mk_fp_value(mk_bv_zero(bv_sort1),
                         mk_bv_zero(bv_sort5),
                         mk_bv_one(bv_sort10))
    assert fp_val.str() == '(fp #b0 #b00000 #b0000000001)'

    fp_val = mk_fp_value(mk_bv_one(bv_sort1),
                         mk_bv_zero(bv_sort5),
                         mk_bv_one(bv_sort10))
    assert fp_val.str() == '(fp #b1 #b00000 #b0000000001)'


def test_terms_indexed():
    fp_term = mk_const(mk_fp_sort(5, 11))
    bv_term = mk_const(mk_bv_sort(8))
    rm      = mk_rm_value(RoundingMode.RNE)

    idx = mk_term(Kind.FP_TO_SBV, [rm, fp_term], [8])
    assert idx.num_indices() == 1
    indices = idx.indices()
    assert len(indices) == 1
    assert indices[0] == 8

    idx = mk_term(Kind.FP_TO_UBV, [rm, fp_term], [9])
    assert idx.num_indices() == 1
    indices = idx.indices()
    assert len(indices) == 1
    assert indices[0] == 9

    idx = mk_term(Kind.FP_TO_FP_FROM_BV, [bv_term], [3, 5])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 3
    assert indices[1] == 5

    idx = mk_term(Kind.FP_TO_FP_FROM_FP, [rm, fp_term], [7, 18])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 7
    assert indices[1] == 18

    idx = mk_term(Kind.FP_TO_FP_FROM_SBV, [rm, bv_term], [8, 24])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 8
    assert indices[1] == 24

    idx = mk_term(Kind.FP_TO_FP_FROM_UBV, [rm, bv_term], [5, 11])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 5
    assert indices[1] == 11

    idx = mk_term(Kind.BV_EXTRACT, [bv_term], [6, 0])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 6
    assert indices[1] == 0


def test_terms():
    bv16 = mk_bv_sort(16)
    fp16 = mk_fp_sort(5, 11)
    array_sort = mk_array_sort(bv16, bv16)
    domain = [bv16, bv16, bv16]
    fun_sort = mk_fun_sort(domain, bv16)

    fp_args = [
            mk_rm_value(RoundingMode.RNA),
            mk_const(fp16),
            mk_const(fp16),
            mk_const(fp16)
        ]

    bv_args = [
            mk_const(bv16),
            mk_const(bv16),
            mk_const(bv16),
            mk_const(bv16)
        ]

    bool_args = [mk_const(mk_bool_sort()), mk_const(mk_bool_sort())]

    for kind in Kind:
        if kind == Kind.CONSTANT \
           or kind == Kind.CONST_ARRAY \
           or kind == Kind.VALUE \
           or kind == Kind.VARIABLE:
               continue

        term = None

        # Boolean
        if kind == Kind.NOT:
               term = mk_term(kind, [bool_args[0]])
               break

        if kind == Kind.AND \
           or kind == Kind.IFF \
           or kind == Kind.IMPLIES \
           or kind == Kind.OR \
           or kind == Kind.XOR:
               term = mk_term(kind, bool_args)
               break

        # BV Unary
        if kind == Kind.BV_DEC \
           or kind == Kind.BV_INC \
           or kind == Kind.BV_NEG \
           or kind == Kind.BV_NOT \
           or kind == Kind.BV_REDAND \
           or kind == Kind.BV_REDOR \
           or kind == Kind.BV_REDXOR:
               term = mk_term(kind, [bv_args[0]])
               break

        # BV Binary
        if  kind == Kind.BV_ASHR \
            or kind == Kind.BV_COMP \
            or kind == Kind.BV_NAND \
            or kind == Kind.BV_NOR \
            or kind == Kind.BV_ROL \
            or kind == Kind.BV_ROR \
            or kind == Kind.BV_SADD_OVERFLOW \
            or kind == Kind.BV_SDIV_OVERFLOW \
            or kind == Kind.BV_SDIV \
            or kind == Kind.BV_SGE \
            or kind == Kind.BV_SGT \
            or kind == Kind.BV_SHL \
            or kind == Kind.BV_SHR \
            or kind == Kind.BV_SLE \
            or kind == Kind.BV_SLT \
            or kind == Kind.BV_SMOD \
            or kind == Kind.BV_SMUL_OVERFLOW \
            or kind == Kind.BV_SREM \
            or kind == Kind.BV_SSUB_OVERFLOW \
            or kind == Kind.BV_SUB \
            or kind == Kind.BV_UADD_OVERFLOW \
            or kind == Kind.BV_UDIV \
            or kind == Kind.BV_UGE \
            or kind == Kind.BV_UGT \
            or kind == Kind.BV_ULE \
            or kind == Kind.BV_ULT \
            or kind == Kind.BV_UMUL_OVERFLOW \
            or kind == Kind.BV_UREM \
            or kind == Kind.BV_USUB_OVERFLOW \
            or kind == Kind.BV_XNOR:
                term = mk_term(kind, [bv_args[0], bv_args[1]])
                break

        # BV Binary+
        if kind == Kind.BV_ADD \
           or kind == Kind.BV_AND \
           or kind == Kind.BV_CONCAT \
           or kind == Kind.BV_MUL \
           or kind == Kind.BV_OR \
           or kind == Kind.BV_XOR:
               term = mk_term(kind, bv_args)
               break

        if kind == Kind.DISTINCT or kind == Kind.EQUAL:
            term = mk_term(kind, bv_args)
            break

        # BV indexed
        if kind == Kind.BV_EXTRACT:
            term = mk_term(kind, [bv_args[0]], [3, 2])
            break

        if kind == Kind.BV_REPEAT \
           or kind == Kind.BV_ROLI \
           or kind == Kind.BV_RORI \
           or kind == Kind.BV_SIGN_EXTEND \
           or kind == Kind.BV_ZERO_EXTEND:
               term = mk_term(kind, [bv_args[0]], [5])
               break

        # Arrays
        if kind == Kind.ARRAY_SELECT:
            term = mk_term(kind, [mk_const(array_sort), bv_args[0]])
            break

        if kind == Kind.ARRAY_STORE:
            term = mk_term(kind, [mk_const(array_sort), bv_args[0], bv_args[1]])
            break

        if kind == Kind.APPLY:
            term = mk_term(
                    kind, [mk_const(fun_sort), bv_args[0], bv_args[1], bv_args[2]])
            break

        # Binder
        if kind == Kind.EXISTS \
           or kind == Kind.FORALL \
           or kind == Kind.LAMBDA:
               bvars = [mk_var(d_bv_sort16), mk_var(d_bv_sort16)]
               # body
               term = mk_term(
                       kind, [bvars[0], bvars[1], mk_term(Kind.BV_SLT, bvars)])
               break;

        # FP Unary
        if kind == Kind.FP_ABS \
           or kind == Kind.FP_IS_INF \
           or kind == Kind.FP_IS_NAN \
           or kind == Kind.FP_IS_NEG \
           or kind == Kind.FP_IS_NORMAL \
           or kind == Kind.FP_IS_POS \
           or kind == Kind.FP_IS_SUBNORMAL \
           or kind == Kind.FP_IS_ZERO \
           or kind == Kind.FP_NEG:
               term = mk_term(kind, [fp_args[1]])
               break

        # FP Binary
        if kind == Kind.FP_EQUAL \
           or kind == Kind.FP_GEQ \
           or kind == Kind.FP_GT \
           or kind == Kind.FP_LEQ \
           or kind == Kind.FP_LT \
           or kind == Kind.FP_MAX \
           or kind == Kind.FP_MIN \
           or kind == Kind.FP_REM:
               term = mk_term(kind, [fp_args[1], fp_args[2]])
               break

        if kind == Kind.FP_SQRT or kind == Kind.FP_RTI:
            term = mk_term(kind, [fp_args[0], fp_args[1]])
            break

        # FP Ternary
        if  kind == Kind.FP_ADD \
            or kind == Kind.FP_DIV \
            or kind == Kind.FP_MUL \
            or kind == Kind.FP_SUB:
                term = mk_term(kind, [fp_args.begin(), fp_args.end() - 1])
                break

        if kind == Kind.FP_FP:
            term = mk_term(
                    kind, [mk_const(mk_bv_sort(1)), bv_args[0], bv_args[1]])
            break

        # FP Quaternery
        if kind == Kind.FP_FMA:
            term = mk_term(kind, fp_args)
            break

        # FP indexed
        if kind == Kind.FP_TO_FP_FROM_BV:
            term = mk_term(kind, [bv_args[0]], [5, 11])
            break

        if kind == Kind.FP_TO_FP_FROM_SBV or kind == Kind.FP_TO_FP_FROM_UBV:
            term = mk_term(kind, [fp_args[0], bv_args[0]], [5, 11])
            break

        if kind == Kind.FP_TO_FP_FROM_FP:
            term = mk_term(kind, [fp_args[0], fp_args[1]], [5, 11])
            break

        if kind == Kind.FP_TO_SBV or kind == Kind.FP_TO_UBV:
            term = mk_term(kind, [fp_args[0], fp_args[1]], [16])
            break

        # Others
        if kind == Kind.ITE:
            term = mk_term(kind, [bool_args[0], bv_args[0], bv_args[1]])
            break

        # no unhandled kind
        assert term

        children = term.children()
        size     = len(children)

        if term.is_const() or term.is_variable() or term.is_value():
            assert size == 0
            continue

        assert size > 0
        for i in range(0, size):
            assert term[i] == children[i]
            assert children[i]

        tterm = None
        if term.kind() == Kind.CONST_ARRAY:
            assert size == 1
            term = mk_const_array(term.sort(), children[0])
        else:
          kind = term.kind()
          if term.num_indices() > 0:
            tterm = mk_term(kind, children, term.indices())
          elif kind == Kind.LAMBDA \
               or kind == Kind.FORALL \
               or kind == Kind.EXISTS:
               tterm = term
          else:
              assert kind != Kind.BV_NOT or size == 1
              tterm = mk_term(kind, children)
        assert tterm == term

    assert mk_const(mk_bv_sort(8)).kind() == Kind.CONSTANT
    assert len(mk_const(mk_bv_sort(8)).children()) == 0

    assert mk_const(mk_rm_sort()).kind() == Kind.CONSTANT
    assert len(mk_const(mk_rm_sort()).children()) == 0

    assert mk_const(mk_uninterpreted_sort()).kind() == Kind.CONSTANT
    assert len(mk_const(mk_uninterpreted_sort()).children()) == 0

    bv_var = mk_var(bv16)
    assert bv_var.kind() == Kind.VARIABLE
    assert len(bv_var.children()) == 0

    rm_val = mk_rm_value(RoundingMode.RNA)
    assert rm_val.kind() == Kind.VALUE
    assert len(rm_val.children()) == 0

    fp_from_real_val = mk_fp_value(fp16, rm_val, '1.1')
    assert fp_from_real_val.kind() == Kind.VALUE
    assert len(fp_from_real_val.children()) == 0

    fp_from_real = mk_fp_value(fp16, mk_const(mk_rm_sort()), '1.1')
    assert fp_from_real.kind() == Kind.ITE
    assert len(fp_from_real.children()) > 0

    fp_from_rat_val = mk_fp_value(fp16, rm_val, '1', '2')
    assert fp_from_rat_val.kind() == Kind.VALUE
    assert len(fp_from_rat_val.children()) == 0

    fp_from_rat = mk_fp_value(fp16, mk_const(mk_rm_sort()), '1', '2')
    assert fp_from_rat.kind() == Kind.ITE
    assert len(fp_from_rat.children()) > 0

    fp_nan = mk_fp_nan(fp16)
    assert fp_nan.kind() == Kind.VALUE
    assert len(fp_nan.children()) == 0

    bv_one = mk_bv_one(bv16)
    assert bv_one.kind() == Kind.VALUE
    assert len(bv_one.children()) == 0

    bv_val = mk_bv_value(bv16, '43', 10)
    assert bv_val.kind() == Kind.VALUE
    assert len(bv_val.children()) == 0

    # TODO enable when implemented
    # const_array = mk_const_array(array_sort, bv_val)
    # assert const_array.kind() == Kind.VALUE
    # assert len(const_array.children()) == 0


def test_substitute1():
    bv16 = mk_bv_sort(16)
    bv_const = mk_const(bv16)
    bv_value = mk_bv_value(bv16, '143', 10)

    # simple substitution const -> value
    substs = {bv_const: bv_value}
    result = substitute_term(bv_const, substs)
    assert result == bv_value


def test_substitute2():
    bv16 = mk_bv_sort(16)
    bv_const = mk_const(bv16)
    bv_value = mk_bv_value(bv16, '143', 10)
    # (sdiv x y) -> (sdiv value y)
    x = mk_const(bv16)
    y = mk_const(bv16)

    substs = {x: bv_value}

    result = substitute_term(mk_term(Kind.BV_SDIV, [x, y]), substs)
    assert result == mk_term(Kind.BV_SDIV, [bv_value, y])


def test_substitute3():
    bv16 = mk_bv_sort(16)
    domain = [bv16, bv16, bv16]
    fun_sort   = mk_fun_sort(domain, mk_bool_sort())
    bv_const = mk_const(bv16)
    bv_value = mk_bv_value(bv16, '143', 10)
    # partial substitution of variables in quantified formula
    args = [mk_const(fun_sort),
            mk_var(bv16, 'x'),
            mk_var(bv16, 'y'),
            mk_var(bv16, 'z')]
    args.append(mk_term(Kind.APPLY, args))
    q = mk_term(Kind.FORALL, args[1:])

    substs = {args[1]: mk_const(bv16, 'cx'), args[2]: mk_const(bv16, 'cy')}

    apply = mk_term(
            Kind.APPLY, [args[0], substs[args[1]], substs[args[2]], args[3]])
    expected = mk_term(Kind.FORALL, [args[3], apply])

    result = substitute_term(q, substs)
    assert result == expected

def test_substitute4():
    bv16 = mk_bv_sort(16)
    domain = [bv16, bv16, bv16]
    fun_sort   = mk_fun_sort(domain, mk_bool_sort())
    array_sort = mk_array_sort(bv16, bv16)
    bv_const = mk_const(bv16)
    bv_value = mk_bv_value(bv16, '143', 10)
    # substitute term in constant array
    term = mk_const(bv16)
    const_array = mk_const_array(array_sort, term)

    substs = {term: bv_value}

    result = substitute_term(const_array, substs)
    expected = mk_const_array(array_sort, bv_value)
    assert result == expected
    assert result.kind() == Kind.CONST_ARRAY


def test_substitute4():
    bv8   = mk_bv_sort(8)
    x     = mk_const(bv8, 'x')
    one   = mk_bv_one(bv8)
    btrue = mk_true()
    addxx = mk_term(Kind.BV_ADD, [x, x])
    addoo = mk_term(Kind.BV_ADD, [one, one])

    with pytest.raises(BitwuzlaException):
        substitute_term(addxx, {one: btrue})

    assert substitute_term(addxx, {x: one}) == addoo
    assert substitute_term(addxx, {one: x}) == addxx

    # simultaneous substitution
    y     = mk_const(bv8, 'y')
    addxy = mk_term(Kind.BV_ADD, [x, y])
    addyo = mk_term(Kind.BV_ADD, [y, one])

    with pytest.raises(BitwuzlaException):
        substitute_term(addxy, {x: y, y: btrue})

    assert substitute_term(addxy, {x: y, y: one}) == addyo

    terms = [addxx, addxy]
    expected = [mk_term(Kind.BV_ADD, [y, y]), mk_term(Kind.BV_ADD, [y, x])]
    assert substitute_terms(terms, {x: y, y: x}) == expected


def test_term_print1():
    a = mk_const(mk_bv_sort(1), 'a')
    t = mk_term(Kind.BV_NOT, [a])
    assert t.str() == '(bvnot a)'


def test_term_print2():
    fn1_1 = mk_fun_sort([mk_bv_sort(1)], mk_bv_sort(1))
    t     = mk_const(fn1_1, 'f')
    assert t.str() == 'f'


def test_term_print3():
    ar1_1 = mk_array_sort(mk_bv_sort(1), mk_bv_sort(1))
    t     = mk_const(ar1_1, 'a')
    assert t.str() == 'a'


def test_arrayfun():
    bvsort = mk_bv_sort(4)
    domain = [bvsort]
    funsort = mk_fun_sort(domain, bvsort)
    arrsort = mk_array_sort(bvsort, bvsort)
    f       = mk_const(funsort, 'f')
    a       = mk_const(arrsort, 'a')
    assert f.sort() != a.sort()
    assert f.sort().is_fun()
    assert not a.sort().is_fun()
    assert not f.sort().is_array()
    assert a.sort().is_array()

# ----------------------------------------------------------------------------
# Parsing
# ----------------------------------------------------------------------------

def test_parser():
    filename = "parse.smt2";
    with open(filename, 'w') as smt2:
        smt2.write('(set-logic QF_BV)\n(check-sat)\n(exit)\n')
        smt2.close()

    options = Options()
    with pytest.raises(BitwuzlaException):
        Parser(options, '')
    with pytest.raises(BitwuzlaException):
        Parser(options, 'parsex.smt2')

    parser = Parser(options, filename)
    err = parser.parse(True)
    assert not err
    os.remove(filename)

# ----------------------------------------------------------------------------
# Termination function
# ----------------------------------------------------------------------------

def test_terminate():

    class TestTerminator:
        def __call__(self):
            return True

    bv4 = mk_bv_sort(4)
    x = mk_const(bv4)
    s = mk_const(bv4)
    t = mk_const(bv4)
    a = mk_term(Kind.AND,
                [
                    mk_term(
                        Kind.EQUAL,
                        [mk_term(Kind.BV_ADD, [x, x]), mk_bv_value(bv4, 3)]),
                    mk_term(
                        Kind.NOT,
                        [mk_term(Kind.BV_UADD_OVERFLOW, [x, x])])
                ])
    b = mk_term(Kind.DISTINCT,
                [
                    mk_term(
                        Kind.BV_MUL,
                        [s, mk_term(Kind.BV_MUL, [x, t])]),
                    mk_term(
                        Kind.BV_MUL,
                        [mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # solved by rewriting
    options = Options()
    options.set(Option.BV_SOLVER, 'bitblast')
    bitwuzla = Bitwuzla(options)
    bitwuzla.assert_formula(a)
    assert bitwuzla.check_sat() == Result.UNSAT

    options.set(Option.BV_SOLVER, 'prop')
    bitwuzla = Bitwuzla(options)
    bitwuzla.assert_formula(a)
    assert bitwuzla.check_sat() == Result.UNSAT

    # not solved by rewriting, should be terminated when configured
    tt = TestTerminator()
    options.set(Option.BV_SOLVER, 'bitblast')
    bitwuzla = Bitwuzla(options)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNSAT
    bitwuzla.configure_terminator(tt)
    assert bitwuzla.check_sat() == Result.UNKNOWN

    options.set(Option.BV_SOLVER, 'prop')
    bitwuzla = Bitwuzla(options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN


def test_terminate_sat():
    class TestTerminator:
        def __init__(self, time_limit):
            self.start_time = time.time()
            self.time_limit = time_limit

        def __call__(self):
            # Terminate after self.time_limit ms passed
            return (time.time() - self.start_time) * 1000 > self.time_limit

    bv32 = mk_bv_sort(32)
    x = mk_const(bv32)
    s = mk_const(bv32)
    t = mk_const(bv32)
    b = mk_term(Kind.DISTINCT,
                [
                    mk_term(Kind.BV_MUL, [s, mk_term(Kind.BV_MUL, [x, t])]),
                    mk_term(Kind.BV_MUL, [mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # not solved by bit-blasting without preprocessing, should be terminated in
    # the SAT solver when configured
    tt = TestTerminator(1)
    options = Options()
    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN

    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.SAT_SOLVER, 'kissat')
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN


def test_terminate_timeout_wrap():
    class TestTerminator:
        def __init__(self):
            self.terminated = False
        def __call__(self):
            self.terminated = True
            return True

    bv32 = mk_bv_sort(32)
    x = mk_const(bv32)
    s = mk_const(bv32)
    t = mk_const(bv32)
    b = mk_term(Kind.DISTINCT,
                [
                    mk_term(Kind.BV_MUL, [s, mk_term(Kind.BV_MUL, [x, t])]),
                    mk_term(Kind.BV_MUL, [mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # not solved by bit-blasting, should be terminated in the SAT solver when
    # configured
    tt = TestTerminator()
    options = Options()
    options.set(Option.TIME_LIMIT_PER, 100)
    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.REWRITE_LEVEL, 0)
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    bitwuzla.check_sat()
    assert tt.terminated

    bitwuzla.configure_terminator(None)
    assert bitwuzla.check_sat() == Result.UNKNOWN

    class TestTerminator2:
        def __call__(self):
            return False
    tt = TestTerminator2()
    options = Options()
    options.set(Option.TIME_LIMIT_PER, 100)
    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.REWRITE_LEVEL, 0)
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN
