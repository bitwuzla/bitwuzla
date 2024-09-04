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

@pytest.fixture
def tm():
    return TermManager()

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

def test_mk_bool_sort(tm):
    sort = tm.mk_bool_sort()
    assert sort.is_bool()


def test_mk_array_sort(tm):
    bsort = tm.mk_bool_sort()
    sort = tm.mk_array_sort(bsort, bsort)
    assert sort.is_array()
    tm.mk_array_sort(bsort, sort)

    with pytest.raises(BitwuzlaException):
        tm.mk_array_sort(Sort(), bsort)
    with pytest.raises(BitwuzlaException):
        tm.mk_array_sort(bsort, Sort())


def test_mk_bv_sort(tm):
    sort = tm.mk_bv_sort(8)
    assert sort.is_bv()
    assert sort.bv_size() == 8
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(0)


def test_mk_fp_sort(tm):
    sort = tm.mk_fp_sort(5, 11)
    assert sort.is_fp()
    assert sort.fp_exp_size() == 5
    assert sort.fp_sig_size() == 11
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_sort(0, 11)
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_sort(5, 0)


def test_mk_fun_sort(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_fun_sort([], tm.mk_bool_sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fun_sort([tm.mk_bool_sort(), tm.mk_bool_sort()], Sort())


def test_mk_uninterpreted_sort(tm):
    s1 = tm.mk_uninterpreted_sort()
    s2 = tm.mk_uninterpreted_sort("foo")
    s3 = tm.mk_uninterpreted_sort("foo")
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

def test_mk_true(tm):
    val = tm.mk_true()
    assert val.is_true()
    assert val.value() == True


def test_mk_false(tm):
    val = tm.mk_false()
    assert val.is_false()
    assert val.value() == False


def test_mk_bv_zero(tm):
    val = tm.mk_bv_zero(tm.mk_bv_sort(8))
    assert val.is_bv_value_zero()
    assert val.value() == "00000000"
    assert val.value(10) == "0"
    assert val.value(16) == "0"
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_zero(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_zero(tm.mk_fp_sort(5, 11))


def test_mk_bv_one(tm):
    val = tm.mk_bv_one(tm.mk_bv_sort(8))
    assert val.is_bv_value_one()
    assert val.value() == "00000001"
    assert val.value(10) == "1"
    assert val.value(16) == "1"
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_one(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_one(tm.mk_fp_sort(5, 11))


def test_mk_bv_ones(tm):
    val = tm.mk_bv_ones(tm.mk_bv_sort(8))
    assert val.is_bv_value_ones()
    assert val.value() == "11111111"
    assert val.value(10) == "255"
    assert val.value(16) == "ff"
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_ones(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_ones(tm.mk_fp_sort(5, 11))


def test_mk_bv_min_signed(tm):
    val = tm.mk_bv_min_signed(tm.mk_bv_sort(8))
    assert val.is_bv_value_min_signed()
    assert val.value() == "10000000"
    assert val.value(10) == "128"
    assert val.value(16) == "80"
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_min_signed(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_min_signed(tm.mk_fp_sort(5, 11))


def test_mk_bv_max_signed(tm):
    val = tm.mk_bv_max_signed(tm.mk_bv_sort(8))
    assert val.is_bv_value_max_signed()
    assert val.value() == "01111111"
    assert val.value(10) == "127"
    assert val.value(16) == "7f"
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_max_signed(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_max_signed(tm.mk_fp_sort(5, 11))

def test_mk_fp_pos_zero(tm):
    val = tm.mk_fp_pos_zero(tm.mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_zero()
    assert val.value(2, False) == "0000000000000000"
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_pos_zero(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_pos_zero(tm.mk_bv_sort(8))

def test_mk_fp_neg_zero(tm):
    val = tm.mk_fp_neg_zero(tm.mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_zero()
    assert val.value(2, False) == "1000000000000000"
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_neg_zero(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_neg_zero(tm.mk_bv_sort(8))

def test_mk_fp_pos_inf(tm):
    val = tm.mk_fp_pos_inf(tm.mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_inf()
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_pos_inf(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_pos_inf(tm.mk_bv_sort(8))

def test_mk_fp_neg_inf(tm):
    val = tm.mk_fp_neg_inf(tm.mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_inf()
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_neg_inf(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_neg_inf(tm.mk_bv_sort(8))

def test_mk_fp_nan(tm):
    val = tm.mk_fp_nan(tm.mk_fp_sort(5, 11))
    assert val.is_fp_value_nan()
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_nan(Sort())
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_nan(tm.mk_bv_sort(8))

def test_mk_bv_value(tm):
    val = tm.mk_bv_value(tm.mk_bv_sort(4), "1101", 2)
    assert val.value() == "1101"
    assert val.value(10) == "13"
    assert val.value(16) == "d"
    tm.mk_bv_value(tm.mk_bv_sort(8), "127", 10)
    tm.mk_bv_value(tm.mk_bv_sort(8), 127)
    tm.mk_bv_value(tm.mk_bv_sort(8), "-128", 10)
    tm.mk_bv_value(tm.mk_bv_sort(8), -128)
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_value(tm.mk_bv_sort(8), "256", 10)
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_value(tm.mk_bv_sort(8), "-129", 10)
        tm.mk_bv_value(Sort(), "010", 2)
    with pytest.raises(BitwuzlaException):
      tm.mk_bv_value(tm.mk_bv_sort(8), "", 2)

def test_mk_fp_value(tm):
    val = tm.mk_fp_value(tm.mk_bv_value(tm.mk_bv_sort(1), 1),
                      tm.mk_bv_value(tm.mk_bv_sort(5), 0),
                      tm.mk_bv_value(tm.mk_bv_sort(10), 0))
    assert val.is_fp_value_neg_zero()

    with pytest.raises(BitwuzlaException):
        tm.mk_fp_value(Term(),
                    tm.mk_bv_value(tm.mk_bv_sort(5), 0),
                    tm.mk_bv_value(tm.mk_bv_sort(10), 0))
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_value(tm.mk_bv_value(tm.mk_bv_sort(1), 1),
                    Term(),
                    tm.mk_bv_value(tm.mk_bv_sort(10), 0))
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_value(tm.mk_bv_value(tm.mk_bv_sort(1), 1),
                    tm.mk_bv_value(tm.mk_bv_sort(5), 0),
                    Term())

    val1 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), "1.2")
    val2 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), 1.2)
    assert val1 == val2

    val2 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), "6", "5")
    assert val1 == val2

    val1 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), "1", "3")
    val2 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), "1", 3)
    assert val1 == val2
    val2 = tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                          tm.mk_rm_value(RoundingMode.RNE), 1, 3)
    assert val1 == val2

    with pytest.raises(ValueError):
        tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                       tm.mk_rm_value(RoundingMode.RNE), 1.2, 3)
    with pytest.raises(ValueError):
        tm.mk_fp_value(tm.mk_fp_sort(5, 11),
                       tm.mk_rm_value(RoundingMode.RNE), 1, 3.3)


def test_mk_rm_value(tm):
    rne = tm.mk_rm_value(RoundingMode.RNE)
    assert rne.value() == RoundingMode.RNE
    rna = tm.mk_rm_value(RoundingMode.RNA)
    assert rna.value() == RoundingMode.RNA
    rtz = tm.mk_rm_value(RoundingMode.RTZ)
    assert rtz.value() == RoundingMode.RTZ
    rtp = tm.mk_rm_value(RoundingMode.RTP)
    assert rtp.value() == RoundingMode.RTP
    rtn = tm.mk_rm_value(RoundingMode.RTN)
    assert rtn.value() == RoundingMode.RTN


def test_mk_const(tm):
    a = tm.mk_const(tm.mk_bv_sort(8), "a")
    assert a.symbol() == "a"
    assert tm.mk_const(tm.mk_bool_sort()).symbol() == None


def test_mk_const_array(tm):
    a = tm.mk_const_array(tm.mk_array_sort(tm.mk_bool_sort(),
                                           tm.mk_bool_sort()), tm.mk_true())
    assert a[0].is_value()
    assert a[0].value() == True


def test_mk_var(tm):
    x = tm.mk_var(tm.mk_bv_sort(8), "x")
    assert x.symbol() == "x"
    assert tm.mk_var(tm.mk_bool_sort()).symbol() == None


# ----------------------------------------------------------------------------
# Bitwuzla
# ----------------------------------------------------------------------------

def test_push(tm):
    bitwuzla = Bitwuzla(tm)
    bitwuzla.push(0)
    bitwuzla.push(2)


def test_pop(tm):
    bitwuzla = Bitwuzla(tm)
    bitwuzla.pop(0)
    with pytest.raises(BitwuzlaException):
        bitwuzla.pop(2)
    bitwuzla.push(2)
    bitwuzla.pop(2)


def test_assert_formula(tm):
  bitwuzla = Bitwuzla(tm)
  with pytest.raises(BitwuzlaException):
      bitwuzla.assert_formula(Term())
  bitwuzla.assert_formula(tm.mk_true())
  bitwuzla.assert_formula(tm.mk_false())


def test_get_assertions(tm):
  bitwuzla = Bitwuzla(tm)
  bitwuzla.assert_formula(tm.mk_true())
  bitwuzla.assert_formula(tm.mk_false())
  assert bitwuzla.get_assertions() == [tm.mk_true(), tm.mk_false()]


def test_is_unsat_assumption(tm):
    options = Options()
    options.set(Option.PRODUCE_UNSAT_ASSUMPTIONS, True)
    bitwuzla = Bitwuzla(tm, options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.is_unsat_assumption(tm.mk_false())

    a = tm.mk_const(tm.mk_bool_sort(), "a")
    not_a = tm.mk_term(Kind.NOT, [a])
    bitwuzla.assert_formula(tm.mk_true())
    bitwuzla.check_sat(a, not_a)
    assert not bitwuzla.is_unsat_assumption(tm.mk_true())
    assert bitwuzla.is_unsat_assumption(a)
    assert bitwuzla.is_unsat_assumption(not_a)


def test_get_unsat_assumption(tm):
    options = Options()
    options.set(Option.PRODUCE_UNSAT_ASSUMPTIONS, True)
    bitwuzla = Bitwuzla(tm, options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_unsat_assumptions()

    a = tm.mk_const(tm.mk_bool_sort(), "a")
    not_a = tm.mk_term(Kind.NOT, [a])
    bitwuzla.assert_formula(tm.mk_true())
    bitwuzla.check_sat(a, not_a)
    assert set(bitwuzla.get_unsat_assumptions()) == set([a, not_a])


def test_get_unsat_core(tm):
    options = Options()
    options.set(Option.PRODUCE_UNSAT_CORES, True)
    bitwuzla = Bitwuzla(tm, options)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_unsat_core()

    a = tm.mk_const(tm.mk_bool_sort(), "a")
    b = tm.mk_const(tm.mk_bool_sort(), "b")
    not_a = tm.mk_term(Kind.NOT, [a])
    not_b = tm.mk_term(Kind.NOT, [b])
    bitwuzla.assert_formula(tm.mk_true())
    bitwuzla.assert_formula(a, not_a)
    bitwuzla.assert_formula(b, not_b)
    bitwuzla.check_sat()
    assert set(bitwuzla.get_unsat_core()) == set([a, not_a])

    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(a)
    bitwuzla.check_sat(not_a)
    assert set(bitwuzla.get_unsat_core()) == set([a, not_a])


def test_simplify(tm):
    bitwuzla = Bitwuzla(tm)
    bitwuzla.assert_formula(tm.mk_const(tm.mk_bool_sort(), 'b'))
    bv_one1 = tm.mk_bv_one(tm.mk_bv_sort(1))
    bitwuzla.assert_formula(tm.mk_term(Kind.EQUAL, [bv_one1,
       tm.mk_term(Kind.BV_AND, [bv_one1, tm.mk_const(tm.mk_bv_sort(1), 'bv')])]))
    bitwuzla.simplify()


def test_check_sat(tm):
    bitwuzla = Bitwuzla(tm)
    bitwuzla.check_sat()
    bitwuzla.check_sat()


def test_get_value(tm):
    bv8 = tm.mk_bv_sort(8)
    bvconst8 = tm.mk_const(bv8)
    bitwuzla = Bitwuzla(tm)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(bvconst8)

    options = Options()
    options.set(Option.PRODUCE_MODELS, True)
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(tm.mk_true())
    assert bitwuzla.check_sat(tm.mk_false()) == Result.UNSAT
    b = tm.mk_const(tm.mk_bool_sort())
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(b)
    bitwuzla.check_sat()
    bitwuzla.get_value(b)
    bitwuzla.get_value(tm.mk_false())

    bitwuzla = Bitwuzla(tm, options)
    var = tm.mk_var(bv8, 'q')
    exists = tm.mk_term(Kind.EXISTS, [
        var,
        tm.mk_term(Kind.EQUAL, [
            tm.mk_bv_zero(bv8),
            tm.mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(exists)
    with pytest.raises(BitwuzlaException):
        bitwuzla.get_value(bvconst8)
    assert bitwuzla.check_sat() == Result.SAT
    bitwuzla.assert_formula(
            tm.mk_term(Kind.EQUAL, [bvconst8, bitwuzla.get_value(bvconst8)]))
    assert bitwuzla.check_sat() == Result.SAT

    bitwuzla = Bitwuzla(tm, options)
    a = tm.mk_const(tm.mk_bool_sort())
    b = tm.mk_const(tm.mk_bool_sort())
    bitwuzla.assert_formula(a)
    bitwuzla.assert_formula(tm.mk_term(Kind.NOT, [b]))
    bitwuzla.check_sat()
    assert bitwuzla.get_value(a).value() == True
    assert bitwuzla.get_value(b).value() == False


def test_get_bool_value(tm):
    assert tm.mk_true().value() == True
    assert tm.mk_false().value() == False
    assert str(tm.mk_true().value()) == 'True'
    assert str(tm.mk_false().value()) == 'False'


def test_get_bv_value(tm):
    fun_sort = tm.mk_fun_sort(
            [tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11), tm.mk_bv_sort(32)], tm.mk_bv_sort(8))
    fun = tm.mk_const(fun_sort)
    with pytest.raises(BitwuzlaException):
        fun.value()

    assert tm.mk_bv_one(tm.mk_bv_sort(1)).value() == '1'

    bv_maxs32 = tm.mk_bv_max_signed(tm.mk_bv_sort(32))
    assert bv_maxs32.value() == '01111111111111111111111111111111'
    assert bv_maxs32.value(10) == '2147483647'
    assert bv_maxs32.value(16) == '7fffffff'

    bv8 = tm.mk_bv_sort(8)
    assert tm.mk_bv_value(bv8, '-1', 10).value() == '11111111'
    assert tm.mk_bv_value(bv8, '-1', 10).value(10) == '255'
    assert tm.mk_bv_value(bv8, '-1', 10).value(16) == 'ff'

    assert tm.mk_bv_value(bv8, '-123', 10).value() == '10000101'
    print(tm.mk_bv_value(bv8, '-123', 10))
    assert tm.mk_bv_value(bv8, '-123', 10).value(10) == '133'
    assert tm.mk_bv_value(bv8, '-123', 10).value(16) == '85'

    assert tm.mk_bv_value(bv8, '-128', 10).value() == '10000000'
    assert tm.mk_bv_value(bv8, '-128', 10).value(10) == '128'
    assert tm.mk_bv_value(bv8, '-128', 10).value(16) == '80'


def test_get_fp_value(tm):
    # single bit-vector string
    fp32 = tm.mk_fp_sort(8, 24)
    fpnan32 = tm.mk_fp_nan(fp32)
    fpnzero32 = tm.mk_fp_neg_zero(fp32)
    assert fpnan32.value(2, False) == '01111111110000000000000000000000'
    assert fpnzero32.value(2, False) == '10000000000000000000000000000000'
    # component bit-vector strings
    assert fpnan32.value() == ['0', '11111111', '10000000000000000000000']
    assert fpnzero32.value() == ['1', '00000000', '00000000000000000000000']


def test_get_rm_value(tm):
    assert tm.mk_rm_value(RoundingMode.RNA).value() == RoundingMode.RNA
    assert tm.mk_rm_value(RoundingMode.RNE).value() == RoundingMode.RNE
    assert tm.mk_rm_value(RoundingMode.RTN).value() == RoundingMode.RTN
    assert tm.mk_rm_value(RoundingMode.RTP).value() == RoundingMode.RTP
    assert tm.mk_rm_value(RoundingMode.RTZ).value() == RoundingMode.RTZ
    assert str(tm.mk_rm_value(RoundingMode.RNA).value()) == 'RNA'
    assert str(tm.mk_rm_value(RoundingMode.RNE).value()) == 'RNE'
    assert str(tm.mk_rm_value(RoundingMode.RTN).value()) == 'RTN'
    assert str(tm.mk_rm_value(RoundingMode.RTP).value()) == 'RTP'
    assert str(tm.mk_rm_value(RoundingMode.RTZ).value()) == 'RTZ'


# ----------------------------------------------------------------------------
# Printing
# ----------------------------------------------------------------------------

def test_print_formula(tm):
    bitwuzla = Bitwuzla(tm)
    with pytest.raises(BitwuzlaException):
        bitwuzla.print_formula('')
    with pytest.raises(BitwuzlaException):
        bitwuzla.print_formula('asdf')

    b = tm.mk_const(tm.mk_bool_sort(), 'b')
    bv8 = tm.mk_bv_sort(8)
    var = tm.mk_var(bv8, 'z')
    bvconst8 = tm.mk_const(bv8, 'bv8')
    lambd = tm.mk_term(Kind.LAMBDA, [
        var, tm.mk_term(Kind.BV_ADD, [var, bvconst8])])
    bitwuzla.assert_formula(b)
    bitwuzla.assert_formula(tm.mk_term(Kind.EQUAL, [
        tm.mk_term(Kind.APPLY, [lambd, bvconst8]), tm.mk_bv_zero(bv8)]))

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

    var = tm.mk_var(bv8, 'q')
    exists = tm.mk_term(Kind.EXISTS, [
        var,
        tm.mk_term(Kind.EQUAL, [
            tm.mk_bv_zero(bv8),
            tm.mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(exists)

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

    fpconst16 = tm.mk_const(tm.mk_fp_sort(5, 11), 'fp16')
    funfp = tm.mk_const(
            tm.mk_fun_sort(
                [tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11), tm.mk_bv_sort(32)],
                tm.mk_fp_sort(5, 11)),
            'fun_fp')
    apply = tm.mk_term(Kind.APPLY, [
            funfp,
            bvconst8,
            fpconst16,
            tm.mk_term(Kind.BV_ZERO_EXTEND,
                       [tm.mk_bv_ones(tm.mk_bv_sort(23))], [9])])
    bitwuzla.assert_formula(tm.mk_term(Kind.FP_LEQ, [apply, fpconst16]))

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


def test_print_formula2(tm):
    bitwuzla = Bitwuzla(tm)
    bv1      = tm.mk_bv_sort(1)
    bv8      = tm.mk_bv_sort(8)
    bvconst8 = tm.mk_const(bv8, 'bv8')
    ar1_1    = tm.mk_array_sort(bv1, bv1)
    a        = tm.mk_const(ar1_1, "a")
    b        = tm.mk_const(ar1_1, "b")
    z        = tm.mk_bv_zero(bv1)
    e        = tm.mk_term(Kind.ARRAY_SELECT, [a, z])
    c        = tm.mk_term(Kind.EQUAL, [a, b])
    var = tm.mk_var(bv8, 'q')
    exists = tm.mk_term(Kind.EXISTS, [
        var,
        tm.mk_term(Kind.EQUAL, [
            tm.mk_bv_zero(bv8),
            tm.mk_term(Kind.BV_MUL, [bvconst8, var])])])
    bitwuzla.assert_formula(tm.mk_term(Kind.EQUAL, [e, z]))
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


def test_print_formula3(tm):
    bitwuzla = Bitwuzla(tm)
    bv32 = tm.mk_bv_sort(32)
    n    = tm.mk_const(bv32, 'n')
    sim  = tm.mk_const(bv32, '~')
    zero = tm.mk_bv_zero(bv32)
    two  = tm.mk_bv_value(bv32, 2)
    bitwuzla.assert_formula(tm.mk_term(Kind.DISTINCT, [
         zero, tm.mk_term(Kind.BV_ADD, [n, sim])]))
    bitwuzla.push(1)
    bitwuzla.assert_formula(tm.mk_term(Kind.EQUAL, [
        tm.mk_term(Kind.BV_ADD, [n, two]),
        tm.mk_term(Kind.BV_NEG, [
            tm.mk_term(Kind.BV_ADD, [sim, tm.mk_term(Kind.BV_MUL, [n, two])])])]))
    bitwuzla.push(1)
    bitwuzla.assert_formula(tm.mk_term(Kind.EQUAL, [
        zero, tm.mk_term(Kind.BV_ADD, [n, tm.mk_bv_one(bv32)])]))

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
# Other Bitwuzla methods
# ----------------------------------------------------------------------------

def test_statistics(tm):
    bitwuzla = Bitwuzla(tm)
    bitwuzla.assert_formula(tm.mk_const(tm.mk_bool_sort()))
    stats = bitwuzla.statistics()
    for name, val in stats.items():
        print(f'{name}: {val}')

def test_term_mgr(tm):
    bitwuzla = Bitwuzla(tm)
    assert tm == bitwuzla.term_mgr()
    tm2 = tm
    assert tm2 == tm

# ----------------------------------------------------------------------------
# Sort
# ----------------------------------------------------------------------------

def test_sort_hash(tm):
    hash(tm.mk_bv_sort(8))


def test_sort_bv_size(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_fp_sort(5, 11).bv_size()
    assert tm.mk_bv_sort(8).bv_size() == 8


def test_sort_fp_exp_size(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).fp_exp_size()
    assert tm.mk_fp_sort(5, 11).fp_exp_size() == 5


def test_sort_fp_sig_size(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).fp_sig_size()
    assert tm.mk_fp_sort(5, 11).fp_sig_size() == 11


def test_sort_array_index(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(23).array_index()
    assert tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11)).\
            array_index().is_bv()


def test_sort_array_element(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(23).array_element()
    assert tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11)).\
            array_element().is_fp()


def test_sort_fun_domain_sorts(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).fun_domain()
    fun_sort = tm.mk_fun_sort(
            [tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11), tm.mk_bv_sort(32)],
            tm.mk_bv_sort(8))
    domain = fun_sort.fun_domain()
    assert len(domain) == 3
    assert domain[0] == tm.mk_bv_sort(8)
    assert domain[1] == tm.mk_fp_sort(5, 11)
    assert domain[2] == tm.mk_bv_sort(32)


def test_sort_fun_codomain(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).fun_codomain()
    fun_sort = tm.mk_fun_sort(
            [tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11), tm.mk_bv_sort(32)],
            tm.mk_bv_sort(8))
    assert fun_sort.fun_codomain() == tm.mk_bv_sort(8)


def test_sort_fun_arity(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).fun_arity()
    fun_sort = tm.mk_fun_sort(
            [tm.mk_bv_sort(8), tm.mk_fp_sort(5, 11), tm.mk_bv_sort(32)],
            tm.mk_bv_sort(8))
    assert fun_sort.fun_arity() == 3


def test_sort_uninterpreted_symbol(tm):
    with pytest.raises(BitwuzlaException):
        tm.mk_bv_sort(8).uninterpreted_symbol()
        s1 = tm.mk_uninterpreted_sort()
        s2 = tm.mk_uninterpreted_sort('foo')
        s3 = tm.mk_uninterpreted_sort('foo')
        s4 = tm.mk_uninterpreted_sort('bar')
        assert not s1.uninterpreted_symbol()
        assert s2.uninterpreted_symbol() == 'foo'
        assert s3.uninterpreted_symbol() == 'foo'
        assert s4.uninterpreted_symbol() == 'bar'


def test_sort_is_equal(tm):
    bv8 = tm.mk_bv_sort(8)
    assert tm.mk_bv_sort(8) == bv8
    assert tm.mk_bv_sort(9) != bv8


def test_sort_is_array(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = tm.mk_uninterpreted_sort()
    assert arr_sort_bv.is_array()
    assert arr_sort_bvfp.is_array()
    assert arr_sort_fpbv.is_array()
    assert not fun_sort.is_array()
    assert not fun_sort_fp.is_array()
    assert not bv_sort8.is_array()
    assert not fp_sort16.is_array()
    assert not un_sort.is_array()


def test_sort_is_bv(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    un_sort = tm.mk_uninterpreted_sort()
    assert tm.mk_bv_sort(1).is_bv()
    assert tm.mk_bv_sort(8).is_bv()
    assert tm.mk_bv_sort(23).is_bv()
    assert tm.mk_bv_sort(32).is_bv()
    assert not tm.mk_fp_sort(5, 11).is_bv()
    assert not arr_sort_bv.is_bv()
    assert not arr_sort_bvfp.is_bv()
    assert not arr_sort_fpbv.is_bv()
    assert not fun_sort.is_bv()
    assert not un_sort.is_bv()


def test_sort_is_fp(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    fp_sort32 = tm.mk_fp_sort(8, 24)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    un_sort = tm.mk_uninterpreted_sort()
    assert fp_sort16.is_fp()
    assert fp_sort32.is_fp()
    assert not bv_sort8.is_fp()
    assert not arr_sort_bv.is_fp()
    assert not arr_sort_bvfp.is_fp()
    assert not arr_sort_fpbv.is_fp()
    assert not fun_sort.is_fp()
    assert not un_sort.is_fp()


def test_sort_is_fun(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = tm.mk_uninterpreted_sort()
    assert fun_sort.is_fun()
    assert fun_sort_fp.is_fun()
    assert not arr_sort_bv.is_fun()
    assert not arr_sort_bvfp.is_fun()
    assert not arr_sort_fpbv.is_fun()
    assert not bv_sort8.is_fun()
    assert not fp_sort16.is_fun()
    assert not un_sort.is_fun()


def test_sort_is_rm(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = tm.mk_uninterpreted_sort()
    assert tm.mk_rm_sort().is_rm()
    assert not fun_sort.is_rm()
    assert not fun_sort_fp.is_rm()
    assert not arr_sort_bv.is_rm()
    assert not arr_sort_bvfp.is_rm()
    assert not arr_sort_fpbv.is_rm()
    assert not bv_sort8.is_rm()
    assert not fp_sort16.is_rm()
    assert not un_sort.is_rm()


def test_sort_is_uninterpreted(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    arr_sort_bvfp = tm.mk_array_sort(bv_sort8, fp_sort16)
    arr_sort_fpbv = tm.mk_array_sort(fp_sort16, bv_sort8)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    fun_sort_fp = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], fp_sort16)
    un_sort = tm.mk_uninterpreted_sort()
    assert un_sort.is_uninterpreted()
    assert not tm.mk_rm_sort().is_uninterpreted()
    assert not fun_sort.is_uninterpreted()
    assert not fun_sort_fp.is_uninterpreted()
    assert not arr_sort_bv.is_uninterpreted()
    assert not arr_sort_bvfp.is_uninterpreted()
    assert not arr_sort_fpbv.is_uninterpreted()
    assert not bv_sort8.is_uninterpreted()
    assert not fp_sort16.is_uninterpreted()


def test_sort_str(tm):
    assert f'{tm.mk_bv_sort(1)}{tm.mk_bv_sort(8)}{tm.mk_rm_sort()}{tm.mk_fp_sort(8, 24)}' \
            == '(_ BitVec 1)(_ BitVec 8)RoundingMode(_ FloatingPoint 8 24)'


def test_regr1(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    fun_sort = tm.mk_fun_sort([bv_sort8], bv_sort8)
    arr_sort = tm.mk_array_sort(bv_sort8, bv_sort8)
    args = [tm.mk_const(bv_sort8, 'x'), tm.mk_const(fun_sort, 'f')]
    with pytest.raises(BitwuzlaException):
        tm.mk_term(Kind.APPLY, args)


def test_regr2(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    fun_sort = tm.mk_fun_sort([bv_sort8], bv_sort8)
    arr_sort = tm.mk_array_sort(bv_sort8, bv_sort8)
    assert fun_sort != arr_sort
    fun = tm.mk_const(fun_sort)
    array = tm.mk_const(arr_sort)
    assert arr_sort == array.sort()
    assert fun_sort == fun.sort()
    assert fun.sort() != array.sort()
    assert fun.sort().is_fun()
    assert array.sort().is_array()


# ----------------------------------------------------------------------------
# Term
# ----------------------------------------------------------------------------

def test_term_hash(tm):
    hash(tm.mk_const(tm.mk_bv_sort(8)))


def test_term_sort(tm):
    assert tm.mk_const(tm.mk_bv_sort(8)).sort() == tm.mk_bv_sort(8)


def test_term_symbol(tm):
    x = tm.mk_const(tm.mk_bv_sort(8), 'x')
    assert x.symbol() and x.symbol() == 'x'
    x = tm.mk_const(tm.mk_bv_sort(8))
    assert not x.symbol()


def test_term_is_const(tm):
    bv_sort8 = tm.mk_bv_sort(8)
    bv_sort32 = tm.mk_bv_sort(32)
    arr_sort_bv = tm.mk_array_sort(bv_sort32, bv_sort8)
    fp_sort16 = tm.mk_fp_sort(5, 11)
    fun_sort = tm.mk_fun_sort([bv_sort8, fp_sort16, bv_sort32], bv_sort8)
    assert tm.mk_const(arr_sort_bv).is_const()
    assert tm.mk_const(fun_sort).is_const()
    assert tm.mk_const(tm.mk_bv_sort(1)).is_const()
    assert tm.mk_const(fp_sort16).is_const()
    assert tm.mk_const(tm.mk_rm_sort()).is_const()
    assert not tm.mk_bv_one(tm.mk_bv_sort(1)).is_const()
    assert not tm.mk_term(
            Kind.ARRAY_STORE,
            [
                tm.mk_const(arr_sort_bv),
                tm.mk_const(bv_sort32), tm.mk_bv_zero(bv_sort8)
            ]).is_const()


def test_term_is_var(tm):
    assert tm.mk_var(tm.mk_bv_sort(1)).is_variable()
    assert tm.mk_var(tm.mk_bv_sort(8)).is_variable()
    assert not tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_variable()


def test_term_is_value(tm):
    assert tm.mk_bv_one(tm.mk_bv_sort(1)).is_value()
    assert tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_value()
    assert not tm.mk_const(tm.mk_fp_sort(5, 11)).is_value()
    var = tm.mk_var(tm.mk_bv_sort(8))
    exists = tm.mk_term(Kind.EXISTS, [
        var,
        tm.mk_term(Kind.EQUAL, [
            tm.mk_bv_zero(tm.mk_bv_sort(8)),
            tm.mk_term(Kind.BV_MUL, [tm.mk_const(tm.mk_bv_sort(8)), var])])])
    assert not exists.is_value()


def test_term_is_true(tm):
    assert tm.mk_true().is_true()
    assert not tm.mk_false().is_true()
    assert not tm.mk_bv_one(tm.mk_bv_sort(1)).is_true()


def test_term_is_false(tm):
    assert tm.mk_false().is_false()
    assert not tm.mk_true().is_false()
    assert not tm.mk_bv_zero(tm.mk_bv_sort(1)).is_false()


def test_term_is_bv_value_zero(tm):
    assert tm.mk_bv_zero(tm.mk_bv_sort(8)).is_bv_value_zero()
    assert not tm.mk_bv_one(tm.mk_bv_sort(1)).is_bv_value_zero()
    assert not tm.mk_bv_ones(tm.mk_bv_sort(23)).is_bv_value_zero()
    assert not tm.mk_bv_min_signed(tm.mk_bv_sort(8)).is_bv_value_zero()
    assert not tm.mk_bv_max_signed(tm.mk_bv_sort(8)).is_bv_value_zero()


def test_term_is_bv_value_one(tm):
    assert tm.mk_bv_one(tm.mk_bv_sort(1)).is_bv_value_one()
    assert not tm.mk_bv_zero(tm.mk_bv_sort(8)).is_bv_value_one()
    assert not tm.mk_bv_ones(tm.mk_bv_sort(23)).is_bv_value_one()
    assert not tm.mk_bv_min_signed(tm.mk_bv_sort(8)).is_bv_value_one()
    assert not tm.mk_bv_max_signed(tm.mk_bv_sort(8)).is_bv_value_one()


def test_term_is_bv_value_ones(tm):
    assert tm.mk_bv_ones(tm.mk_bv_sort(23)).is_bv_value_ones()
    assert not tm.mk_bv_zero(tm.mk_bv_sort(8)).is_bv_value_ones()
    assert tm.mk_bv_one(tm.mk_bv_sort(1)).is_bv_value_ones()
    assert not tm.mk_bv_min_signed(tm.mk_bv_sort(8)).is_bv_value_ones()
    assert not tm.mk_bv_max_signed(tm.mk_bv_sort(8)).is_bv_value_ones()


def test_term_is_bv_value_min_signed(tm):
    assert tm.mk_bv_min_signed(tm.mk_bv_sort(8)).is_bv_value_min_signed()
    assert not tm.mk_bv_zero(tm.mk_bv_sort(8)).is_bv_value_min_signed()
    assert tm.mk_bv_one(tm.mk_bv_sort(1)).is_bv_value_min_signed()
    assert not tm.mk_bv_ones(tm.mk_bv_sort(23)).is_bv_value_min_signed()
    assert not tm.mk_bv_max_signed(tm.mk_bv_sort(8)).is_bv_value_min_signed()


def test_term_is_bv_value_max_signed(tm):
    assert tm.mk_bv_max_signed(tm.mk_bv_sort(8)).is_bv_value_max_signed()
    assert not tm.mk_bv_zero(tm.mk_bv_sort(8)).is_bv_value_max_signed()
    assert not tm.mk_bv_one(tm.mk_bv_sort(1)).is_bv_value_max_signed()
    assert not tm.mk_bv_ones(tm.mk_bv_sort(23)).is_bv_value_max_signed()
    assert not tm.mk_bv_min_signed(tm.mk_bv_sort(8)).is_bv_value_max_signed()


def test_term_is_fp_value_pos_zero(tm):
    assert tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not tm.mk_fp_neg_zero(tm.mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not tm.mk_fp_pos_inf(tm.mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not tm.mk_fp_neg_inf(tm.mk_fp_sort(8, 24)).is_fp_value_pos_zero()
    assert not tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_fp_value_pos_zero()


def test_term_is_fp_value_neg_zero(tm):
    assert tm.mk_fp_neg_zero(tm.mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not tm.mk_fp_pos_inf(tm.mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not tm.mk_fp_neg_inf(tm.mk_fp_sort(8, 24)).is_fp_value_neg_zero()
    assert not tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_fp_value_neg_zero()


def test_term_is_fp_value_pos_inf(tm):
    assert tm.mk_fp_pos_inf(tm.mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not tm.mk_fp_neg_zero(tm.mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not tm.mk_fp_neg_inf(tm.mk_fp_sort(8, 24)).is_fp_value_pos_inf()
    assert not tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_fp_value_pos_inf()


def test_term_is_fp_value_neg_inf(tm):
    assert tm.mk_fp_neg_inf(tm.mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not tm.mk_fp_neg_zero(tm.mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not tm.mk_fp_pos_inf(tm.mk_fp_sort(8, 24)).is_fp_value_neg_inf()
    assert not tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_fp_value_neg_inf()


def test_term_is_fp_value_nan(tm):
    assert tm.mk_fp_nan(tm.mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not tm.mk_fp_pos_zero(tm.mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not tm.mk_fp_neg_zero(tm.mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not tm.mk_fp_pos_inf(tm.mk_fp_sort(8, 24)).is_fp_value_nan()
    assert not tm.mk_fp_neg_inf(tm.mk_fp_sort(8, 24)).is_fp_value_nan()


def test_term_is_rm_value_rna(tm):
    assert tm.mk_rm_value(RoundingMode.RNA).is_rm_value_rna()
    assert not tm.mk_rm_value(RoundingMode.RNE).is_rm_value_rna()
    assert not tm.mk_rm_value(RoundingMode.RTN).is_rm_value_rna()
    assert not tm.mk_rm_value(RoundingMode.RTP).is_rm_value_rna()
    assert not tm.mk_rm_value(RoundingMode.RTZ).is_rm_value_rna()


def test_term_is_rm_value_rne(tm):
    assert not tm.mk_rm_value(RoundingMode.RNA).is_rm_value_rne()
    assert tm.mk_rm_value(RoundingMode.RNE).is_rm_value_rne()
    assert not tm.mk_rm_value(RoundingMode.RTN).is_rm_value_rne()
    assert not tm.mk_rm_value(RoundingMode.RTP).is_rm_value_rne()
    assert not tm.mk_rm_value(RoundingMode.RTZ).is_rm_value_rne()


def test_term_is_rm_value_rtn(tm):
    assert not tm.mk_rm_value(RoundingMode.RNA).is_rm_value_rtn()
    assert not tm.mk_rm_value(RoundingMode.RNE).is_rm_value_rtn()
    assert tm.mk_rm_value(RoundingMode.RTN).is_rm_value_rtn()
    assert not tm.mk_rm_value(RoundingMode.RTP).is_rm_value_rtn()
    assert not tm.mk_rm_value(RoundingMode.RTZ).is_rm_value_rtn()


def test_term_is_rm_value_rtp(tm):
    assert not tm.mk_rm_value(RoundingMode.RNA).is_rm_value_rtp()
    assert not tm.mk_rm_value(RoundingMode.RNE).is_rm_value_rtp()
    assert not tm.mk_rm_value(RoundingMode.RTN).is_rm_value_rtp()
    assert tm.mk_rm_value(RoundingMode.RTP).is_rm_value_rtp()
    assert not tm.mk_rm_value(RoundingMode.RTZ).is_rm_value_rtp()


def test_term_is_rm_value_rtz(tm):
    assert not tm.mk_rm_value(RoundingMode.RNA).is_rm_value_rtz()
    assert not tm.mk_rm_value(RoundingMode.RNE).is_rm_value_rtz()
    assert not tm.mk_rm_value(RoundingMode.RTN).is_rm_value_rtz()
    assert not tm.mk_rm_value(RoundingMode.RTP).is_rm_value_rtz()
    assert tm.mk_rm_value(RoundingMode.RTZ).is_rm_value_rtz()


def test_term_print(tm):
    bv1  = tm.mk_bv_sort(1)
    and_bv_const1 = tm.mk_term(
            Kind.EQUAL,
            [
                tm.mk_bv_one(bv1),
                tm.mk_term(
                    Kind.BV_AND,
                    [tm.mk_bv_one(bv1), tm.mk_const(bv1, 'bv1')])
            ])
    var = tm.mk_var(tm.mk_bv_sort(8), 'q')
    exists = tm.mk_term(Kind.EXISTS, [
        var,
        tm.mk_term(Kind.EQUAL, [
            tm.mk_bv_zero(tm.mk_bv_sort(8)),
            tm.mk_term(Kind.BV_MUL, [tm.mk_const(tm.mk_bv_sort(8), 'bv8'),
                                     var])])])
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

    bv5  = tm.mk_bv_sort(5)
    bv10 = tm.mk_bv_sort(10)
    bv4  = tm.mk_bv_sort(4)
    bv8  = tm.mk_bv_sort(8)

    t = tm.mk_fp_value(tm.mk_bv_one(bv1),
                    tm.mk_bv_value(bv5, 3),
                    tm.mk_bv_value(bv10, 23))

    expected = '(fp #b1 #b00011 #b0000010111)' \
               + '(fp (_ bv1 1) (_ bv3 5) (_ bv23 10))' \
               + '(fp #b1 #b00011 #b0000010111)'
    res = t.str() + t.str(10) + t.str(16)
    assert res == expected

    t = tm.mk_fp_value(tm.mk_bv_one(bv1),
                    tm.mk_bv_value(bv4, 3),
                    tm.mk_bv_value(bv8, 23))

    expected = '(fp #b1 #b0011 #b00010111)' \
               + '(fp (_ bv1 1) (_ bv3 4) (_ bv23 8))' \
               + '(fp #b1 #b0011 #b00010111)'
    res = t.str() + t.str(10) + t.str(16)
    assert res == expected


def test_term_print_regr0(tm):
    res = tm.mk_rm_value(RoundingMode.RNA).str() + '\n' \
          + tm.mk_rm_value(RoundingMode.RNE).str() + '\n' \
          + tm.mk_rm_value(RoundingMode.RTN).str() + '\n' \
          + tm.mk_rm_value(RoundingMode.RTP).str() + '\n' \
          + tm.mk_rm_value(RoundingMode.RTZ).str()
    assert res == "RNA\nRNE\nRTN\nRTP\nRTZ"


def test_term_print_regr1(tm):
    bv_sort1  = tm.mk_bv_sort(1)
    bv_sort5  = tm.mk_bv_sort(5)
    bv_sort10 = tm.mk_bv_sort(10)

    fp_val = tm.mk_fp_value(tm.mk_bv_zero(bv_sort1),
                         tm.mk_bv_zero(bv_sort5),
                         tm.mk_bv_zero(bv_sort10))
    assert fp_val.str() == '(fp #b0 #b00000 #b0000000000)'

    fp_val = tm.mk_fp_value(tm.mk_bv_one(bv_sort1),
                         tm.mk_bv_zero(bv_sort5),
                         tm.mk_bv_zero(bv_sort10))
    assert fp_val.str() == '(fp #b1 #b00000 #b0000000000)'

    fp_val = tm.mk_fp_value(tm.mk_bv_zero(bv_sort1),
                         tm.mk_bv_zero(bv_sort5),
                         tm.mk_bv_one(bv_sort10))
    assert fp_val.str() == '(fp #b0 #b00000 #b0000000001)'

    fp_val = tm.mk_fp_value(tm.mk_bv_one(bv_sort1),
                         tm.mk_bv_zero(bv_sort5),
                         tm.mk_bv_one(bv_sort10))
    assert fp_val.str() == '(fp #b1 #b00000 #b0000000001)'


def test_terms_indexed(tm):
    fp_term = tm.mk_const(tm.mk_fp_sort(5, 11))
    bv_term = tm.mk_const(tm.mk_bv_sort(8))
    rm      = tm.mk_rm_value(RoundingMode.RNE)

    idx = tm.mk_term(Kind.FP_TO_SBV, [rm, fp_term], [8])
    assert idx.num_indices() == 1
    indices = idx.indices()
    assert len(indices) == 1
    assert indices[0] == 8

    idx = tm.mk_term(Kind.FP_TO_UBV, [rm, fp_term], [9])
    assert idx.num_indices() == 1
    indices = idx.indices()
    assert len(indices) == 1
    assert indices[0] == 9

    idx = tm.mk_term(Kind.FP_TO_FP_FROM_BV, [bv_term], [3, 5])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 3
    assert indices[1] == 5

    idx = tm.mk_term(Kind.FP_TO_FP_FROM_FP, [rm, fp_term], [7, 18])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 7
    assert indices[1] == 18

    idx = tm.mk_term(Kind.FP_TO_FP_FROM_SBV, [rm, bv_term], [8, 24])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 8
    assert indices[1] == 24

    idx = tm.mk_term(Kind.FP_TO_FP_FROM_UBV, [rm, bv_term], [5, 11])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 5
    assert indices[1] == 11

    idx = tm.mk_term(Kind.BV_EXTRACT, [bv_term], [6, 0])
    assert idx.num_indices() == 2
    indices = idx.indices()
    assert len(indices) == 2
    assert indices[0] == 6
    assert indices[1] == 0


def test_terms(tm):
    bv16 = tm.mk_bv_sort(16)
    fp16 = tm.mk_fp_sort(5, 11)
    array_sort = tm.mk_array_sort(bv16, bv16)
    domain = [bv16, bv16, bv16]
    fun_sort = tm.mk_fun_sort(domain, bv16)

    fp_args = [
            tm.mk_rm_value(RoundingMode.RNA),
            tm.mk_const(fp16),
            tm.mk_const(fp16),
            tm.mk_const(fp16)
        ]

    bv_args = [
            tm.mk_const(bv16),
            tm.mk_const(bv16),
            tm.mk_const(bv16),
            tm.mk_const(bv16)
        ]

    bool_args = [tm.mk_const(tm.mk_bool_sort()), tm.mk_const(tm.mk_bool_sort())]

    for kind in Kind:
        if kind == Kind.CONSTANT \
           or kind == Kind.CONST_ARRAY \
           or kind == Kind.VALUE \
           or kind == Kind.VARIABLE:
               continue

        term = None

        # Boolean
        if kind == Kind.NOT:
               term = tm.mk_term(kind, [bool_args[0]])
               break

        if kind == Kind.AND \
           or kind == Kind.IFF \
           or kind == Kind.IMPLIES \
           or kind == Kind.OR \
           or kind == Kind.XOR:
               term = tm.mk_term(kind, bool_args)
               break

        # BV Unary
        if kind == Kind.BV_DEC \
           or kind == Kind.BV_INC \
           or kind == Kind.BV_NEG \
           or kind == Kind.BV_NOT \
           or kind == Kind.BV_REDAND \
           or kind == Kind.BV_REDOR \
           or kind == Kind.BV_REDXOR:
               term = tm.mk_term(kind, [bv_args[0]])
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
                term = tm.mk_term(kind, [bv_args[0], bv_args[1]])
                break

        # BV Binary+
        if kind == Kind.BV_ADD \
           or kind == Kind.BV_AND \
           or kind == Kind.BV_CONCAT \
           or kind == Kind.BV_MUL \
           or kind == Kind.BV_OR \
           or kind == Kind.BV_XOR:
               term = tm.mk_term(kind, bv_args)
               break

        if kind == Kind.DISTINCT or kind == Kind.EQUAL:
            term = tm.mk_term(kind, bv_args)
            break

        # BV indexed
        if kind == Kind.BV_EXTRACT:
            term = tm.mk_term(kind, [bv_args[0]], [3, 2])
            break

        if kind == Kind.BV_REPEAT \
           or kind == Kind.BV_ROLI \
           or kind == Kind.BV_RORI \
           or kind == Kind.BV_SIGN_EXTEND \
           or kind == Kind.BV_ZERO_EXTEND:
               term = tm.mk_term(kind, [bv_args[0]], [5])
               break

        # Arrays
        if kind == Kind.ARRAY_SELECT:
            term = tm.mk_term(kind, [tm.mk_const(array_sort), bv_args[0]])
            break

        if kind == Kind.ARRAY_STORE:
            term = tm.mk_term(kind, [tm.mk_const(array_sort), bv_args[0], bv_args[1]])
            break

        if kind == Kind.APPLY:
            term = tm.mk_term(
                    kind, [tm.mk_const(fun_sort), bv_args[0], bv_args[1], bv_args[2]])
            break

        # Binder
        if kind == Kind.EXISTS \
           or kind == Kind.FORALL \
           or kind == Kind.LAMBDA:
               bvars = [tm.mk_var(d_bv_sort16), tm.mk_var(d_bv_sort16)]
               # body
               term = tm.mk_term(
                       kind, [bvars[0], bvars[1], tm.mk_term(Kind.BV_SLT, bvars)])
               break

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
               term = tm.mk_term(kind, [fp_args[1]])
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
               term = tm.mk_term(kind, [fp_args[1], fp_args[2]])
               break

        if kind == Kind.FP_SQRT or kind == Kind.FP_RTI:
            term = tm.mk_term(kind, [fp_args[0], fp_args[1]])
            break

        # FP Ternary
        if  kind == Kind.FP_ADD \
            or kind == Kind.FP_DIV \
            or kind == Kind.FP_MUL \
            or kind == Kind.FP_SUB:
                term = tm.mk_term(kind, [fp_args.begin(), fp_args.end() - 1])
                break

        if kind == Kind.FP_FP:
            term = tm.mk_term(
                    kind, [tm.mk_const(tm.mk_bv_sort(1)), bv_args[0], bv_args[1]])
            break

        # FP Quaternery
        if kind == Kind.FP_FMA:
            term = tm.mk_term(kind, fp_args)
            break

        # FP indexed
        if kind == Kind.FP_TO_FP_FROM_BV:
            term = tm.mk_term(kind, [bv_args[0]], [5, 11])
            break

        if kind == Kind.FP_TO_FP_FROM_SBV or kind == Kind.FP_TO_FP_FROM_UBV:
            term = tm.mk_term(kind, [fp_args[0], bv_args[0]], [5, 11])
            break

        if kind == Kind.FP_TO_FP_FROM_FP:
            term = tm.mk_term(kind, [fp_args[0], fp_args[1]], [5, 11])
            break

        if kind == Kind.FP_TO_SBV or kind == Kind.FP_TO_UBV:
            term = tm.mk_term(kind, [fp_args[0], fp_args[1]], [16])
            break

        # Others
        if kind == Kind.ITE:
            term = tm.mk_term(kind, [bool_args[0], bv_args[0], bv_args[1]])
            break

        # no unhandled kind
        assert term

        children = term.children()
        size     = len(children)

        if term.is_const() or term.is_variable() or term.is_value(tm):
            assert size == 0
            continue

        assert size > 0
        for i in range(0, size):
            assert term[i] == children[i]
            assert children[i]

        tterm = None
        if term.kind() == Kind.CONST_ARRAY:
            assert size == 1
            term = tm.mk_const_array(term.sort(), children[0])
        else:
          kind = term.kind()
          if term.num_indices() > 0:
            tterm = tm.mk_term(kind, children, term.indices())
          elif kind == Kind.LAMBDA \
               or kind == Kind.FORALL \
               or kind == Kind.EXISTS:
               tterm = term
          else:
              assert kind != Kind.BV_NOT or size == 1
              tterm = tm.mk_term(kind, children)
        assert tterm == term

    assert tm.mk_const(tm.mk_bv_sort(8)).kind() == Kind.CONSTANT
    assert len(tm.mk_const(tm.mk_bv_sort(8)).children()) == 0

    assert tm.mk_const(tm.mk_rm_sort()).kind() == Kind.CONSTANT
    assert len(tm.mk_const(tm.mk_rm_sort()).children()) == 0

    assert tm.mk_const(tm.mk_uninterpreted_sort()).kind() == Kind.CONSTANT
    assert len(tm.mk_const(tm.mk_uninterpreted_sort()).children()) == 0

    bv_var = tm.mk_var(bv16)
    assert bv_var.kind() == Kind.VARIABLE
    assert len(bv_var.children()) == 0

    rm_val = tm.mk_rm_value(RoundingMode.RNA)
    assert rm_val.kind() == Kind.VALUE
    assert len(rm_val.children()) == 0

    fp_from_real_val = tm.mk_fp_value(fp16, rm_val, '1.1')
    assert fp_from_real_val.kind() == Kind.VALUE
    assert len(fp_from_real_val.children()) == 0

    fp_from_real = tm.mk_fp_value(fp16, tm.mk_const(tm.mk_rm_sort()), '1.1')
    assert fp_from_real.kind() == Kind.ITE
    assert len(fp_from_real.children()) > 0

    fp_from_rat_val = tm.mk_fp_value(fp16, rm_val, '1', '2')
    assert fp_from_rat_val.kind() == Kind.VALUE
    assert len(fp_from_rat_val.children()) == 0

    fp_from_rat = tm.mk_fp_value(fp16, tm.mk_const(tm.mk_rm_sort()), '1', '2')
    assert fp_from_rat.kind() == Kind.ITE
    assert len(fp_from_rat.children()) > 0

    fp_nan = tm.mk_fp_nan(fp16)
    assert fp_nan.kind() == Kind.VALUE
    assert len(fp_nan.children()) == 0

    bv_one = tm.mk_bv_one(bv16)
    assert bv_one.kind() == Kind.VALUE
    assert len(bv_one.children()) == 0

    bv_val = tm.mk_bv_value(bv16, '43', 10)
    assert bv_val.kind() == Kind.VALUE
    assert len(bv_val.children()) == 0

    # TODO enable when implemented
    # const_array = tm.mk_const_array(array_sort, bv_val)
    # assert const_array.kind() == Kind.VALUE
    # assert len(const_array.children()) == 0


def test_substitute1(tm):
    bv16 = tm.mk_bv_sort(16)
    bv_const = tm.mk_const(bv16)
    bv_value = tm.mk_bv_value(bv16, '143', 10)

    # simple substitution const -> value
    substs = {bv_const: bv_value}
    result = tm.substitute_term(bv_const, substs)
    assert result == bv_value


def test_substitute2(tm):
    bv16 = tm.mk_bv_sort(16)
    bv_const = tm.mk_const(bv16)
    bv_value = tm.mk_bv_value(bv16, '143', 10)
    # (sdiv x y) -> (sdiv value y)
    x = tm.mk_const(bv16)
    y = tm.mk_const(bv16)

    substs = {x: bv_value}

    result = tm.substitute_term(tm.mk_term(Kind.BV_SDIV, [x, y]), substs)
    assert result == tm.mk_term(Kind.BV_SDIV, [bv_value, y])


def test_substitute3(tm):
    bv16 = tm.mk_bv_sort(16)
    domain = [bv16, bv16, bv16]
    fun_sort   = tm.mk_fun_sort(domain, tm.mk_bool_sort())
    bv_const = tm.mk_const(bv16)
    bv_value = tm.mk_bv_value(bv16, '143', 10)
    # partial substitution of variables in quantified formula
    args = [tm.mk_const(fun_sort),
            tm.mk_var(bv16, 'x'),
            tm.mk_var(bv16, 'y'),
            tm.mk_var(bv16, 'z')]
    args.append(tm.mk_term(Kind.APPLY, args))
    q = tm.mk_term(Kind.FORALL, args[1:])

    substs = {args[1]: tm.mk_const(bv16, 'cx'), args[2]: tm.mk_const(bv16, 'cy')}

    apply = tm.mk_term(
            Kind.APPLY, [args[0], substs[args[1]], substs[args[2]], args[3]])
    expected = tm.mk_term(Kind.FORALL, [args[3], apply])

    result = tm.substitute_term(q, substs)
    assert result == expected

def test_substitute4(tm):
    bv16 = tm.mk_bv_sort(16)
    domain = [bv16, bv16, bv16]
    fun_sort   = tm.mk_fun_sort(domain, tm.mk_bool_sort())
    array_sort = tm.mk_array_sort(bv16, bv16)
    bv_const = tm.mk_const(bv16)
    bv_value = tm.mk_bv_value(bv16, '143', 10)
    # substitute term in constant array
    term = tm.mk_const(bv16)
    const_array = tm.mk_const_array(array_sort, term)

    substs = {term: bv_value}

    result = tm.substitute_term(const_array, substs)
    expected = tm.mk_const_array(array_sort, bv_value)
    assert result == expected
    assert result.kind() == Kind.CONST_ARRAY


def test_substitute4(tm):
    bv8   = tm.mk_bv_sort(8)
    x     = tm.mk_const(bv8, 'x')
    one   = tm.mk_bv_one(bv8)
    btrue = tm.mk_true()
    addxx = tm.mk_term(Kind.BV_ADD, [x, x])
    addoo = tm.mk_term(Kind.BV_ADD, [one, one])

    with pytest.raises(BitwuzlaException):
        tm.substitute_term(addxx, {one: btrue})

    assert tm.substitute_term(addxx, {x: one}) == addoo
    assert tm.substitute_term(addxx, {one: x}) == addxx

    # simultaneous substitution
    y     = tm.mk_const(bv8, 'y')
    addxy = tm.mk_term(Kind.BV_ADD, [x, y])
    addyo = tm.mk_term(Kind.BV_ADD, [y, one])

    with pytest.raises(BitwuzlaException):
        tm.substitute_term(addxy, {x: y, y: btrue})

    assert tm.substitute_term(addxy, {x: y, y: one}) == addyo

    terms = [addxx, addxy]
    expected = [tm.mk_term(Kind.BV_ADD, [y, y]), tm.mk_term(Kind.BV_ADD, [y, x])]
    assert tm.substitute_terms(terms, {x: y, y: x}) == expected


def test_term_print1(tm):
    a = tm.mk_const(tm.mk_bv_sort(1), 'a')
    t = tm.mk_term(Kind.BV_NOT, [a])
    assert t.str() == '(bvnot a)'


def test_term_print2(tm):
    fn1_1 = tm.mk_fun_sort([tm.mk_bv_sort(1)], tm.mk_bv_sort(1))
    t     = tm.mk_const(fn1_1, 'f')
    assert t.str() == 'f'


def test_term_print3(tm):
    ar1_1 = tm.mk_array_sort(tm.mk_bv_sort(1), tm.mk_bv_sort(1))
    t     = tm.mk_const(ar1_1, 'a')
    assert t.str() == 'a'


def test_arrayfun(tm):
    bvsort = tm.mk_bv_sort(4)
    domain = [bvsort]
    funsort = tm.mk_fun_sort(domain, bvsort)
    arrsort = tm.mk_array_sort(bvsort, bvsort)
    f       = tm.mk_const(funsort, 'f')
    a       = tm.mk_const(arrsort, 'a')
    assert f.sort() != a.sort()
    assert f.sort().is_fun()
    assert not a.sort().is_fun()
    assert not f.sort().is_array()
    assert a.sort().is_array()

# ----------------------------------------------------------------------------
# Parsing
# ----------------------------------------------------------------------------

def test_parser_smt2(tm):
    filename = "parse.smt2"
    with open(filename, 'w') as smt2:
        smt2.write('(set-logic QF_BV)\n(check-sat)\n(exit)\n')
        smt2.close()

    options = Options()
    with pytest.raises(BitwuzlaException):
        Parser(tm, options, '')
    with pytest.raises(BitwuzlaException):
        Parser(tm, options, 'foo')

    parser = Parser(tm, options)

    with pytest.raises(BitwuzlaException):
        parser.bitwuzla()
    with pytest.raises(BitwuzlaException):
        parser.parse('parsex.smt2')
    with pytest.raises(BitwuzlaException):
        parser.parse(filename, True)

    parser = Parser(tm, options)
    parser.parse(filename, True)
    assert parser.get_declared_sorts() == []
    assert parser.get_declared_funs() == []
    os.remove(filename)

def test_parser_smt2_string1(tm):
    smt2 = "(set-logic QF_BV)\n(check-sat)\n(exit)\n"
    options = Options()
    parser = Parser(tm, options)
    with pytest.raises(BitwuzlaException):
        parser.parse(smt2, True, True)
    parser = Parser(tm, options)
    parser.parse(smt2, True, False)
    assert parser.get_declared_sorts() == []
    assert parser.get_declared_funs() == []

def test_parser_smt2_string2(tm):
    str_decl  = "(declare-const a Bool)"
    str_true  = "(assert (= a true))"
    str_false = "(assert (= a false))"
    options = Options()
    parser = Parser(tm, options)
    parser.parse(str_decl, True, False)
    parser.parse(str_true, True, False)
    parser.parse(str_false, True, False)
    bitwuzla = parser.bitwuzla()
    bitwuzla.check_sat() == Result.UNSAT
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert decl_funs == [parser.parse_term("a")]
    assert decl_funs[0].symbol() == "a"

def test_parser_smt2_string3(tm):
    options = Options()
    parser = Parser(tm, options)
    parser.parse("(set-logic QF_ABV)", True, False)
    parser.parse("(set-info :status unsat)", True, False)
    parser.parse("(declare-const v0 (_ BitVec 8))", True, False)
    parser.parse("(declare-const v1 (_ BitVec 15))", True, False)
    parser.parse(
      "(declare-const a0 (Array (_ BitVec 16) (_ BitVec 1) ))", True, False)
    parser.parse("(assert (= #b1 (bvnot (ite (= (select (store a0 (concat v0 "
                + "(_ bv0 8)) (_ bv1 1)) (concat v1 (_ bv1 1))) (select a0 "
                + "(concat v1 (_ bv1 1)))) #b1 #b0))))",
                True,
                False)
    parser.parse("(check-sat)", True, False)
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert decl_funs == [
            parser.parse_term("v0"),
            parser.parse_term("v1"),
            parser.parse_term("a0")]
    decl_funs_strs = [t.symbol() for t in decl_funs]
    assert "v0" in decl_funs_strs
    assert "v1" in decl_funs_strs
    assert "a0" in decl_funs_strs

def test_parser_smt2_string_term(tm):
    options = Options()
    parser = Parser(tm, options)
    assert parser.parse_term("true") == tm.mk_true()
    assert parser.parse_term("false") == tm.mk_false()
    parser.parse("(declare-const a Bool)", True, False)
    t_a = parser.parse_term("a")
    parser.parse("(declare-const b (_ BitVec 16))", True, False)
    t_b = parser.parse_term("b")
    parser.parse("(declare-const c Bool)", True, False)
    t_c = parser.parse_term("c")
    assert parser.parse_term("(xor a c)")  == tm.mk_term(Kind.XOR, [t_a, t_c])
    assert parser.parse_term("(bvadd b #b1011111010001010)") == \
            tm.mk_term(Kind.BV_ADD,
                [t_b,
                 tm.mk_bv_value(
                     tm.mk_bv_sort(16), "1011111010001010", 2)])
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert decl_funs == [t_a, t_b, t_c]
    decl_funs_strs = [t.symbol() for t in decl_funs]
    assert "a" in decl_funs_strs
    assert "b" in decl_funs_strs
    assert "c" in decl_funs_strs

def test_parser_smt2_string_sort(tm):
    options = Options()
    parser = Parser(tm, options)
    assert parser.parse_sort("Bool") == tm.mk_bool_sort()
    assert parser.parse_sort("(_ BitVec 32)") == tm.mk_bv_sort(32)
    assert parser.parse_sort("RoundingMode") == tm.mk_rm_sort()
    parser.parse("(declare-sort m 0)", True, False)
    assert parser.parse_sort("m")
    parser.parse("(define-sort FPN () (_ FloatingPoint 11 53))", True, False)
    assert parser.parse_sort("(_ FloatingPoint 11 53)") == \
            parser.parse_sort("FPN")
    decl_sorts = parser.get_declared_sorts()
    assert decl_sorts == [parser.parse_sort("m")]
    assert decl_sorts[0].uninterpreted_symbol() == "m"
    assert parser.get_declared_funs() == []

def test_parser_smt2_print_model_sat(tm):
    filename = "parse.smt2"
    with open(filename, 'w') as smt2:
        smt2.write('(declare-fun a () (_ BitVec 1))\n')
        smt2.write('(declare-fun b () (_ BitVec 1))\n')
        smt2.write('(declare-fun c () (_ BitVec 1))\n')
        smt2.write('(declare-fun d () (_ BitVec 1))\n')
        smt2.write('(assert (= b (ite (= (_ bv1 1) (bvand c b d a)) (_ bv0 1)')
        smt2.write('(_ bv1 1))))\n(set-info :status sat)\n(check-sat)\n')
    options = Options()
    # error, produce models not enabled
    with pytest.raises(BitwuzlaException):
        parser = Parser(tm, options, "smt2", 2)
        parser.configure_auto_print_model(True)
        parser.parse(filename, False)
    options.set(Option.PRODUCE_MODELS, True)
    # parse only
    parser = Parser(tm, options, "smt2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename, True)
    # parse and execute
    parser = Parser(tm, options, "smt2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename)
    os.remove(filename)

def test_parser_smt2_print_model_unsat(tm):
    filename = "parse.smt2"
    with open(filename, 'w') as smt2:
        smt2.write('(declare-fun a () (_ BitVec 1))\n')
        smt2.write('(declare-fun b () (_ BitVec 1))\n')
        smt2.write('(declare-fun c () (_ BitVec 1))\n')
        smt2.write('(declare-fun d () (_ BitVec 1))\n')
        smt2.write('(assert (= b (ite (= (_ bv1 1) (bvand c b d a))\n')
        smt2.write('(_ bv0 1) (_ bv1 1))))\n')
        smt2.write('(check-sat)\n')
    options = Options()
    # error, produce models not enabled
    with pytest.raises(BitwuzlaException):
        parser = Parser(tm, options, "smt2", 2)
        parser.configure_auto_print_model(True)
        parser.parse(filename, False)
    options.set(Option.PRODUCE_MODELS, True)
    # parse only
    parser = Parser(tm, options, "smt2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename, True)
    # parse and execute
    parser = Parser(tm, options, "smt2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename)
    os.remove(filename)

def test_parser_btor2(tm):
    iinput = "parse.btor2"
    with open(iinput, 'w') as btor2:
        btor2.write("1 sort bitvec 8\n")
        btor2.write("2 input 1 @inp2\n")
        btor2.write("3 sort bitvec 3\n")
        btor2.write("4 one 3\n")
        btor2.write("5 uext 1 4 5\n")
        btor2.write("6 srl 1 2 5\n")
        btor2.write("7 sort bitvec 1\n")
        btor2.write("8 slice 7 6 7 7\n")
        btor2.write("9 constraint 8\n")

    options = Options()
    parser = Parser(tm, options, 'btor2')
    bitwuzla = parser.bitwuzla()
    with pytest.raises(BitwuzlaException):
        parser.parse('parsex.btor2')

    parser = Parser(tm, options, 'btor2')
    parser.parse(iinput, True, True)
    parser.bitwuzla().check_sat() == Result.UNSAT
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert len(decl_funs) == 1
    assert decl_funs[0].symbol() == "@inp2"
    os.remove(iinput)

def test_parser_btor2_string1(tm):
    btor2 = "1 sort bitvec 8\n2 input 1 @inp2\n3 sort bitvec 3\n"\
            "4 one 3 @one\n5 uext 1 4 5\n6 srl 1 2 5 @srl\n7 sort bitvec 1\n"\
            "8 slice 7 6 7 7\n9 constraint 8\n"
    options = Options()
    parser = Parser(tm, options, 'btor2')
    with pytest.raises(BitwuzlaException):
        parser.parse(btor2, True, True)

    parser = Parser(tm, options, 'btor2')
    parser.parse(btor2, True, False)
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert len(decl_funs) == 1
    assert decl_funs[0].symbol() == "@inp2"

def test_parser_btor2_string2(tm):
    str_decl  = "(declare-const a Bool)"
    str_true  = "(assert (= a True))"
    str_false = "(assert (= a False))"

    decl_sorts = "1 sort bitvec 8\n2 sort array 1 1\n"
    decl_inputs = "3 input 2 @arr3\n4 input 2 @arr4\n5 input 2 @arr5\n"
    decl_more_inputs = "6 sort bitvec 1\n7 input 6 @inp7\n8 input 1 @inp8\n"
    ite9 = "9 ite 2 -7 4 5\n"
    reads = "10 read 1 4 8\n11 read 1 9 8\n12 neq 6 10 11\n"
    and13 = "13 and 6 -7 12\n"
    root = "14 constraint 13\n"

    options = Options()
    parser = Parser(tm, options, 'btor2')
    parser.parse(decl_sorts, True, False)
    parser.parse(decl_inputs, True, False)
    parser.parse(decl_more_inputs, True, False)
    parser.parse(ite9, True, False)
    parser.parse(reads, True, False)
    parser.parse(and13, True, False)
    parser.parse(root, True, False)
    assert parser.bitwuzla().check_sat() == Result.UNSAT
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert len(decl_funs) == 5
    decl_funs_strs = [t.symbol() for t in decl_funs]
    assert "@arr3" in decl_funs_strs
    assert "@arr4" in decl_funs_strs
    assert "@arr5" in decl_funs_strs
    assert "@inp7" in decl_funs_strs
    assert "@inp8" in decl_funs_strs

def test_parser_btor2_string_term(tm):
    options = Options()
    parser = Parser(tm, options, 'btor2')
    assert parser.parse_sort("1 sort bitvec 1") == tm.mk_bv_sort(1)
    parser.parse_term("2 constd 1 1")
    assert parser.parse_term("3 constd 1 0") == tm.mk_bv_value(tm.mk_bv_sort(1), 0)
    t_a = parser.parse_term("4 input 1 a")
    parser.parse("5 sort bitvec 16", True, False)
    with pytest.raises(BitwuzlaException):
        parser.parse("5 sort bitvec 16", True, False)
    t_b = parser.parse_term("6 input 5 b")
    t_c = parser.parse_term("7 input 1 c")
    assert parser.parse_term("8 xor 1 4 7") == tm.mk_term(Kind.BV_XOR, [t_a, t_c])
    parser.parse_term("9 const 5 1011111010001010")
    assert parser.parse_term("10 add 5 6 9") == \
            tm.mk_term(Kind.BV_ADD,
                          [t_b,
                           tm.mk_bv_value(tm.mk_bv_sort(16), "1011111010001010", 2)])
    assert parser.get_declared_sorts() == []
    decl_funs = parser.get_declared_funs()
    assert len(decl_funs) == 3
    decl_funs_strs = [t.symbol() for t in decl_funs]
    assert "a" in decl_funs_strs
    assert "b" in decl_funs_strs
    assert "c" in decl_funs_strs

def test_parser_btor2_string_sort(tm):
    options = Options()
    parser = Parser(tm, options, 'btor2')
    bv1 = parser.parse_sort("1 sort bitvec 1")
    assert bv1 == tm.mk_bv_sort(1)
    assert parser.parse_sort("2 sort bitvec 32") == tm.mk_bv_sort(32)
    assert parser.parse_sort("3 sort array 1 1") == tm.mk_array_sort(bv1, bv1)
    assert parser.get_declared_sorts() == []
    assert parser.get_declared_funs() == []

def test_parser_btor2_print_model_sat(tm):
    filename = "parse.smt2"
    with open(filename, 'w') as btor2:
        btor2.write('1 sort bitvec 32\n')
        btor2.write('2 input 1 x\n')
        btor2.write('3 input 1 y\n')
        btor2.write('4 add 1 -2 -3\n')
        btor2.write('5 add 1 2 4\n')
        btor2.write('6 add 1 3 5\n')
        btor2.write('7 const 1 11111111111111111111111111111110\n')
        btor2.write('8 sort bitvec 1\n')
        btor2.write('9 eq 8 6 7\n')
        btor2.write('10 constraint 9\n')
    options = Options()
    # error, produce models not enabled
    with pytest.raises(BitwuzlaException):
        parser = Parser(tm, options, "btor2", 2)
        parser.configure_auto_print_model(True)
        parser.parse(filename, False)
    options.set(Option.PRODUCE_MODELS, True)
    # parse only
    parser = Parser(tm, options, "btor2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename, True)
    # parse and execute
    parser = Parser(tm, options, "btor2", 2)
    parser.configure_auto_print_model(True)
    parser.parse(filename)
    os.remove(filename)

# ----------------------------------------------------------------------------
# Termination function
# ----------------------------------------------------------------------------

def test_terminate(tm):

    class TestTerminator:
        def __call__(self):
            return True

    bv4 = tm.mk_bv_sort(4)
    x = tm.mk_const(bv4)
    s = tm.mk_const(bv4)
    t = tm.mk_const(bv4)
    a = tm.mk_term(Kind.AND,
                [
                    tm.mk_term(
                        Kind.EQUAL,
                        [tm.mk_term(Kind.BV_ADD, [x, x]), tm.mk_bv_value(bv4, 3)]),
                    tm.mk_term(
                        Kind.NOT,
                        [tm.mk_term(Kind.BV_UADD_OVERFLOW, [x, x])])
                ])
    b = tm.mk_term(Kind.DISTINCT,
                [
                    tm.mk_term(
                        Kind.BV_MUL,
                        [s, tm.mk_term(Kind.BV_MUL, [x, t])]),
                    tm.mk_term(
                        Kind.BV_MUL,
                        [tm.mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # solved by rewriting
    options = Options()
    options.set(Option.BV_SOLVER, 'bitblast')
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(a)
    assert bitwuzla.check_sat() == Result.UNSAT

    options.set(Option.BV_SOLVER, 'prop')
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(a)
    assert bitwuzla.check_sat() == Result.UNSAT

    # not solved by bit-blasting without preprocessing, should be terminated in
    # the SAT solver when configured
    tt = TestTerminator()
    options.set(Option.BV_SOLVER, 'bitblast')
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNSAT
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.assert_formula(b)
    bitwuzla.configure_terminator(tt)
    assert bitwuzla.check_sat() == Result.UNKNOWN

    options.set(Option.BV_SOLVER, 'prop')
    options.set(Option.REWRITE_LEVEL, 0)
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN


def test_terminate_sat(tm):
    class TestTerminator:
        def __init__(self, time_limit):
            self.start_time = time.time()
            self.time_limit = time_limit

        def __call__(self):
            # Terminate after self.time_limit ms passed
            return (time.time() - self.start_time) * 1000 > self.time_limit

    bv32 = tm.mk_bv_sort(32)
    x = tm.mk_const(bv32)
    s = tm.mk_const(bv32)
    t = tm.mk_const(bv32)
    b = tm.mk_term(Kind.DISTINCT,
                [
                    tm.mk_term(Kind.BV_MUL, [s, tm.mk_term(Kind.BV_MUL, [x, t])]),
                    tm.mk_term(Kind.BV_MUL, [tm.mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # not solved by bit-blasting without preprocessing, should be terminated in
    # the SAT solver when configured
    tt = TestTerminator(1)
    options = Options()
    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN

    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.SAT_SOLVER, 'kissat')
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN


def test_terminate_timeout_wrap(tm):
    class TestTerminator:
        def __init__(self):
            self.terminated = False
        def __call__(self):
            self.terminated = True
            return True

    bv32 = tm.mk_bv_sort(32)
    x = tm.mk_const(bv32)
    s = tm.mk_const(bv32)
    t = tm.mk_const(bv32)
    b = tm.mk_term(Kind.DISTINCT,
                [
                    tm.mk_term(Kind.BV_MUL, [s, tm.mk_term(Kind.BV_MUL, [x, t])]),
                    tm.mk_term(Kind.BV_MUL, [tm.mk_term(Kind.BV_MUL, [s, x]), t])
                ])
    # not solved by bit-blasting, should be terminated in the SAT solver when
    # configured
    tt = TestTerminator()
    options = Options()
    options.set(Option.TIME_LIMIT_PER, 100)
    options.set(Option.BV_SOLVER, 'bitblast')
    options.set(Option.REWRITE_LEVEL, 0)
    options.set(Option.PREPROCESS, False)
    bitwuzla = Bitwuzla(tm, options)
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
    bitwuzla = Bitwuzla(tm, options)
    bitwuzla.configure_terminator(tt)
    bitwuzla.assert_formula(b)
    assert bitwuzla.check_sat() == Result.UNKNOWN
