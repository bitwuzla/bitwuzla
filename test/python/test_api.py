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
    assert val.value() == "0000000000000000"
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_zero(Sort())
    with pytest.raises(BitwuzlaException):
        mk_fp_pos_zero(mk_bv_sort(8))

def test_mk_fp_neg_zero():
    val = mk_fp_neg_zero(mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_zero()
    assert val.value() == "1000000000000000"
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
    val = mk_bv_value(mk_bv_sort(4), "1101")
    assert val.value() == "1101"
    assert val.value(10) == "13"
    assert val.value(16) == "d"
    mk_bv_value(mk_bv_sort(8), "127", 10)
    mk_bv_value(mk_bv_sort(8), 127, 10)
    mk_bv_value(mk_bv_sort(8), "-128", 10)
    mk_bv_value(mk_bv_sort(8), -128, 10)
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
    fp32 = mk_fp_sort(8, 24)
    assert mk_fp_nan(fp32).value() == '01111111110000000000000000000000'
    assert mk_fp_neg_zero(fp32).value() == '10000000000000000000000000000000'


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
    two  = mk_bv_value(bv32, 2, 10)
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
