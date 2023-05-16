###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

import pytest

from bitwuzla import *

def test_options_set():
    options = Options()
    with pytest.raises(RuntimeError):
        options.set("incremental", True)
    with pytest.raises(RuntimeError):
        options.set(Option.VERBOSITY, 5)
    with pytest.raises(RuntimeError):
        options.set("VERBOSITY", 5)

    options.set(Option.PRODUCE_MODELS, True)

    assert options.get(Option.PRODUCE_UNSAT_CORES) == 0
    options.set(Option.PRODUCE_UNSAT_CORES, 1)
    assert options.get(Option.PRODUCE_UNSAT_CORES) == 1

    assert options.get(Option.VERBOSITY) == 0
    options.set(Option.VERBOSITY, 2)
    assert options.get(Option.VERBOSITY) == 2
    options.set("verbose", 3)
    assert options.get(Option.VERBOSITY) == 3
    with pytest.raises(RuntimeError):
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

    with pytest.raises(RuntimeError):
        options.set("sat--solver", "kissat")
    with pytest.raises(RuntimeError):
        options.set(Option.BV_SOLVER, "asdf")


def test_options_set_args():
    options = Options()
    options.set_args("-v", "-v")
    assert options.get(Option.VERBOSITY) == 2
    options.set_args("-v", 3)
    assert options.get(Option.VERBOSITY) == 3
    options.set_args("-v=4")
    assert options.get(Option.VERBOSITY) == 4
    with pytest.raises(RuntimeError):
        options.set_args("-v=100")
    options.set_args("-S=cadical")
    assert options.get(Option.SAT_SOLVER), "cadical"
    with pytest.raises(RuntimeError):
        options.set_args("--no-verbose")


def test_mk_bool_sort():
    sort = mk_bool_sort()
    assert sort.is_bool()


def test_mk_array_sort():
    bsort = mk_bool_sort()
    sort = mk_array_sort(bsort, bsort)
    assert sort.is_array()
    mk_array_sort(bsort, sort)

    with pytest.raises(RuntimeError):
        mk_array_sort(Sort(), bsort)
    with pytest.raises(RuntimeError):
        mk_array_sort(bsort, Sort())


def test_mk_bv_sort():
    sort = mk_bv_sort(8)
    assert sort.is_bv()
    assert sort.bv_size() == 8
    with pytest.raises(RuntimeError):
        mk_bv_sort(0)

def test_mk_fp_sort():
    sort = mk_fp_sort(5, 11)
    assert sort.is_fp()
    assert sort.fp_exp_size() == 5
    assert sort.fp_sig_size() == 11
    with pytest.raises(RuntimeError):
        mk_fp_sort(0, 11)
    with pytest.raises(RuntimeError):
        mk_fp_sort(5, 0)


def test_mk_fun_sort():
    with pytest.raises(RuntimeError):
        mk_fun_sort([], mk_bool_sort())
    with pytest.raises(RuntimeError):
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


def test_mk_bv_zero():
    val = mk_bv_zero(mk_bv_sort(8))
    assert val.is_bv_value_zero()
    with pytest.raises(RuntimeError):
        mk_bv_zero(Sort())
    with pytest.raises(RuntimeError):
        mk_bv_zero(mk_fp_sort(5, 11))


def test_mk_bv_one():
    val = mk_bv_one(mk_bv_sort(8))
    assert val.is_bv_value_one()
    with pytest.raises(RuntimeError):
        mk_bv_one(Sort())
    with pytest.raises(RuntimeError):
        mk_bv_one(mk_fp_sort(5, 11))


def test_mk_bv_ones():
    val = mk_bv_ones(mk_bv_sort(8))
    assert val.is_bv_value_ones()
    with pytest.raises(RuntimeError):
        mk_bv_ones(Sort())
    with pytest.raises(RuntimeError):
        mk_bv_ones(mk_fp_sort(5, 11))


def test_mk_bv_min_signed():
    val = mk_bv_min_signed(mk_bv_sort(8))
    assert val.is_bv_value_min_signed()
    with pytest.raises(RuntimeError):
        mk_bv_min_signed(Sort())
    with pytest.raises(RuntimeError):
        mk_bv_min_signed(mk_fp_sort(5, 11))


def test_mk_bv_max_signed():
    val = mk_bv_max_signed(mk_bv_sort(8))
    assert val.is_bv_value_max_signed()
    with pytest.raises(RuntimeError):
        mk_bv_max_signed(Sort())
    with pytest.raises(RuntimeError):
        mk_bv_max_signed(mk_fp_sort(5, 11))

def test_mk_fp_pos_zero():
    val = mk_fp_pos_zero(mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_zero()
    with pytest.raises(RuntimeError):
        mk_fp_pos_zero(Sort())
    with pytest.raises(RuntimeError):
        mk_fp_pos_zero(mk_bv_sort(8))

def test_mk_fp_neg_zero():
    val = mk_fp_neg_zero(mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_zero()
    with pytest.raises(RuntimeError):
        mk_fp_neg_zero(Sort())
    with pytest.raises(RuntimeError):
        mk_fp_neg_zero(mk_bv_sort(8))

def test_mk_fp_pos_inf():
    val = mk_fp_pos_inf(mk_fp_sort(5, 11))
    assert val.is_fp_value_pos_inf()
    with pytest.raises(RuntimeError):
        mk_fp_pos_inf(Sort())
    with pytest.raises(RuntimeError):
        mk_fp_pos_inf(mk_bv_sort(8))

def test_mk_fp_neg_inf():
    val = mk_fp_neg_inf(mk_fp_sort(5, 11))
    assert val.is_fp_value_neg_inf()
    with pytest.raises(RuntimeError):
        mk_fp_neg_inf(Sort())
    with pytest.raises(RuntimeError):
        mk_fp_neg_inf(mk_bv_sort(8))

def test_mk_fp_nan():
    val = mk_fp_nan(mk_fp_sort(5, 11))
    assert val.is_fp_value_nan()
    with pytest.raises(RuntimeError):
        mk_fp_nan(Sort())
    with pytest.raises(RuntimeError):
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
    with pytest.raises(RuntimeError):
        mk_bv_value(mk_bv_sort(8), "256", 10)
    with pytest.raises(RuntimeError):
        mk_bv_value(mk_bv_sort(8), "-129", 10)
        mk_bv_value(Sort(), "010", 2)
    with pytest.raises(RuntimeError):
      mk_bv_value(mk_bv_sort(8), "", 2)

def test_mk_fp_value():
    val = mk_fp_value(mk_bv_value(mk_bv_sort(1), 1),
                      mk_bv_value(mk_bv_sort(5), 0),
                      mk_bv_value(mk_bv_sort(10), 0))
    assert val.is_fp_value_neg_zero()

    with pytest.raises(RuntimeError):
        mk_fp_value(Term(),
                    mk_bv_value(mk_bv_sort(5), 0),
                    mk_bv_value(mk_bv_sort(10), 0))
    with pytest.raises(RuntimeError):
        mk_fp_value(mk_bv_value(mk_bv_sort(1), 1),
                    Term(),
                    mk_bv_value(mk_bv_sort(10), 0))
    with pytest.raises(RuntimeError):
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
