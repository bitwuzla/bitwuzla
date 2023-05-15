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
