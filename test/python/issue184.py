###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2026 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

# Regression tests for https://github.com/bitwuzla/bitwuzla/issues/184
#
# Cyclic GC could destroy the C++ TermManager (and its NodeManager) before
# the C++ Term destructor ran, producing a use-after-free in
# NodeData::dec_ref. The fix lives in the C++ API: NodeManager and
# TypeManager each defer their actual destruction until their last
# NodeData/TypeData is freed, so a surviving Python Term/Sort can still
# safely run its C++ destructor after its TermManager has gone away.
#
# Without the fix these tests SIGSEGV (or report a heap-use-after-free
# under ASAN) inside gc.collect().

import gc

import pytest

from bitwuzla import (
    Bitwuzla,
    Kind,
    Options,
    RoundingMode,
    TermManager,
)


def test_rm_value_in_self_cycle_list():
    """List cycle that pulls a Term and its TermManager into the
    unreachable set together."""
    tm = TermManager()
    rm = tm.mk_rm_value(RoundingMode.RNE)
    cycle = [rm, tm]
    cycle.append(cycle)
    del tm, rm, cycle
    gc.collect()


def test_sort_in_self_cycle_list():
    """Same pattern but for Sort, which has the analogous c_sort
    destructor path."""
    tm = TermManager()
    sort = tm.mk_fp_sort(8, 24)
    cycle = [sort, tm]
    cycle.append(cycle)
    del tm, sort, cycle
    gc.collect()


def test_rm_value_in_dict_cycle():
    """A dict cycle exercises a different tp_clear order than a list."""
    tm = TermManager()
    rm = tm.mk_rm_value(RoundingMode.RNE)
    d = {'rm': rm, 'tm': tm}
    d['self'] = d
    del tm, rm, d
    gc.collect()


def test_class_attribute_pattern():
    """The exact attribute pattern from issue #184:

        self.default_rm = self.tm.mk_rm_value(RoundingMode.RNE)
    """
    class Holder:
        def __init__(self):
            self.tm = TermManager()
            self.default_rm = self.tm.mk_rm_value(RoundingMode.RNE)
            self._cycle = self  # reach back to self via instance dict

    h = Holder()
    del h
    gc.collect()


def test_solver_with_fp_in_cycle():
    """Full solver setup with a floating-point query, mirroring the
    reporter's use case (rounding mode wrapped because FP ops require
    a Term, plus a Bitwuzla solver pinned alongside)."""
    class Solver:
        def __init__(self):
            self.tm = TermManager()
            self.opts = Options()
            self.bzla = Bitwuzla(self.tm, self.opts)
            self.default_rm = self.tm.mk_rm_value(RoundingMode.RNE)
            fp_sort = self.tm.mk_fp_sort(8, 24)
            x = self.tm.mk_const(fp_sort, "x")
            y = self.tm.mk_const(fp_sort, "y")
            self.bzla.assert_formula(
                self.tm.mk_term(
                    Kind.EQUAL,
                    [x, self.tm.mk_term(
                        Kind.FP_ADD, [self.default_rm, x, y])],
                ))
            self.bzla.check_sat()
            self._cycle = self

    solvers = [Solver() for _ in range(5)]
    del solvers
    gc.collect()


def test_term_outlives_explicit_termmanager_drop():
    """Dropping the only reference to the TermManager destroys the C++
    TermManager, but the surviving Term holds a NodeData reference that
    keeps the underlying NodeManager alive (its destruction is deferred
    until the last NodeData is freed), so the Term stays valid."""
    tm = TermManager()
    rm = tm.mk_rm_value(RoundingMode.RNE)
    del tm
    gc.collect()
    # Touching the surviving Term must not access freed memory.
    assert rm.is_value()
    assert rm.sort().is_rm()


@pytest.mark.parametrize("_iteration", range(20))
def test_cycle_repeated(_iteration):
    """Repeat the minimal cycle multiple times to catch order-sensitive
    flakiness in the cyclic GC path."""
    tm = TermManager()
    rm = tm.mk_rm_value(RoundingMode.RNE)
    cycle = [rm, tm]
    cycle.append(cycle)
    del tm, rm, cycle
    gc.collect()
