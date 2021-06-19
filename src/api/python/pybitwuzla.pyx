###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

"""
The Python API of the SMT solver Bitwuzla.
"""

cimport bitwuzla_api
from libc.stdlib cimport malloc, free
from libc.stdio cimport stdout, FILE, fopen, fclose
from libc.stdint cimport int32_t, uint32_t, uint64_t
from libcpp cimport bool as cbool
from cpython.ref cimport PyObject
from cpython cimport array
import array
import math, os, sys

include "pybitwuzla_enums.pxd"

class BitwuzlaException(Exception):
    """ BitwuzlaException

        The class representing a Bitwuzla exception.
    """
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "[pybitwuzla] {}".format(self.msg)

# --------------------------------------------------------------------------- #
# Utility functions
# --------------------------------------------------------------------------- #

cdef str _to_str(const char *string):
    if string is NULL:
        return None
    cdef bytes py_str = string
    return str(py_str.decode())

cdef char * _to_cstr(s):
    if s is None:
        return NULL
    cdef bytes py_str = s.encode()
    cdef char * c_str = py_str
    return c_str

cdef _to_result(BitwuzlaResult result):
    if result == BITWUZLA_SAT:
        return Result.SAT
    elif result == BITWUZLA_UNSAT:
        return Result.UNSAT
    return Result.UNKNOWN

cdef bitwuzla_api.BitwuzlaTerm** _alloc_terms(size):
    cdef bitwuzla_api.BitwuzlaTerm **terms = \
        <bitwuzla_api.BitwuzlaTerm **> \
            malloc(size * sizeof(bitwuzla_api.BitwuzlaTerm*))
    if not terms:
        raise MemoryError()
    return terms

cdef bitwuzla_api.BitwuzlaSort** _alloc_sorts(size):
    cdef bitwuzla_api.BitwuzlaSort **sorts = \
        <bitwuzla_api.BitwuzlaSort **> \
            malloc(size * sizeof(bitwuzla_api.BitwuzlaSort*))
    if not sorts:
        raise MemoryError()
    return sorts

cdef _to_terms(Bitwuzla bitwuzla, size, bitwuzla_api.BitwuzlaTerm **c_terms):
    terms = []
    for i in range(size):
        term = BitwuzlaTerm(bitwuzla)
        term.set(c_terms[i])
        terms.append(term)
    return terms


# --------------------------------------------------------------------------- #
# Sort wrapper classes
# --------------------------------------------------------------------------- #

cdef class BitwuzlaSort:
    """ BitwuzlaSort

        The class representing a Bitwuzla sort.
    """
    cdef Bitwuzla bitwuzla
    cdef bitwuzla_api.BitwuzlaSort *_c_sort

    cdef set(self, bitwuzla_api.BitwuzlaSort* sort):
        self._c_sort = sort

    cdef bitwuzla_api.BitwuzlaSort* ptr(self):
        return self._c_sort

    cdef BitwuzlaSort new_sort(self, bitwuzla_api.BitwuzlaSort* sort):
        res = BitwuzlaSort(self.bitwuzla)
        res.set(sort)
        return res

    def __init__(self, Bitwuzla bitwuzla):
        self.bitwuzla = bitwuzla

    def bv_get_size(self):
        """
        """
        return bitwuzla_api.bitwuzla_sort_bv_get_size(self.ptr())

    def fp_get_exp_size(self):
        """
        """
        return bitwuzla_api.bitwuzla_sort_fp_get_exp_size(self.ptr())

    def fp_get_sig_size(self):
        """
        """
        return bitwuzla_api.bitwuzla_sort_fp_get_sig_size(self.ptr())

    def array_get_index(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_sort_array_get_index(self.ptr()))

    def array_get_element(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_sort_array_get_element(self.ptr()))

    def fun_get_domain_sorts(self):
        """
        """
        cdef size_t size
        cdef bitwuzla_api.BitwuzlaSort** sorts = \
                bitwuzla_api.bitwuzla_sort_fun_get_domain_sorts(self.ptr(),
                                                                &size)

        res = []
        for i in range(self.fun_get_arity()):
            res.append(self.new_sort(sorts[i]))
        return res

    def fun_get_codomain(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_sort_fun_get_codomain(self.ptr()))

    def fun_get_arity(self):
        return bitwuzla_api.bitwuzla_sort_fun_get_arity(self.ptr())

    def __eq__(self, BitwuzlaSort other):
        return bitwuzla_api.bitwuzla_sort_is_equal(self.ptr(), other.ptr())

    def is_array(self):
        return bitwuzla_api.bitwuzla_sort_is_array(self.ptr())

    def is_bv(self):
        return bitwuzla_api.bitwuzla_sort_is_bv(self.ptr())

    def is_fp(self):
        return bitwuzla_api.bitwuzla_sort_is_fp(self.ptr())

    def is_fun(self):
        return bitwuzla_api.bitwuzla_sort_is_fun(self.ptr())

    def is_rm(self):
        return bitwuzla_api.bitwuzla_sort_is_rm(self.ptr())


# --------------------------------------------------------------------------- #
# Wrapper classes for BitwuzlaTerm
# --------------------------------------------------------------------------- #

cdef class BitwuzlaTerm:
    """ BitwuzlaTerm

        The class representing a Bitwuzla term.
    """
    cdef Bitwuzla bitwuzla
    cdef bitwuzla_api.BitwuzlaTerm *_c_term

    cdef set(self, bitwuzla_api.BitwuzlaTerm* term):
        self._c_term = term

    cdef bitwuzla_api.BitwuzlaTerm* ptr(self):
        return self._c_term

    cdef BitwuzlaTerm new_term(self, bitwuzla_api.BitwuzlaTerm* term):
        res = BitwuzlaTerm(self.bitwuzla)
        res.set(term)
        return res

    cdef BitwuzlaSort new_sort(self, bitwuzla_api.BitwuzlaSort* sort):
        res = BitwuzlaSort(self.bitwuzla)
        res.set(sort)
        return res

    def __init__(self, Bitwuzla bitwuzla):
        self.bitwuzla = bitwuzla

    def __hash__(self):
        return bitwuzla_api.bitwuzla_term_hash(self.ptr())

    def __eq__(self, BitwuzlaTerm other):
        return self.ptr() == other.ptr()

    def get_children(self):
        cdef bitwuzla_api.BitwuzlaTerm** children
        cdef size_t size
        children = bitwuzla_api.bitwuzla_term_get_children(self.ptr(), &size)
        return _to_terms(self.bitwuzla, size, children)

    def get_indices(self):
        cdef uint32_t* indices
        cdef size_t size
        indices = bitwuzla_api.bitwuzla_term_get_indices(self.ptr(), &size)

        res = []
        for i in range(size):
            res.append(indices[i])
        return res

    def get_kind(self):
        cdef bitwuzla_api.BitwuzlaKind kind
        kind = bitwuzla_api.bitwuzla_term_get_kind(self.ptr())
        return Kind(kind)

    def get_sort(self):
        return self.new_sort(bitwuzla_api.bitwuzla_term_get_sort(self.ptr()))

    def array_get_index_sort(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_term_array_get_index_sort(
                        self.ptr()))

    def array_get_element_sort(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_term_array_get_element_sort(
                        self.ptr()))

    def fun_get_domain_sorts(self):
        return self.get_sort().fun_get_domain_sorts()

    def fun_get_codomain_sort(self):
        return self.new_sort(
                    bitwuzla_api.bitwuzla_term_fun_get_codomain_sort(
                        self.ptr()))

    def bv_get_size(self):
        return bitwuzla_api.bitwuzla_term_bv_get_size(self.ptr())

    def fp_get_exp_size(self):
        return bitwuzla_api.bitwuzla_term_fp_get_exp_size(self.ptr())

    def fp_get_sig_size(self):
        return bitwuzla_api.bitwuzla_term_fp_get_sig_size(self.ptr())

    def fun_get_arity(self):
        return bitwuzla_api.bitwuzla_term_fun_get_arity(self.ptr())

    def get_symbol(self):
        return _to_str(bitwuzla_api.bitwuzla_term_get_symbol(self.ptr()))

    def set_symbol(self, str symbol):
        bitwuzla_api.bitwuzla_term_set_symbol(self.ptr(), _to_cstr(symbol))

#    bool bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0, const BitwuzlaTerm *term1) \

    def is_array(self):
        return bitwuzla_api.bitwuzla_term_is_array(self.ptr())

    def is_const(self):
        return bitwuzla_api.bitwuzla_term_is_const(self.ptr())

    def is_const_array(self):
        return bitwuzla_api.bitwuzla_term_is_const_array(self.ptr())

    def is_fun(self):
        return bitwuzla_api.bitwuzla_term_is_fun(self.ptr())

    def is_var(self):
        return bitwuzla_api.bitwuzla_term_is_var(self.ptr())

    def is_bound_var(self):
        return bitwuzla_api.bitwuzla_term_is_var(self.ptr())

    def is_bv_value(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value(self.ptr())

    def is_fp_value(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value(self.ptr())

    def is_rm_value(self):
        return bitwuzla_api.bitwuzla_term_is_rm_value(self.ptr())

    def is_bv(self):
        return bitwuzla_api.bitwuzla_term_is_bv(self.ptr())

    def is_fp(self):
        return bitwuzla_api.bitwuzla_term_is_fp(self.ptr())

    def is_rm(self):
        return bitwuzla_api.bitwuzla_term_is_rm(self.ptr())

    def is_bv_value_zero(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value_zero(self.ptr())

    def is_bv_value_one(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value_one(self.ptr())

    def is_bv_value_ones(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value_ones(self.ptr())

    def is_bv_value_min_signed(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value_min_signed(self.ptr())

    def is_bv_value_max_signed(self):
        return bitwuzla_api.bitwuzla_term_is_bv_value_max_signed(self.ptr())

    def is_fp_value_pos_zero(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value_pos_zero(self.ptr())

    def is_fp_value_neg_zero(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value_neg_zero(self.ptr())

    def is_fp_value_pos_inf(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value_pos_inf(self.ptr())

    def is_fp_value_neg_inf(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value_neg_inf(self.ptr())

    def is_fp_value_nan(self):
        return bitwuzla_api.bitwuzla_term_is_fp_value_nan(self.ptr())

    def is_indexed(self):
        return bitwuzla_api.bitwuzla_term_is_indexed(self.ptr())

#
#    void bitwuzla_term_dump(const BitwuzlaTerm *term,
#                            const char *format,
#                            FILE *file) \

# -------------------------------------------------------------------------- #


# --------------------------------------------------------------------------- #
# Wrapper class for Bitwuzla solver
# --------------------------------------------------------------------------- #

cdef class Bitwuzla:
    """ Bitwuzla

        The class representing a Bitwuzla solver instance.
    """
    cdef bitwuzla_api.Bitwuzla *_c_bitwuzla

    def __init__(self):
        self._c_bitwuzla = bitwuzla_api.bitwuzla_new()
        if self._c_bitwuzla is NULL:
            raise MemoryError()
        bitwuzla_api.bitwuzla_set_abort_callback(
            bitwuzla_api.pybitwuzla_abort_fun)

    def __dealloc__(self):
        if self._c_bitwuzla is not NULL:
            bitwuzla_api.pybitwuzla_delete(self._c_bitwuzla)

    cdef bitwuzla_api.Bitwuzla* ptr(self):
        return self._c_bitwuzla

    # ------------------------------------------------------------------------
    # Termination callback
    # ------------------------------------------------------------------------

    def set_term(self, fun, args):
        """ set_term(fun, args)

            Set a termination callback function.

            Use this function to force Bitwuzla to prematurely terminate if
            callback function ``fun`` returns True. Arguments ``args`` to
            ``fun`` may be passed as a single Python object (in case that
            ``fun`` takes only one argument), a tuple, or a list of arguments.

            E.g., ::

              import time

              def fun1 (arg):
                  # timeout after 1 sec.
                  return time.time() - arg > 1.0

              def fun2 (arg0, arg1):
                  # do something and return True/False
                  ...

              bitwuzla = Bitwuzla()

              bitwuzla.set_term(fun1, time.time())
              bitwuzla.set_term(fun1, (time.time(),))
              bitwuzla.set_term(fun1, [time.time()])

              bitwuzla.set_term(fun2, (arg0, arg1))
              bitwuzla.set_term(run2, [arg0, arg1])

            :param fun: A python function.
            :param args: A function argument or a list or tuple of function arguments.
        """
        cdef PyObject* funptr = <PyObject*>fun
        cdef PyObject* argsptr = <PyObject*>args
        bitwuzla_api.pybitwuzla_set_term(self.ptr(), funptr, argsptr)

    def terminate(self):
        """ terminate()

            Determine if Bitwuzla has been terminated (and/or terminate
            Bitwuzla) via the previously configured termination callback
            function.

            See :func:`~pybitwuzla.Bitwuzla.set_term`.

            :return True if termination condition is fulfilled, else False.
            :rtype: bool
        """
        cdef int32_t res
        res = bitwuzla_api.bitwuzla_terminate(self.ptr())
        return res > 0

    # ------------------------------------------------------------------------
    # Bitwuzla API functions (general)
    # ------------------------------------------------------------------------

    def copyright(self):
        """ copyright()

            :return: The copyright information.
            :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_copyright(self.ptr())
        return _to_str(c_str)

    def version(self):
        """ version()

            :return: The version number.
            :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_version(self.ptr())
        return _to_str(c_str)

    def git_id(self):
        """ git_id()

            :return: The git commit sha.
            :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_git_id(self.ptr())
        return _to_str(c_str)

    def push(self, uint32_t levels = 1):
        """ push(level)

            push new context levels.

            :param level: Number of context levels to create.

            .. note::
              Assumptions added via `:~pybitwuzla.Bitwuzla.assume_formula`
              are not affected by context level changes and are only valid
              until the next `:~pybitwuzla.Bitwuzla.check_sat` call no matter
              at what level they were assumed.

            .. seealso::
                :func:`~pybitwuzla.Bitwuzla.assume_formula`
        """
        bitwuzla_api.bitwuzla_push(self.ptr(), levels)

    def pop(self, uint32_t levels = 1):
        """ pop(level)

            Pop context levels.

            :param level: Number of levels to pop.

            .. note::
              Assumptions added via `:~pybitwuzla.Bitwuzla.assume_formula`
              are not affected by context level changes and are only valid
              until the next `:~pybitwuzla.Bitwuzla.check_sat` call no matter
              at what level they were assumed.

            .. seealso::
                :func:`~pybitwuzla.Bitwuzla.assume_formula`
        """
        bitwuzla_api.bitwuzla_pop(self.ptr(), levels)

    def assert_formula(self, *formulas):
        """ assert_formula(formula,...)

            Assert one or more formulas.

            Added formulas can not be removed.

            :param formula: Boolean term.
            :type formula:  :class:`~pybitwuzla.BitwuzlaTerm`
        """
        for i in range(len(formulas)):
            f = formulas[i]
            if not isinstance(f, BitwuzlaTerm):
              raise BitwuzlaException("Argument at position {0:d} is not "\
                                       "a BitwuzlaTerm".format(i))
            n = <BitwuzlaTerm> f
            bitwuzla_api.bitwuzla_assert(self.ptr(), n._c_term)

    def check_sat(self):
        """ check_sat()

            Check satisfiability of asserted and assumed input formulas.

            Input formulas can either be asserted via
            :func:`~pybitwuzla.Boolector.Assert` or
            assumed via :func:`~pybitwuzla.Bitwuzla.assume_formula`.

            If this function is called multiple times it is required to
            enable incremental usage via :func:`~pybitwuzla.Bitwuzla.set_opt`.

            :return: `~pybitwuzla.Result.SAT` if the input formula is satisfiable (under possibly given assumptions), `~pybitwuzla.Result.UNSAT` if it is unsatisfiable, and `~pybitwuzla.Result.UNKNOWN` otherwise.

            .. note::
                Assertions and assumptions are combined via Boolean *and*.

            .. seealso::
                :data:`~pybitwuzla.Bitwuzla.get_value`
        """
        return _to_result(bitwuzla_api.bitwuzla_check_sat(self.ptr()))


    def simplify(self):
        """ simplify()

            Simplify current input formula.

            :return: `~pybitwuzla.Result.SAT` if the input formula was simplified to true, `~pybitwuzla.Result.UNSAT` if it was simplified to false, and `~pybitwuzla.Result.UNKNOWN` otherwise.

            .. note::
                Each call to :func:`~pybitwuzla.Bitwuzla.check_sat`
                simplifies the input formula as a preprocessing step.
        """
        return _to_result(bitwuzla_api.bitwuzla_simplify(self.ptr()))


    def get_unsat_core(self):
        """ get_unsat_core()

            Return list of unsatisfiable assertions previously added via
            :func:`~pybitwuzla.Bitwuzla.assert_formula`.

            Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
            returned `~pybitwuzla.Result.UNSAT`.

            :return:  list of unsatisfiable assertions
            :rtype:   list(BitwuzlaTerm)
        """

        cdef bitwuzla_api.BitwuzlaTerm** core
        cdef size_t size
        core = bitwuzla_api.bitwuzla_get_unsat_core(self.ptr(), &size)
        return _to_terms(self, size, core)

    def get_value(self, BitwuzlaTerm term):
        """ get_value(term)

            Get model value of term.

            Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
            returned `~pybitwuzla.Result.SAT`.

            :return: Term representing the model value of `term`.
            :rtype: BitwuzlaTerm

        """
        res = BitwuzlaTerm(self)
        res.set(bitwuzla_api.bitwuzla_get_value(self.ptr(), term.ptr()))
        return res

    def print_model(self):
        """
        """
        pass

    def dump_formula(self):
        """
        """
        pass

    # ------------------------------------------------------------------------
    # Assumption handling

    def assume_formula(self, *formulas):
        """ assume_formula(formula,...)

            Assume one or more formulas.

            You must enable incremental usage via
            :func:`~pybitwuzla.Bitwuzla.set_opt` before you can add
            assumptions.
            In contrast to assertions added via
            :func:`~pybitwuzla.Bitwuzla.assert`, assumptions
            are discarded after each call to
            :func:`~pybitwuzla.Bitwuzla.check_sat`.
            Assumptions and assertions are logically combined via Boolean
            *and*.
            Assumption handling in Bitwuzla is analogous to assumptions
            in MiniSAT.

            :param formula: Boolean term.
            :type formula:  :class:`~pybitwuzla.BitwuzlaTerm`
        """
        for i in range(len(formulas)):
            f = formulas[i]
            if not isinstance(f, BitwuzlaTerm):
              raise BitwuzlaException("Argument at position {0:d} is not "\
                                       "a BitwuzlaTerm".format(i))
            n = <BitwuzlaTerm> f
            bitwuzla_api.bitwuzla_assume(self.ptr(), n.ptr())

    def is_unsat_assumption(self,  *assumptions):
        """ is_unsat_assumption(a,...)

            Determine if any of the given assumptions are false assumptions.

            Unsat assumptions are those assumptions that force an
            input formula to become unsatisfiable.
            Unsat assumptions handling in Boolector is analogous to
            unsatisfiable assumptions in MiniSAT.

            See :func:`~pybitwuzla.Bitwuzla.assume_formula`.

            :param a: Boolean terms.
            :type a:  :class:`~pybitwuzla.BitwuzlaTerm`
            :return:  list of Boolean values, where True indicates that the assumption at given index is true or false.
            :rtype:   list(bool)
        """
        res = []
        for i in range(len(assumptions)):
            a = assumptions[i]
            if not isinstance(a, BitwuzlaTerm):
              raise BitwuzlaException("Argument at position {0:d} is not "\
                                       "a BitwuzlaTerm".format(i))
            n = <BitwuzlaTerm> a
            res.append(
                bitwuzla_api.bitwuzla_is_unsat_assumption(
                    self.ptr(), n.ptr()) == 1)
        return res

    def fixate_assumptions(self):
        """ fixate_assumptions()

            Assert all assumptions added since the last
            :func:`~pybitwuzla.Bitwuzla.check_sat` call as assertions.

            See :func:`~pybitwuzla.Bitwuzla.assume_formula`.
        """
        bitwuzla_api.bitwuzla_fixate_assumptions(self.ptr())

    def reset_assumptions(self):
        """ reset_assumptions()

            Remove all assumptions added since the last
            :func:`~pybitwuzla.Bitwuzla.check_sat` call.

            See :func:`~pybitwuzla.Bitwuzla.assume_formula`.
        """
        bitwuzla_api.bitwuzla_reset_assumptions(self.ptr())

    def get_unsat_assumptions(self):
        """ get_unsat_assumptions()

            Return list of unsatisfiable assumptions previously added via
            :func:`~pybitwuzla.Bitwuzla.assume_formula`.

            Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
            returned `~pybitwuzla.Result.UNSAT`.

            :return:  list of unsatisfiable assumptions
            :rtype:   list(BitwuzlaTerm)
        """

        cdef bitwuzla_api.BitwuzlaTerm** assumptions
        cdef size_t size
        assumptions = \
            bitwuzla_api.bitwuzla_get_unsat_assumptions(self.ptr(), &size)

        return _to_terms(self, size, assumptions)


    # ------------------------------------------------------------------------
    # Options

    def set_option(self, opt, value):
        """ set_option(opt, value)

            Set an option.

            :param opt:   Option.
            :type opt:    BitwuzlaOption
            :param value: Option value.
        """
        if not isinstance(opt, Option):
            raise ValueError("Given 'opt' is not an option object")
        if isinstance(value, str):
            bitwuzla_api.bitwuzla_set_option_str(
                    self.ptr(), opt.value, _to_cstr(value))
        else:
            bitwuzla_api.bitwuzla_set_option(self.ptr(), opt.value, value)

    def get_option(self, opt):
        """ get_option(opt)

            Get value of given Bitwuzla option ``opt``.

            For a list of all available options, see
            :func:`~pybitwuzla.Bitwuzla.set_option`.

            :param opt: Option.
            :type opt: BitwuzlaOption
            :return: Option value.
            :rtype: uint32_t
        """
        if not isinstance(opt, Option):
            raise ValueError("Given 'opt' is not an option object")
        return bitwuzla_api.bitwuzla_get_option(self.ptr(), opt.value)

    # ------------------------------------------------------------------------
    # Sort methods

    def mk_bool_sort(self):
        """ mk_bool_sort()

            Create a Boolean sort.

            :return: Sort of type Boolean.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
        """
        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_bool_sort(self.ptr()))
        return sort

    def mk_bv_sort(self, uint32_t width):
        """ mk_bv_sort(width)

            Create bit-vector sort of size ``width``.

            :param width: Bit width.
            :type width: uint32_t
            :return:  Bit-vector sort of bit width ``width``.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
        """
        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_bv_sort(self.ptr(), width))
        return sort

    def mk_array_sort(self, BitwuzlaSort index, BitwuzlaSort elem):
        """ mk_array_sort(index, elem)

            Create array sort with given index and element sorts.

            See :func:`~pybitwuzla.Bitwuzla.mk_array_sort`.

            :param index: The sort of the array index.
            :type index: :class:`~pybitwuzla.BitwuzlaSort`
            :param elem: The sort of the array elements.
            :type elem: :class:`~pybitwuzla.BitwuzlaSort`
            :return:  Array sort.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
          """
        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_array_sort(
                            self.ptr(), index.ptr(), elem.ptr()))
        return sort

    def mk_fun_sort(self, list domain, BitwuzlaSort codomain):
        """ mk_fun_sort(domain, codomain)

            Create function sort with given domain and codomain.

            See :func:`~pybitwuzla.Bitwuzla.mk_const`.

            :param domain: A list of all the function arguments' sorts.
            :type domain: list
            :param codomain: The sort of the function's return value.
            :type codomain: :class:`~pybitwuzla.BitwuzlaSort`
            :return:  Function sort, which maps ``domain`` to ``codomain``.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
          """
        cdef uint32_t arity = len(domain)
        cdef bitwuzla_api.BitwuzlaSort **c_domain = _alloc_sorts(arity)
        for i in range(arity):
            if not isinstance(domain[i], BitwuzlaSort):
                raise ValueError('Argument at position {} ' \
                                 'is not of type BitwuzlaSort'.format(i))
            c_domain[i] = (<BitwuzlaSort> domain[i]).ptr()

        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_fun_sort(
                        self.ptr(), arity, c_domain, codomain.ptr()))
        free(c_domain)
        return sort

    def mk_fp_sort(self, uint32_t exp_size, uint32_t sig_size):
        """ mk_fp_sort(exp_size, sig_size)

            Create a floating-point sort with given exponent size ``exp_size``
            and significand size ``sig_size``.

            :param exp_size: Exponent size.
            :type exp_size: uint32_t
            :param sig_size: Significand size.
            :type sig_size: uint32_t
            :return: Floating-point sort.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
        """
        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_fp_sort(
                    self.ptr(), exp_size, sig_size))
        return sort

    def mk_rm_sort(self):
        """ mk_rm_sort()

            Create a FP rounding mode sort.

            :return: Rounding mode sort.
            :rtype: :class:`~pybitwuzla.BitwuzlaSort`
        """
        sort = BitwuzlaSort(self)
        sort.set(bitwuzla_api.bitwuzla_mk_rm_sort(self.ptr()))
        return sort

    # ------------------------------------------------------------------------
    # Value methods

    # Bit-vector values

    def mk_bv_value(self, BitwuzlaSort sort, value):
        """
        """
        term = BitwuzlaTerm(self)
        is_str = isinstance(value, str)
        if is_str and (value.startswith('0x') or value.startswith('#x')):
            term.set(bitwuzla_api.bitwuzla_mk_bv_value(
                                self.ptr(),
                                sort.ptr(),
                                _to_cstr(value[2:]),
                                BITWUZLA_BV_BASE_HEX))
        elif is_str and (value.startswith('0b') or value.startswith('#b')):
            term.set(bitwuzla_api.bitwuzla_mk_bv_value(
                                self.ptr(),
                                sort.ptr(),
                                _to_cstr(value[2:]),
                                BITWUZLA_BV_BASE_BIN))
        elif (is_str and value.lstrip('-').isnumeric()) \
             or isinstance(value, int):
            term.set(bitwuzla_api.bitwuzla_mk_bv_value(
                                self.ptr(),
                                sort.ptr(),
                                _to_cstr(str(value)),
                                BITWUZLA_BV_BASE_DEC))
        else:
            raise ValueError("Cannot convert '{}' to " \
                             "bit-vector value.".format(value))
        return term

    def mk_bv_ones(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_bv_ones(self.ptr(), sort.ptr()))
        return term

    def mk_bv_min_signed(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_bv_min_signed(
                    self.ptr(), sort.ptr()))
        return term

    def mk_bv_max_signed(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_bv_max_signed(
                    self.ptr(), sort.ptr()))
        return term

    # Floating-point values

    def mk_fp_value(self, BitwuzlaSort sort, sign, exponent, significand):
        """
        """
        _exp_size = bitwuzla_api.bitwuzla_sort_fp_get_exp_size(sort.ptr())
        _sig_size = bitwuzla_api.bitwuzla_sort_fp_get_sig_size(sort.ptr())

        sort_sign = self.mk_bool_sort()
        sort_exp = self.mk_bv_sort(_exp_size)
        sort_significand = self.mk_bv_sort(_sig_size - 1)

        cdef BitwuzlaTerm val_sign = self.mk_bv_value(sort_sign, sign)
        cdef BitwuzlaTerm val_exp = self.mk_bv_value(sort_exp, exponent)
        cdef BitwuzlaTerm val_significand = \
                self.mk_bv_value(sort_significand, significand)

        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_value(
                            self.ptr(),
                            val_sign.ptr(),
                            val_exp.ptr(),
                            val_significand.ptr()))
        return term

    def mk_fp_value_from(self, BitwuzlaSort sort, BitwuzlaTerm rm, value):
        """
        """
        term = BitwuzlaTerm(self)
        if isinstance(value, str) and '/' in value:
            num, den = value.split('/')
            term.set(bitwuzla_api.bitwuzla_mk_fp_value_from_rational(
                                self.ptr(),
                                sort.ptr(),
                                rm.ptr(),
                                _to_cstr(num),
                                _to_cstr(den)))

        else:
            term.set(bitwuzla_api.bitwuzla_mk_fp_value_from_real(
                                self.ptr(),
                                sort.ptr(),
                                rm.ptr(),
                                _to_cstr(str(value))))
        return term


    def mk_fp_pos_zero(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_pos_zero(self.ptr(), sort.ptr()))
        return term

    def mk_fp_neg_zero(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_neg_zero(self.ptr(), sort.ptr()))
        return term

    def mk_fp_pos_inf(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_pos_inf(self.ptr(), sort.ptr()))
        return term

    def mk_fp_neg_inf(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_neg_inf(self.ptr(), sort.ptr()))
        return term

    def mk_fp_nan(self, BitwuzlaSort sort):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_fp_nan(self.ptr(), sort.ptr()))
        return term

    def mk_rm_value(self, rm):
        """
        """
        if not isinstance(rm, RoundingMode):
            raise ValueError("Given 'rm' is not a RoundingMode value")
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_rm_value(self.ptr(), rm.value))
        return term


    # ------------------------------------------------------------------------
    # Term methods

    def mk_const(self, BitwuzlaSort sort, str symbol = None):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_const(
                    self.ptr(), sort.ptr(), _to_cstr(symbol)))
        return term

    def mk_const_array(self, BitwuzlaSort sort, BitwuzlaTerm value):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_const_array(
                    self.ptr(), sort.ptr(), value.ptr()))
        return term

    def mk_var(self, BitwuzlaSort sort, str symbol = None):
        """
        """
        term = BitwuzlaTerm(self)
        term.set(bitwuzla_api.bitwuzla_mk_var(
                    self.ptr(), sort.ptr(), _to_cstr(symbol)))
        return term

    def mk_term(self, kind, terms, indices = None):
        """
        """
        if not isinstance(kind, Kind):
            raise ValueError('Given kind is not a Kind object.')
        if not isinstance(terms, list) and not isinstance(terms, tuple):
            raise ValueError('Expected list or tuple for terms')
        if indices is not None \
            and not isinstance(indices, list) \
            and not isinstance(indices, tuple):
            raise ValueError('Expected list or tuple for indices')

        num_terms = len(terms)
        cdef bitwuzla_api.BitwuzlaTerm **c_terms = _alloc_terms(num_terms)

        for i in range(num_terms):
            if not isinstance(terms[i], BitwuzlaTerm):
                raise ValueError('Argument at position {} is ' \
                                 'not of type BitwuzlaTerm'.format(i))
            c_terms[i] = (<BitwuzlaTerm> terms[i]).ptr()

        term = BitwuzlaTerm(self)

        cdef array.array c_indices
        if indices:
            c_indices = array.array('I', indices)
            term.set(bitwuzla_api.bitwuzla_mk_term_indexed(
                            self.ptr(),
                            kind.value,
                            num_terms,
                            c_terms,
                            len(indices),
                            c_indices.data.as_uints))
        else:
            term.set(bitwuzla_api.bitwuzla_mk_term(
                        self.ptr(), kind.value, num_terms, c_terms))
        free(c_terms)

        return term


    def substitute(self, terms, dict map):
        if not isinstance(terms, BitwuzlaTerm) and not isinstance(terms, list):
            raise ValueError('Expected BitwuzlaTerm or list of ' \
                             'BitwuzlaTerm but got {}'.format(type(terms)))
        got_term = False
        if isinstance(terms, BitwuzlaTerm):
            got_term = True
            terms = [terms]

        num_terms = len(terms)
        size_map = len(map)
        cdef bitwuzla_api.BitwuzlaTerm **c_terms = _alloc_terms(num_terms)
        cdef bitwuzla_api.BitwuzlaTerm **c_keys = _alloc_terms(size_map)
        cdef bitwuzla_api.BitwuzlaTerm **c_values = _alloc_terms(size_map)

        for i in range(num_terms):
            if not isinstance(terms[i], BitwuzlaTerm):
                raise ValueError('Expected BitwuzlaTerm but got {}'.format(
                                    type(terms[i])))
            c_terms[i] = (<BitwuzlaTerm> terms[i]).ptr()

        i = 0
        for k, v in map.items():
            if not isinstance(k, BitwuzlaTerm):
                raise ValueError('Expected BitwuzlaTerm as key ' \
                                 'but got {}'.format(type(terms[i])))
            if not isinstance(v, BitwuzlaTerm):
                raise ValueError('Expected BitwuzlaTerm as value ' \
                                 'but got {}'.format(type(terms[i])))
            c_keys[i] = (<BitwuzlaTerm> k).ptr()
            c_values[i] = (<BitwuzlaTerm> v).ptr()
            i += 1

        bitwuzla_api.bitwuzla_substitute_terms(self.ptr(),
                                                num_terms,
                                                c_terms,
                                                size_map,
                                                c_keys,
                                                c_values)

        if got_term:
            term = BitwuzlaTerm(self)
            term.set(c_terms[0])
            return term
        return _to_terms(self, num_terms, c_terms)
