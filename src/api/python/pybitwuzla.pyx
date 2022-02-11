###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
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
from collections import defaultdict
import array
import math, os, sys
import tempfile

include "pybitwuzla_enums.pxd"

class BitwuzlaException(Exception):
    """Bitwuzla exception class."""
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

cdef const bitwuzla_api.BitwuzlaTerm** _alloc_terms(size):
    cdef const bitwuzla_api.BitwuzlaTerm **terms = \
        <const bitwuzla_api.BitwuzlaTerm **> \
            malloc(size * sizeof(bitwuzla_api.BitwuzlaTerm*))
    if not terms:
        raise MemoryError()
    return terms

cdef const bitwuzla_api.BitwuzlaTerm** _alloc_terms_const(size):
    cdef const bitwuzla_api.BitwuzlaTerm **terms = \
        <const bitwuzla_api.BitwuzlaTerm **> \
            malloc(size * sizeof(bitwuzla_api.BitwuzlaTerm*))
    if not terms:
        raise MemoryError()
    return terms

cdef const bitwuzla_api.BitwuzlaSort** _alloc_sorts_const(size):
    cdef const bitwuzla_api.BitwuzlaSort **sorts = \
        <const bitwuzla_api.BitwuzlaSort **> \
            malloc(size * sizeof(bitwuzla_api.BitwuzlaSort*))
    if not sorts:
        raise MemoryError()
    return sorts

cdef _to_term(Bitwuzla bitwuzla, const bitwuzla_api.BitwuzlaTerm* term):
    t = BitwuzlaTerm(bitwuzla)
    t.set(term)
    return t

cdef _to_terms(Bitwuzla bitwuzla, size,
               const bitwuzla_api.BitwuzlaTerm **c_terms):
    return [_to_term(bitwuzla, c_terms[i]) for i in range(size)]

cdef _to_sort(Bitwuzla bitwuzla, const bitwuzla_api.BitwuzlaSort* sort):
    s = BitwuzlaSort(bitwuzla)
    s.set(sort)
    return s

# --------------------------------------------------------------------------- #
# Sort wrapper classes
# --------------------------------------------------------------------------- #

cdef class BitwuzlaSort:
    """Class representing a Bitwuzla sort."""
    cdef Bitwuzla bitwuzla
    cdef const bitwuzla_api.BitwuzlaSort *_c_sort

    cdef set(self, const bitwuzla_api.BitwuzlaSort* sort):
        self._c_sort = <const bitwuzla_api.BitwuzlaSort*> sort

    cdef const bitwuzla_api.BitwuzlaSort* ptr(self):
        return self._c_sort

    def __init__(self, Bitwuzla bitwuzla):
        self.bitwuzla = bitwuzla

    def bv_get_size(self):
        """Get size of bit-vector sort.

           :return: Size of bit-vector sort.
           :rtype: int
        """
        return bitwuzla_api.bitwuzla_sort_bv_get_size(self.ptr())

    def fp_get_exp_size(self):
        """Get size of exponent of floating-point sort.

           :return: Size of exponent.
           :rtype: int
        """
        return bitwuzla_api.bitwuzla_sort_fp_get_exp_size(self.ptr())

    def fp_get_sig_size(self):
        """Get size of significand of floating-point sort.

           :return: Size of significand.
           :rtype: int
        """
        return bitwuzla_api.bitwuzla_sort_fp_get_sig_size(self.ptr())

    def array_get_index(self):
        """Get index sort of array sort.

           :return: Index sort.
           :rtype: BitwuzlaSort
        """
        return _to_sort(self.bitwuzla,
                        bitwuzla_api.bitwuzla_sort_array_get_index(self.ptr()))

    def array_get_element(self):
        """Get element sort of array sort.

           :return: Element sort.
           :rtype: BitwuzlaSort
        """
        return _to_sort(
                    self.bitwuzla,
                    bitwuzla_api.bitwuzla_sort_array_get_element(self.ptr()))

    def fun_get_domain_sorts(self):
        """Get domain sorts of function sort.

           :return: Domain sorts.
           :rtype: list(BitwuzlaSort)
        """
        cdef size_t size
        cdef const bitwuzla_api.BitwuzlaSort** sorts = \
                bitwuzla_api.bitwuzla_sort_fun_get_domain_sorts(self.ptr(),
                                                                &size)
        return [_to_sort(self.bitwuzla, sorts[i]) for i in range(size)]

    def fun_get_codomain(self):
        """ Get codomain sort of function sort.

            :return: Codomain sort.
            :rtype: BitwuzlaSort
        """
        return _to_sort(self.bitwuzla,
                        bitwuzla_api.bitwuzla_sort_fun_get_codomain(self.ptr()))

    def fun_get_arity(self):
        """Get arity of function sort.

           :return: Function arity.
           :rtype: int
        """
        return bitwuzla_api.bitwuzla_sort_fun_get_arity(self.ptr())

    def __eq__(self, BitwuzlaSort other):
        return bitwuzla_api.bitwuzla_sort_is_equal(self.ptr(), other.ptr())

    def is_array(self):
        """:return: True if sort is an array sort, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_sort_is_array(self.ptr())

    def is_bv(self):
        """:return: True if sort is a bit-vector sort, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_sort_is_bv(self.ptr())

    def is_fp(self):
        """:return: True if sort is a floating-point sort, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_sort_is_fp(self.ptr())

    def is_fun(self):
        """:return: True if sort is a function sort, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_sort_is_fun(self.ptr())

    def is_rm(self):
        """:return: True if sort is a rounding mode sort, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_sort_is_rm(self.ptr())


# --------------------------------------------------------------------------- #
# Wrapper classes for BitwuzlaTerm
# --------------------------------------------------------------------------- #

cdef class BitwuzlaTerm:
    """Class representing a Bitwuzla term."""
    cdef Bitwuzla bitwuzla
    cdef const bitwuzla_api.BitwuzlaTerm *_c_term

    cdef set(self, const bitwuzla_api.BitwuzlaTerm* term):
        self._c_term = <const bitwuzla_api.BitwuzlaTerm*> term

    cdef const bitwuzla_api.BitwuzlaTerm* ptr(self):
        return self._c_term

    def __init__(self, Bitwuzla bitwuzla):
        self.bitwuzla = bitwuzla

    def __hash__(self):
        return bitwuzla_api.bitwuzla_term_hash(self.ptr())

    def __eq__(self, BitwuzlaTerm other):
        return self.ptr() == other.ptr()

    def dump(self, fmt='smt2'):
        """dump(fmt = "smt2")

           Get string representation of term in format ``fmt``.

           :param fmt: Output format. Available formats: "btor", "smt2"
           :type: str

           :return: String representation of the term in format ``fmt``.
           :rtype: str
        """
        cdef FILE * out
        with tempfile.NamedTemporaryFile('r') as f:
            out = fopen(_to_cstr(f.name), 'w')
            bitwuzla_api.bitwuzla_term_dump(self.ptr(), _to_cstr(fmt), out)
            fclose(out)
            return f.read().strip()

    def get_children(self):
        """:return: The children of the term.
           :rtype: list(BitwuzlaTerm)
        """
        cdef const bitwuzla_api.BitwuzlaTerm** children
        cdef size_t size
        children = bitwuzla_api.bitwuzla_term_get_children(self.ptr(), &size)
        return _to_terms(self.bitwuzla, size, children)

    def get_indices(self):
        """:return: Indices of indexed operator.
           :rtype: list(int)
        """
        cdef uint32_t* indices
        cdef size_t size
        indices = bitwuzla_api.bitwuzla_term_get_indices(self.ptr(), &size)
        return [indices[i] for i in range(size)]

    def get_kind(self):
        """:return: Operator kind of term.
           :rtype: Kind
        """
        cdef bitwuzla_api.BitwuzlaKind kind
        kind = bitwuzla_api.bitwuzla_term_get_kind(self.ptr())
        return Kind(kind)

    def get_sort(self):
        """:return: The sort of the term.
           :rtype: BitwuzlaSort
        """
        return _to_sort(self.bitwuzla,
                        bitwuzla_api.bitwuzla_term_get_sort(self.ptr()))

    def get_symbol(self):
        """:return: The symbol of the term.
           :rtype: str

           .. seealso::
               :func:`~pybitwuzla.BitwuzlaTerm.set_symbol`
        """
        return _to_str(bitwuzla_api.bitwuzla_term_get_symbol(self.ptr()))

    def set_symbol(self, str symbol):
        """set_symbol(symbol)

           Set the symbol of the term.

           :param symbol: Symbol of the term.
           :type symbol: str
        """
        bitwuzla_api.bitwuzla_term_set_symbol(self.ptr(), _to_cstr(symbol))

    def is_array(self):
        """:return: True if term is an array, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_array(self.ptr())

    def is_const(self):
        """:return: True if term is a constant, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_const(self.ptr())

    def is_const_array(self):
        """:return: True if term is a constant array, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_const_array(self.ptr())

    def is_fun(self):
        """:return: True if term is a function, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fun(self.ptr())

    def is_var(self):
        """:return: True if term is a variable, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_var(self.ptr())

    def is_bound_var(self):
        """:return: True if term is a bound variable, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bound_var(self.ptr())

    def is_bv_value(self):
        """:return: True if term is a bit-vector value, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value(self.ptr())

    def is_fp_value(self):
        """:return: True if term is a floating-point value, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value(self.ptr())

    def is_rm_value(self):
        """:return: True if term is a rounding mode value, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_rm_value(self.ptr())

    def is_bv(self):
        """:return: True if term is a bit-vector, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv(self.ptr())

    def is_fp(self):
        """:return: True if term is a floating-point, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp(self.ptr())

    def is_rm(self):
        """:return: True if term is a rounding mode, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_rm(self.ptr())

    def is_bv_value_zero(self):
        """:return: True if term is a bit-vector value zero, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value_zero(self.ptr())

    def is_bv_value_one(self):
        """:return: True if term is a bit-vector value one, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value_one(self.ptr())

    def is_bv_value_ones(self):
        """:return: True if term is a bit-vector value ones, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value_ones(self.ptr())

    def is_bv_value_min_signed(self):
        """:return: True if term is a bit-vector minimum signed value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value_min_signed(self.ptr())

    def is_bv_value_max_signed(self):
        """:return: True if term is a bit-vector maximum signed value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_bv_value_max_signed(self.ptr())

    def is_fp_value_pos_zero(self):
        """:return: True if term is a floating-point positive zero value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value_pos_zero(self.ptr())

    def is_fp_value_neg_zero(self):
        """:return: True if term is a floating-point negative zero value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value_neg_zero(self.ptr())

    def is_fp_value_pos_inf(self):
        """:return: True if term is a floating-point positive infinity value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value_pos_inf(self.ptr())

    def is_fp_value_neg_inf(self):
        """:return: True if term is a floating-point negative infinity value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value_neg_inf(self.ptr())

    def is_fp_value_nan(self):
        """:return: True if term is a floating-point NaN value,
                    False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_fp_value_nan(self.ptr())

    def is_indexed(self):
        """:return: True if term is indexed, False otherwise.
           :rtype: bool
        """
        return bitwuzla_api.bitwuzla_term_is_indexed(self.ptr())

# -------------------------------------------------------------------------- #


# --------------------------------------------------------------------------- #
# Wrapper class for Bitwuzla solver
# --------------------------------------------------------------------------- #

cdef class Bitwuzla:
    """Class representing a Bitwuzla solver instance."""
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
        """set_term(fun, args)

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
           :param args: A function argument or a list or tuple of function
                        arguments.
        """
        cdef PyObject* funptr = <PyObject*>fun
        cdef PyObject* argsptr = <PyObject*>args
        bitwuzla_api.pybitwuzla_set_term(self.ptr(), funptr, argsptr)

    def terminate(self):
        """Call terminate callback that was set via
           :func:`~pybitwuzla.Bitwuzla.set_term`.

           :return: True if termination condition is fulfilled, else False.
           :rtype: bool

           .. seealso::
                :func:`~pybitwuzla.Bitwuzla.set_term`.
        """
        cdef int32_t res
        res = bitwuzla_api.bitwuzla_terminate(self.ptr())
        return res > 0

    # ------------------------------------------------------------------------
    # Bitwuzla API functions (general)
    # ------------------------------------------------------------------------

    def copyright(self):
        """:return: The copyright information.
           :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_copyright(self.ptr())
        return _to_str(c_str)

    def version(self):
        """:return: The version number.
           :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_version(self.ptr())
        return _to_str(c_str)

    def git_id(self):
        """:return: The git commit sha.
           :rtype: str
        """
        cdef const char * c_str
        c_str = bitwuzla_api.bitwuzla_git_id(self.ptr())
        return _to_str(c_str)

    def push(self, uint32_t levels = 1):
        """push(levels = 1)

           Push new context levels.

           :param levels: Number of context levels to create.
           :type levels: int

           .. note::
             Assumptions added via :func:`~pybitwuzla.Bitwuzla.assume_formula`
             are not affected by context level changes and are only valid
             until the next :func:`~pybitwuzla.Bitwuzla.check_sat` call no matter
             at what level they were assumed.

           .. seealso::
               :func:`~pybitwuzla.Bitwuzla.assume_formula`
        """
        bitwuzla_api.bitwuzla_push(self.ptr(), levels)

    def pop(self, uint32_t levels = 1):
        """pop(levels = 1)

           Pop context levels.

           :param levels: Number of levels to pop.
           :type levels: int

           .. note::
             Assumptions added via :func:`~pybitwuzla.Bitwuzla.assume_formula`
             are not affected by context level changes and are only valid
             until the next :func:`~pybitwuzla.Bitwuzla.check_sat` call no matter
             at what level they were assumed.

           .. seealso::
               :func:`~pybitwuzla.Bitwuzla.assume_formula`
        """
        bitwuzla_api.bitwuzla_pop(self.ptr(), levels)

    def assert_formula(self, *formulas):
        """assert_formula(formula,...)

           Assert one or more formulas.

           :param formula: Boolean term.
           :type formula: BitwuzlaTerm
        """
        for i in range(len(formulas)):
            f = formulas[i]
            if not isinstance(f, BitwuzlaTerm):
              raise BitwuzlaException("Argument at position {0:d} is not "\
                                       "a BitwuzlaTerm".format(i))
            n = <BitwuzlaTerm> f
            bitwuzla_api.bitwuzla_assert(self.ptr(), n._c_term)

    def check_sat(self):
        """Check satisfiability of asserted and assumed input formulas.

           Input formulas can either be asserted via
           :func:`~pybitwuzla.Bitwuzla.assert_formula` or
           assumed via :func:`~pybitwuzla.Bitwuzla.assume_formula`.

           If this function is called multiple times it is required to
           enable incremental usage via :func:`~pybitwuzla.Bitwuzla.set_opt`.

           :return: - :class:`~pybitwuzla.Result.SAT` if the input formula is
                      satisfiable (under possibly given assumptions)
                    - :class:`~pybitwuzla.Result.UNSAT` if it is unsatisfiable
                    - :class:`~pybitwuzla.Result.UNKNOWN` otherwise
           :rtype: Result

           .. note::
               Assertions and assumptions are combined via Boolean *and*.

           .. seealso::
               :func:`~pybitwuzla.Bitwuzla.get_value`,
               :func:`~pybitwuzla.Bitwuzla.get_value_str`
        """
        return _to_result(bitwuzla_api.bitwuzla_check_sat(self.ptr()))


    def simplify(self):
        """Simplify current input formula.

           :return: - :class:`~pybitwuzla.Result.SAT` if the input formula is
                      satisfiable (under possibly given assumptions)
                    - :class:`~pybitwuzla.Result.UNSAT` if it is unsatisfiable
                    - :class:`~pybitwuzla.Result.UNKNOWN` otherwise
           :rtype: Result

           .. note::
               Each call to :func:`~pybitwuzla.Bitwuzla.check_sat`
               simplifies the input formula as a preprocessing step.
        """
        return _to_result(bitwuzla_api.bitwuzla_simplify(self.ptr()))


    def get_unsat_core(self):
        """Return list of unsatisfiable assertions previously added via
           :func:`~pybitwuzla.Bitwuzla.assert_formula`.

           Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
           returned :class:`~pybitwuzla.Result.UNSAT`.

           :return:  list of unsatisfiable assertions
           :rtype:   list(BitwuzlaTerm)
        """

        cdef const bitwuzla_api.BitwuzlaTerm** core
        cdef size_t size
        core = bitwuzla_api.bitwuzla_get_unsat_core(self.ptr(), &size)
        return _to_terms(self, size, core)

    def get_value(self, BitwuzlaTerm term):
        """get_value(term)

           Get model value of term.

           Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
           returned `~pybitwuzla.Result.SAT`.

           :return: Term representing the model value of `term`.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self, bitwuzla_api.bitwuzla_get_value(self.ptr(),
                                                              term.ptr()))

    def get_value_str(self, BitwuzlaTerm term):
        """get_value_str(term)

           Get string representation of model value of a `term`.

           Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
           returned :class:`~pybitwuzla.Result.SAT`.

           :return:
               - arrays: dictionary mapping indices to values
               - bit-vectors: bit string
               - floating-points: 3-tuple of bit strings
                 (sign, exponent, significand)
               - functions: dictionary mapping tuples of arguments to values
               - rounding mode: string representation of rounding mode value
        """
        cdef const char* sign
        cdef const char* exponent
        cdef const char* significand
        cdef const bitwuzla_api.BitwuzlaTerm** array_indices
        cdef const bitwuzla_api.BitwuzlaTerm** array_values
        cdef const bitwuzla_api.BitwuzlaTerm* array_default_value
        cdef size_t array_size
        cdef const bitwuzla_api.BitwuzlaTerm*** fun_args
        cdef const bitwuzla_api.BitwuzlaTerm** fun_values
        cdef size_t fun_arity, fun_size

        if term.is_array():
            bitwuzla_api.bitwuzla_get_array_value(self.ptr(),
                                                  term.ptr(),
                                                  &array_indices,
                                                  &array_values,
                                                  &array_size,
                                                  &array_default_value)

            if array_default_value is not NULL:
                val = defaultdict(lambda: self.get_value_str(
                                    _to_term(self, array_default_value)))
            else:
                val = dict()

            for i in range(array_size):
                vi = self.get_value_str(_to_term(self, array_indices[i]))
                ve = self.get_value_str(_to_term(self, array_values[i]))
                val[vi] = ve

            return val
        elif term.is_bv():
            return _to_str(bitwuzla_api.bitwuzla_get_bv_value(self.ptr(),
                                                              term.ptr()))
        elif term.is_fp():
            bitwuzla_api.bitwuzla_get_fp_value(self.ptr(),
                                               term.ptr(),
                                               &sign,
                                               &exponent,
                                               &significand)
            return (_to_str(sign), _to_str(exponent), _to_str(significand))
        elif term.is_fun():
            bitwuzla_api.bitwuzla_get_fun_value(self.ptr(),
                                                term.ptr(),
                                                &fun_args,
                                                &fun_arity,
                                                &fun_values,
                                                &fun_size)

            val = dict()
            for i in range(fun_size):
                args = [self.get_value_str(_to_term(self, fun_args[i][j])) \
                            for j in range(fun_arity)]
                val[tuple(args)] = self.get_value_str(_to_term(self,
                                                               fun_values[i]))
            return val
        else:
            assert term.is_rm()
            return _to_str(bitwuzla_api.bitwuzla_get_rm_value(self.ptr(),
                                                              term.ptr()))

    def get_model(self, fmt='smt2'):
        """get_model(fmt = "smt2")

           Get the model as a string in format ``fmt``.

           :param fmt: Model format. Available formats: "btor", "smt2"
           :type: str

           :return: String representation of model in format ``fmt``.
           :rtype: str
        """
        cdef FILE * out
        with tempfile.NamedTemporaryFile('r') as f:
            out = fopen(_to_cstr(f.name), 'w')
            bitwuzla_api.bitwuzla_print_model(self.ptr(), _to_cstr(fmt), out)
            fclose(out)
            return f.read().strip()


    def dump_formula(self, fmt='smt2'):
        """dump_formula(fmt = "smt2")

           Dump the current formula as a string in format ``fmt``.

           :param fmt: Model format. Available formats: "btor", "smt2"
           :type: str

           :return: String representation of formula in format ``fmt``.
           :rtype: str
        """
        cdef FILE * out
        with tempfile.NamedTemporaryFile('r') as f:
            out = fopen(_to_cstr(f.name), 'w')
            bitwuzla_api.bitwuzla_dump_formula(self.ptr(), _to_cstr(fmt), out)
            fclose(out)
            return f.read().strip()

    # ------------------------------------------------------------------------
    # Assumption handling

    def assume_formula(self, *formulas):
        """assume_formula(formula,...)

           Assume one or more formulas.

           You must enable incremental usage via
           :func:`~pybitwuzla.Bitwuzla.set_option` before you can add
           assumptions.
           In contrast to assertions added via
           :func:`~pybitwuzla.Bitwuzla.assert_formula`, assumptions
           are discarded after each call to
           :func:`~pybitwuzla.Bitwuzla.check_sat`.
           Assumptions and assertions are logically combined via Boolean
           *and*.
           Assumption handling in Bitwuzla is analogous to assumptions
           in MiniSAT.

           :param formula: Boolean term.
           :type formula: BitwuzlaTerm
        """
        for i in range(len(formulas)):
            f = formulas[i]
            if not isinstance(f, BitwuzlaTerm):
              raise BitwuzlaException("Argument at position {0:d} is not "\
                                       "a BitwuzlaTerm".format(i))
            n = <BitwuzlaTerm> f
            bitwuzla_api.bitwuzla_assume(self.ptr(), n.ptr())

    def is_unsat_assumption(self, *assumptions):
        """is_unsat_assumption(assumption,...)

           Determine if any of the given assumptions are false assumptions.

           Unsat assumptions are those assumptions that force an
           input formula to become unsatisfiable.
           Unsat assumptions handling in Bitwuzla is analogous to
           unsatisfiable assumptions in MiniSAT.

           See :func:`~pybitwuzla.Bitwuzla.assume_formula`.

           :param assumption: Boolean terms.
           :type assumption:  BitwuzlaTerm
           :return:  List of Boolean values, where True indicates that the
                     assumption at given index is true or false.
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
        """Assert all assumptions added since the last
           :func:`~pybitwuzla.Bitwuzla.check_sat` call as assertions.

           .. seealso::
                :func:`~pybitwuzla.Bitwuzla.assume_formula`.
        """
        bitwuzla_api.bitwuzla_fixate_assumptions(self.ptr())

    def reset_assumptions(self):
        """Remove all assumptions added since the last
           :func:`~pybitwuzla.Bitwuzla.check_sat` call.

           .. seealso::
                :func:`~pybitwuzla.Bitwuzla.assume_formula`.
        """
        bitwuzla_api.bitwuzla_reset_assumptions(self.ptr())

    def get_unsat_assumptions(self):
        """Return list of unsatisfiable assumptions previously added via
           :func:`~pybitwuzla.Bitwuzla.assume_formula`.

           Requires that the last :func:`~pybitwuzla.Bitwuzla.check_sat` call
           returned `~pybitwuzla.Result.UNSAT`.

           :return:  List of unsatisfiable assumptions
           :rtype:   list(BitwuzlaTerm)
        """
        cdef const bitwuzla_api.BitwuzlaTerm** assumptions
        cdef size_t size
        assumptions = \
            bitwuzla_api.bitwuzla_get_unsat_assumptions(self.ptr(), &size)

        return _to_terms(self, size, assumptions)


    # ------------------------------------------------------------------------
    # Options

    def set_option(self, opt, value):
        """set_option(opt, value)

           Set option ``opt`` to ``value``.

           :param opt:   Option.
           :type opt:    BitwuzlaOption
           :param value: Option value.

           .. seealso::
                For a list of available options see :class:`~pybitwuzla.Option`
        """
        if not isinstance(opt, Option):
            raise ValueError("Given 'opt' is not an option object")
        if isinstance(value, str):
            bitwuzla_api.bitwuzla_set_option_str(
                    self.ptr(), opt.value, _to_cstr(value))
        else:
            bitwuzla_api.bitwuzla_set_option(self.ptr(), opt.value, value)

    def get_option(self, opt):
        """get_option(opt)

           Get the current value of option ``opt``.

           :param opt: Option.
           :type opt: BitwuzlaOption
           :return: Option value.

           .. seealso::
                For a list of available options see :class:`~pybitwuzla.Option`
        """
        if not isinstance(opt, Option):
            raise ValueError("Given 'opt' is not an option object")
        cdef bitwuzla_api.BitwuzlaOptionInfo info
        bitwuzla_api.bitwuzla_get_option_info(self.ptr(), opt.value, &info)
        if info.is_numeric:
            return info.numeric.cur_val
        return _to_str(info.string.cur_val)

    # ------------------------------------------------------------------------
    # Sort methods

    def mk_bool_sort(self):
        """Create a Boolean sort.

           :return: Sort of type Boolean.
           :rtype: BitwuzlaSort
        """
        return _to_sort(self, bitwuzla_api.bitwuzla_mk_bool_sort(self.ptr()))

    def mk_bv_sort(self, uint32_t width):
        """mk_bv_sort(width)

           Create bit-vector sort of size ``width``.

           :param width: Bit width.
           :type width: uint32_t

           :return:  Bit-vector sort of bit width ``width``.
           :rtype: pybitwuzla.BitwuzlaSort
        """
        return _to_sort(self,
                        bitwuzla_api.bitwuzla_mk_bv_sort(self.ptr(), width))

    def mk_array_sort(self, BitwuzlaSort index, BitwuzlaSort elem):
        """mk_array_sort(index, elem)

           Create array sort with given index and element sorts.

           :param index: The sort of the array index.
           :type index: BitwuzlaSort
           :param elem: The sort of the array elements.
           :type elem: BitwuzlaSort

           :return:  Array sort.
           :rtype: BitwuzlaSort
          """
        return _to_sort(self,
                        bitwuzla_api.bitwuzla_mk_array_sort(self.ptr(),
                                                            index.ptr(),
                                                            elem.ptr()))

    def mk_fun_sort(self, list domain, BitwuzlaSort codomain):
        """mk_fun_sort(domain, codomain)

           Create function sort with given domain and codomain.

           :param domain: A list of all the function arguments' sorts.
           :type domain: list
           :param codomain: The sort of the function's return value.
           :type codomain: BitwuzlaSort

           :return:  Function sort, which maps ``domain`` to ``codomain``.
           :rtype: BitwuzlaSort
          """
        cdef uint32_t arity = len(domain)
        cdef const bitwuzla_api.BitwuzlaSort **c_domain = \
                _alloc_sorts_const(arity)
        for i in range(arity):
            if not isinstance(domain[i], BitwuzlaSort):
                raise ValueError('Argument at position {} ' \
                                 'is not of type BitwuzlaSort'.format(i))
            c_domain[i] = (<BitwuzlaSort> domain[i]).ptr()

        sort = _to_sort(self,
                        bitwuzla_api.bitwuzla_mk_fun_sort(self.ptr(),
                                                          arity,
                                                          c_domain,
                                                          codomain.ptr()))
        free(c_domain)
        return sort

    def mk_fp_sort(self, uint32_t exp_size, uint32_t sig_size):
        """mk_fp_sort(exp_size, sig_size)

           Create a floating-point sort with given exponent size ``exp_size``
           and significand size ``sig_size``.

           :param exp_size: Exponent size.
           :type exp_size: uint32_t
           :param sig_size: Significand size.
           :type sig_size: uint32_t

           :return: Floating-point sort.
           :rtype: BitwuzlaSort
        """
        return _to_sort(self,
                        bitwuzla_api.bitwuzla_mk_fp_sort(self.ptr(),
                                                         exp_size, sig_size))

    def mk_rm_sort(self):
        """mk_rm_sort()

           Create a rounding mode sort.

           :return: Rounding mode sort.
           :rtype: BitwuzlaSort
        """
        return _to_sort(self, bitwuzla_api.bitwuzla_mk_rm_sort(self.ptr()))

    # ------------------------------------------------------------------------
    # Value methods

    # Bit-vector values

    def mk_bv_value(self, BitwuzlaSort sort, value):
        """mk_bv_value(sort, value)

           Create bit-vector ``value`` with given ``sort``.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort
           :param value: Hexadecimal, binary or decimal value.

                         - hexadecimal prefix: ``0x`` or ``#x``
                         - binary prefix: ``0b`` or ``#b``
           :type value: str or int

           :return: A term representing the bit-vector value.
           :rtype: BitwuzlaTerm
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
        """mk_bv_ones(sort)

           Create a bit-vector value with ``sort`` where all bits are set to 1.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where all bits are set to 1.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self, bitwuzla_api.bitwuzla_mk_bv_ones(self.ptr(),
                                                               sort.ptr()))

    def mk_bv_min_signed(self, BitwuzlaSort sort):
        """mk_bv_min_signed(sort)

           Create a bit-vector minimum signed value.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where the MSB is set to 1 and all remaining bits are set to
                    0.
           :rtype: BitwuzlaTerm

        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_bv_min_signed(self.ptr(),
                                                               sort.ptr()))

    def mk_bv_max_signed(self, BitwuzlaSort sort):
        """mk_bv_max_signed(sort)

           Create a bit-vector maximum signed value.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where the MSB is set to 0 and all remaining bits are set to
                    1.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_bv_max_signed(self.ptr(),
                                                               sort.ptr()))

    # Floating-point values

    def mk_fp_value(self, BitwuzlaSort sort, sign, exponent, significand):
        """mk_fp_value(sort, sign, exponent, significand)

           Create a floating-point value from its IEEE 754 standard
           representation given as three bit-vector values representing the
           sign bit, the exponent and the significand.

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort
           :param sign: The sign bit.
           :type sign: str or int
           :param exponent: The exponent bit-vector value.
           :type exponent: str or int
           :param significand: The significand bit-vector value.
           :type significand: str or int

           :return: A term representing the floating-point value.
           :rtype: BitwuzlaTerm

           .. seealso::
             :func:`~pybitwuzla.Bitwuzla.mk_bv_value` for the supported value
             format for ``sign``, ``exponent``, and ``significand``.
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

        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_value(
                            self.ptr(),
                            val_sign.ptr(),
                            val_exp.ptr(),
                            val_significand.ptr()))

    def mk_fp_value_from(self, BitwuzlaSort sort, BitwuzlaTerm rm, value):
        """mk_fp_value_from(sort, rm, value)

           Create a floating-point value from its real or rational
           representation, given as a string, with respect to given
           rounding mode.

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort
           :param rm: Rounding mode.
           :type rm: BitwuzlaTerm
           :param value: String representation of real or rational value to
                         create. The expected format for rational values is
                         <numerator>/<denominator>.
           :type value: str

           :return: A term representing the real or rational value as floating
                    point value with given sort.
           :rtype: BitwuzlaTerm
        """
        term = BitwuzlaTerm(self)
        if isinstance(value, str) and '/' in value:
            num, den = value.split('/')
            return _to_term(self,
                            bitwuzla_api.bitwuzla_mk_fp_value_from_rational(
                                self.ptr(),
                                sort.ptr(),
                                rm.ptr(),
                                _to_cstr(num),
                                _to_cstr(den)))

        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_value_from_real(
                            self.ptr(),
                            sort.ptr(),
                            rm.ptr(),
                            _to_cstr(str(value))))


    def mk_fp_pos_zero(self, BitwuzlaSort sort):
        """mk_fp_pos_zero(sort)

           Create a floating-point positive zero value (SMT-LIB: `+zero`).

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort

           :return: A term representing the floating-point positive zero value
                    of given floating-point sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_pos_zero(self.ptr(),
                                                             sort.ptr()))

    def mk_fp_neg_zero(self, BitwuzlaSort sort):
        """mk_fp_neg_zero(sort)

           Create a floating-point negative zero value (SMT-LIB: `-zero`).

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort

           :return: A term representing the floating-point negative zero value
                    of given floating-point sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_neg_zero(self.ptr(),
                                                             sort.ptr()))

    def mk_fp_pos_inf(self, BitwuzlaSort sort):
        """mk_fp_pos_inf(sort)

           Create a floating-point positive infinity value (SMT-LIB: `+oo`).

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort

           :return: A term representing the floating-point positive infinity
                    value of given floating-point sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_pos_inf(self.ptr(),
                                                            sort.ptr()))

    def mk_fp_neg_inf(self, BitwuzlaSort sort):
        """mk_fp_neg_inf(sort)

           Create a floating-point negative infinity value (SMT-LIB: `-oo`).

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort

           :return: A term representing the floating-point negative infinity
                    value of given floating-point sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_fp_neg_inf(self.ptr(),
                                                            sort.ptr()))

    def mk_fp_nan(self, BitwuzlaSort sort):
        """mk_fp_nan(sort)

           Create a floating-point NaN value.

           :param sort: Floating-point sort.
           :type sort: BitwuzlaSort

           :return: A term representing the floating-point NaN value of given
                    floating-point sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self, bitwuzla_api.bitwuzla_mk_fp_nan(self.ptr(),
                                                              sort.ptr()))

    def mk_rm_value(self, rm):
        """mk_rm_value(rm)

           Create a rounding mode value.

           :param rm: Rounding mode.
           :type rm: RoundingMode

           :return: A term representing the rounding mode value.
           :rtype: BitwuzlaTerm
        """
        if not isinstance(rm, RoundingMode):
            raise ValueError("Given 'rm' is not a RoundingMode value")
        return _to_term(self, bitwuzla_api.bitwuzla_mk_rm_value(self.ptr(),
                                                                rm.value))


    # ------------------------------------------------------------------------
    # Term methods

    def mk_const(self, BitwuzlaSort sort, str symbol = None):
        """mk_const(sort, symbol = None)

           Create a (first-order) constant of given ``sort`` with ``symbol``.

           :param sort: The sort of the constant.
           :type sort: BitwuzlaSort
           :param symbol: The symbol of the constant.
           :type symbol: str

           :return: A term representing the constant.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_const(self.ptr(),
                                                       sort.ptr(),
                                                       _to_cstr(symbol)))

    def mk_const_array(self, BitwuzlaSort sort, BitwuzlaTerm value):
        """mk_const_array(sort, value)

           Create a one-dimensional constant array of given sort, initialized
           with given value.

           :param sort: The sort of the array.
           :type sort: BitwuzlaSort
           :param value: The term to initialize the elements of the array with.
           :type value: BitwuzlaTerm

           :return: A term representing a constant array of given sort.
           :rtype: BitwuzlaTerm
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_const_array(self.ptr(),
                                                             sort.ptr(),
                                                             value.ptr()))

    def mk_var(self, BitwuzlaSort sort, str symbol = None):
        """mk_var(sort, symbol = None)

           Create a variable of given ``sort`` with ``symbol``.

           :param sort: The sort of the variable.
           :type sort: BitwuzlaSort
           :param symbol: The symbol of the variable.
           :type symbol: str

           :return: A term representing the variable.
           :rtype: BitwuzlaTerm

           .. note::
                This creates a variable to be bound by terms of kind
                :class:`~pybitwuzla.Kind.LAMBDA`.
        """
        return _to_term(self,
                        bitwuzla_api.bitwuzla_mk_var(self.ptr(),
                                                     sort.ptr(),
                                                     _to_cstr(symbol)))

    def mk_term(self, kind, terms, indices = None):
        """mk_term(kind, terms, indices = None)

           Create a term of given kind with the given argument terms.

           :param kind: The operator kind.
           :type kind: Kind
           :param terms: The number of argument terms.
           :type terms: list(BitwuzlaTerm)
           :param indices: The argument terms.
           :type indices: list(int)

           :return: A term representing an operation of given kind.
           :rtype: BitwuzlaTerm
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
        cdef const bitwuzla_api.BitwuzlaTerm **c_terms =\
                _alloc_terms_const(num_terms)

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


    def substitute(self, terms, dict subst_map):
        """substitute(terms, subst_map)

           Substitute constants or variables in ``terms`` by applying
           substitutions in ``subst_map``.

           :param terms: List of terms to apply substitutions.
           :type terms: list(BitwuzlaTerm)
           :param subst_map: The substitution map mapping constants or
                             variables to terms.
           :type subst_map: dict(BitwuzlaTerm,BitwuzlaTerm)

           :return: List of terms with substitutions applied.
           :rtype: list(BitwuzlaTerm)
        """
        if not isinstance(terms, BitwuzlaTerm) and not isinstance(terms, list):
            raise ValueError('Expected BitwuzlaTerm or list of ' \
                             'BitwuzlaTerm but got {}'.format(type(terms)))
        got_term = False
        if isinstance(terms, BitwuzlaTerm):
            got_term = True
            terms = [terms]

        num_terms = len(terms)
        size_map = len(subst_map)
        cdef const bitwuzla_api.BitwuzlaTerm **c_terms = _alloc_terms(num_terms)
        cdef const bitwuzla_api.BitwuzlaTerm **c_keys = \
                _alloc_terms_const(size_map)
        cdef const bitwuzla_api.BitwuzlaTerm **c_values = \
                _alloc_terms_const(size_map)

        for i in range(num_terms):
            if not isinstance(terms[i], BitwuzlaTerm):
                raise ValueError('Expected BitwuzlaTerm but got {}'.format(
                                    type(terms[i])))
            c_terms[i] = (<BitwuzlaTerm> terms[i]).ptr()

        i = 0
        for k, v in subst_map.items():
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
            return _to_term(self, c_terms[0])
        return _to_terms(self, num_terms, c_terms)
