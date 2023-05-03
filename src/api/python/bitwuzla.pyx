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
from libc.stdint cimport uint8_t, int32_t, uint32_t, uint64_t
from libcpp cimport bool as cbool
from libcpp.vector cimport vector
from libcpp.optional cimport optional, nullopt, make_optional
from libcpp.string cimport string
from libcpp.memory cimport unique_ptr
from cpython.ref cimport PyObject
from cpython cimport array
from collections import defaultdict
import array
import math, os, sys
import tempfile

include "enums.pxd"
include "options.pxd"

class BitwuzlaException(Exception):
    """Bitwuzla exception class."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return "[bitwuzla] {}".format(self.msg)

# --------------------------------------------------------------------------- #
# Utility functions
# --------------------------------------------------------------------------- #

cdef str _to_str(const char *string):
    if string is NULL:
        return None
    cdef bytes py_str = string
    return str(py_str.decode())

cdef Term _term(term: bitwuzla_api.Term):
    t = Term()
    t.c_term = term
    return t

cdef bitwuzla_api.Term _cterm(term: Term):
    return term.c_term

cdef list[Term] _terms(vector[bitwuzla_api.Term]& c_terms):
    terms = []
    for t in c_terms:
        terms.append(_term(t))
    return terms

cdef Sort _sort(sort: bitwuzla_api.Sort):
    s = Sort()
    s.c_sort = sort
    return s

cdef bitwuzla_api.Sort _csort(sort: Sort):
    return sort.c_sort

cdef vector[bitwuzla_api.Sort] _sort_vec(list sorts):
    cdef vector[bitwuzla_api.Sort] vec
    for s in sorts:
        vec.push_back(_csort(s))
    return vec

cdef vector[bitwuzla_api.Term] _term_vec(terms):
    cdef vector[bitwuzla_api.Term] vec
    for t in terms:
        vec.push_back(_cterm(t))
    return vec

cdef list[Term] _term_list(vector[bitwuzla_api.Term] terms):
    return [_term(t) for t in terms]

cdef vector[string] _to_str_vec(strs):
    cdef vector[string] vec
    for s in strs:
        vec.push_back(str(s).encode())
    return vec

def _check_arg(arg, _type):
    if not isinstance(arg, _type):
        raise ValueError(
                f'Expected type {str(_type)} for argument, but got {type(arg)}')

# -------------------------------------------------------------------------- #

# -------------------------------------------------------------------------- #
# Library info                                                               #
# -------------------------------------------------------------------------- #

def copyright() -> str:
    """:return: The copyright information.
       :rtype: str
    """
    return bitwuzla_api.copyright().decode()

def version() -> str:
    """:return: The version number.
       :rtype: str
    """
    return bitwuzla_api.version().decode()

def git_id() -> str:
    """:return: The git commit sha.
       :rtype: str
    """
    return bitwuzla_api.git_id().decode()

# --------------------------------------------------------------------------- #
# Sort wrapper
# --------------------------------------------------------------------------- #

cdef class Sort:
    cdef bitwuzla_api.Sort c_sort

    def is_null(self) -> bool:
        return self.c_sort.is_null()

    def id(self) -> int:
        return self.c_sort.id()

    def bv_size(self) -> int:
        return self.c_sort.bv_size()

    def fp_exp_size(self) -> int:
        return self.c_sort.fp_exp_size()

    def fp_sig_size(self) -> int:
        return self.c_sort.fp_sig_size()

    def array_index(self) -> Sort:
        return _sort(self.c_sort.array_index())

    def array_element(self) -> Sort:
        return _sort(self.c_sort.array_element())

    def fun_domain(self) -> list[Sort]:
        return [_sort(s) for s in self.c_sort.fun_domain()]

    def fun_codomain(self) -> Sort:
        return _sort(self.c_sort.fun_codomain())

    def fun_arity(self) -> int:
        return self.c_sort.fun_arity()

    def uninterpreted_symbol(self) -> str:
        symbol = self.c_sort.uninterpreted_symbol()
        return symbol.value().decode() if symbol.has_value() else None

    def is_array(self) -> bool:
        return self.c_sort.is_array()

    def is_bool(self) -> bool:
        return self.c_sort.is_bool()

    def is_bv(self) -> bool:
        return self.c_sort.is_bv()

    def is_fp(self) -> bool:
        return self.c_sort.is_fp()

    def is_fun(self) -> bool:
        return self.c_sort.is_fun()

    def is_rm(self) -> bool:
        return self.c_sort.is_rm()

    def is_uninterpreted(self) -> bool:
        return self.c_sort.is_uninterpreted()

    def __str__(self) -> str:
        return self.c_sort.str().decode()

    def __eq__(self, Sort other) -> bool:
        return self.c_sort == other.c_sort


# --------------------------------------------------------------------------- #
# Term wrapper
# --------------------------------------------------------------------------- #

cdef class Term:
    cdef bitwuzla_api.Term c_term

    def is_null(self) -> bool:
        return self.c_term.is_null()

    def id(self) -> int:
        return self.c_term.id()

    def kind(self) -> Kind:
        return self.c_term.kind()

    def sort(self) -> Sort:
        return _sort(self.c_term.sort())

    def num_children(self) -> int:
        return self.c_term.num_children()

    def children(self) -> list[Term]:
        return _terms(self.c_term.children())

    def __getitem__(self, uint64_t index) -> Term:
        return _term(self.c_term[index])

    def num_indices(self) -> int:
        return self.c_term.num_indices()

    def indices(self) -> list[int]:
        return [i for i in self.c_term.indices()]

    def symbol(self) -> str:
        opt = self.c_term.symbol()
        if opt.has_value():
            return (<string?> opt.value()).decode()
        return None

    def is_const(self) -> bool:
        return self.c_term.is_const()

    def is_variable(self) -> bool:
        return self.c_term.is_variable()

    def is_value(self) -> bool:
        return self.c_term.is_value()

    def is_bv_value_zero(self) -> bool:
        return self.c_term.is_bv_value_zero()

    def is_bv_value_one(self) -> bool:
        return self.c_term.is_bv_value_one()

    def is_bv_value_ones(self) -> bool:
        return self.c_term.is_bv_value_ones()

    def is_bv_value_min_signed(self) -> bool:
        return self.c_term.is_bv_value_min_signed()

    def is_bv_value_max_signed(self) -> bool:
        return self.c_term.is_bv_value_max_signed()

    def is_fp_value_pos_zero(self) -> bool:
        return self.c_term.is_fp_value_pos_zero()

    def is_fp_value_neg_zero(self) -> bool:
        return self.c_term.is_fp_value_neg_zero()

    def is_fp_value_pos_inf(self) -> bool:
        return self.c_term.is_fp_value_pos_inf()

    def is_fp_value_neg_inf(self) -> bool:
        return self.c_term.is_fp_value_neg_inf()

    def is_fp_value_nan(self) -> bool:
        return self.c_term.is_fp_value_nan()

    def is_rm_value_rna(self) -> bool:
        return self.c_term.is_rm_value_rna()

    def is_rm_value_rne(self) -> bool:
        return self.c_term.is_rm_value_rne()

    def is_rm_value_rtn(self) -> bool:
        return self.c_term.is_rm_value_rtn()

    def is_rm_value_rtp(self) -> bool:
        return self.c_term.is_rm_value_rtp()

    def is_rm_value_rtz(self) -> bool:
        return self.c_term.is_rm_value_rtz()

    def __str__(self) -> str:
        return self.c_term.str().decode()

    def value(self, uint8_t base = 2):
        sort = self.sort()
        if sort.is_bool():
            return self.c_term.value[cbool]()
        elif sort.is_rm():
            return RoundingMode(self.c_term.value[bitwuzla_api.RoundingMode]())
        return self.c_term.value[string](base).decode()


# --------------------------------------------------------------------------- #
# Options wrapper
# --------------------------------------------------------------------------- #

cdef class Options:
    cdef bitwuzla_api.Options c_options

    def shrt(self, option: Option) -> str:
        return self.c_options.shrt(option.value).decode()

    def lng(self, option: Option) -> str:
        return self.c_options.lng(option.value).decode()

    def description(self, option: Option) -> str:
        return self.c_options.description(option.value).decode()

    def modes(self, option: Option) -> list[str]:
        return [m.decode() for m in self.c_options.modes(option.value)]

    def set(self, option: Option, value):
        cdef bitwuzla_api.Option opt = option.value
        if isinstance(value, str):
            self.c_options.set(opt, <const string&> value.encode())
        elif isinstance(value, bool) or isinstance(value, int):
            self.c_options.set(opt, <uint64_t?> value)
        else:
            raise ValueError(f'Invalid value type for option {option.value}.')

    def set_args(self, *args: str):
        self.c_options.set(_to_str_vec(args))

    def option(self, name: str) -> Option:
        return Option(self.c_options.option(name))

    def get(self, option: Option):
        if self.c_options.is_mode(option.value):
            return self.c_options.get_mode(option.value).decode()
        elif self.c_options.is_numeric(option.value):
            return self.c_options.get(option.value)
        elif self.c_options.is_bool(option.value):
            return self.c_options.get(option.value) != 0

# --------------------------------------------------------------------------- #
# OptionInfo wrapper
# --------------------------------------------------------------------------- #

# TODO

# --------------------------------------------------------------------------- #
# Bitwuzla wrapper
# --------------------------------------------------------------------------- #

cdef class Bitwuzla:
    cdef unique_ptr[bitwuzla_api.Bitwuzla] c_bitwuzla
    cdef unique_ptr[bitwuzla_api.PyTerminator] c_terminator

    def __init__(self, options: Options):
        self.c_bitwuzla.reset(new bitwuzla_api.Bitwuzla(options.c_options))

    def configure_terminator(self, callback: callable):
        """Set a termination callback.

           Use this function to force Bitwuzla to prematurely terminate if
           callback returns True. The callback object needs to be a callable,
           i.e., it is a function or class that implements the builtin method
           __call__().

           For example: ::

             import time
             class TimeLimitTerminator:
                def __init__(self, time_limit):
                    self.start_time = time.time()
                    self.time_limit = time_limit

                def __call__(self)
                    # Terminate after self.time_limit seconds passed
                    return time.time() - self.start_time > self.time_limit

             bitwuzla = Bitwuzla()
             bitwuzla.set_term(lambda: True)            # immediately terminate
             bitwuzla.set_term(TimeLimitTerminator(1))  # terminate after 1s
             bitwuzla.set_term(TimeLimitTerminator(10)) # terminate after 10s

           :param callback: A callable Python object.
        """
        self.c_terminator.reset(
            new bitwuzla_api.PyTerminator(<PyObject*> callback))
        self.c_bitwuzla.get().configure_terminator(
            <bitwuzla_api.Terminator*> self.c_terminator.get())

    def push(self, nlevels: uint32_t = 1):
        """Push new assertion levels.

           :param levels: Number of assertion levels to create.
           :type levels: int
        """
        self.c_bitwuzla.get().push(nlevels)

    def pop(self, nlevels: uint32_t = 1):
        """Pop assertion levels.

           :param levels: Number of assertion levels to pop.
           :type levels: int
        """
        self.c_bitwuzla.get().pop(nlevels)

    def assert_formula(self, *formulas: Term):
        """Assert one or more formulas.

           :param formulas: One or more Boolean terms.
        """
        for f in formulas:
            self.c_bitwuzla.get().assert_formula(_cterm(f))

    def check_sat(self, *assumptions: Term) -> Result:
        """Check satisfiability of asserted formulas under possibly given
           assumptions.

           :param assumptions: Zero or more Boolean terms.

           :return: - :class:`~bitwuzla.Result.SAT` if the input formula is
                      satisfiable (under possibly given assumptions)
                    - :class:`~bitwuzla.Result.UNSAT` if it is unsatisfiable
                    - :class:`~bitwuzla.Result.UNKNOWN` otherwise

           .. seealso::
               :func:`~bitwuzla.Bitwuzla.assert_formula`,
               :func:`~bitwuzla.Bitwuzla.get_value`,
               :func:`~bitwuzla.Bitwuzla.get_unsat_core`,
               :func:`~bitwuzla.Bitwuzla.get_unsat_assumptions`,
        """
        return Result(self.c_bitwuzla.get().check_sat(_term_vec(assumptions)))

    def is_unsat_assumption(self, Term term) -> bool:
        """Determine if given assumption is unsat.

           Unsat assumptions are those assumptions that force an
           input formula to become unsatisfiable.

           See :func:`~bitwuzla.Bitwuzla.check_sat`.

           :param term: Boolean term.
           :return:  True if assumption is unsat, False otherwise.
        """
        return self.c_bitwuzla.get().is_unsat_assumption(_cterm(term))

    def get_unsat_assumptions(self) -> list[Term]:
        """Return list of unsatisfiable assumptions previously added via
           :func:`~bitwuzla.Bitwuzla.check_sat`.

           Requires that the last :func:`~bitwuzla.Bitwuzla.check_sat` call
           returned `~bitwuzla.Result.UNSAT`.

           :return:  List of unsatisfiable assumptions
        """
        return _term_list(self.c_bitwuzla.get().get_unsat_assumptions())

    def get_unsat_core(self) -> list[Term]:
        """Return list of unsatisfiable assertions previously added via
           :func:`~bitwuzla.Bitwuzla.assert_formula`.

           Requires that the last :func:`~bitwuzla.Bitwuzla.check_sat` call
           returned :class:`~bitwuzla.Result.UNSAT`.

           :return:  list of unsatisfiable assertions
        """
        return _term_list(self.c_bitwuzla.get().get_unsat_core())

    def simplify(self) -> Result:
        """Simplify current set of input assertions.

           :return: - :class:`~bitwuzla.Result.SAT` if the input formula is
                      satisfiable (under possibly given assumptions)
                    - :class:`~bitwuzla.Result.UNSAT` if it is unsatisfiable
                    - :class:`~bitwuzla.Result.UNKNOWN` otherwise

           .. note::
               Each call to :func:`~bitwuzla.Bitwuzla.check_sat`
               simplifies the input formula as a preprocessing step.
        """
        return Result(self.c_bitwuzla.get().simplify())

    def get_value(self, term: Term) -> Term:
        """Get model value of term.

           Requires that the last :func:`~bitwuzla.Bitwuzla.check_sat` call
           returned `~bitwuzla.Result.SAT`.

           :return: Term representing the model value of `term`.
        """
        return _term(self.c_bitwuzla.get().get_value(_cterm(term)))

# --------------------------------------------------------------------------- #
# Sort functions
# --------------------------------------------------------------------------- #

def mk_bool_sort() -> Sort:
    """Create a Boolean sort.

       :return: Sort of type Boolean.
    """
    return _sort(bitwuzla_api.mk_bool_sort())

def mk_bv_sort(size: uint64_t) -> Sort:
    """Create bit-vector sort of size ``size``.

       :param size: Bit width.
       :return:  Bit-vector sort of size ``size``.
    """
    return _sort(bitwuzla_api.mk_bv_sort(size))

def mk_array_sort(index: Sort, elem: Sort) -> Sort:
    """Create array sort with given index and element sorts.

       :param index: The sort of the array index.
       :param elem: The sort of the array elements.
       :return:  Array sort.
      """
    return _sort(bitwuzla_api.mk_array_sort(index.c_sort, elem.c_sort))

def mk_fun_sort(domain: list[Sort], codomain: Sort) -> Sort:
    """Create function sort with given domain and codomain.

       :param domain: A list of all the function arguments' sorts.
       :param codomain: The sort of the function's return value.
       :return:  Function sort, which maps ``domain`` to ``codomain``.
      """
    return _sort(bitwuzla_api.mk_fun_sort(_sort_vec(domain), _csort(codomain)))

def mk_fp_sort(exp_size: uint64_t, sig_size: uint64_t) -> Sort:
    """Create a floating-point sort with given exponent size ``exp_size``
       and significand size ``sig_size``.

       :param exp_size: Exponent size.
       :param sig_size: Significand size.
       :return: Floating-point sort.
    """
    return _sort(bitwuzla_api.mk_fp_sort(exp_size, sig_size))

def mk_rm_sort() -> Sort:
    """Create a rounding mode sort.

       :return: Rounding mode sort.
    """
    return _sort(bitwuzla_api.mk_rm_sort())

def mk_uninterpreted_sort(symbol: str = None) -> Sort:
    """Create an uninterpreted sort.

       :param symbol: The symbol of the sort.
       :return: Uninterpreted Sort.

       .. note::
            Only 0-arity uninterpreted sorts are supported.
    """
    cdef optional[string] opt = nullopt
    if symbol:
        opt = <string?> symbol.encode()
    return _sort(bitwuzla_api.mk_uninterpreted_sort(<optional[const string]?> opt))


# --------------------------------------------------------------------------- #
# Value functions
# --------------------------------------------------------------------------- #

def mk_true() -> Term:
    """mk_true()

    Create true value.

    :return: A term representing true.
    :rtype: BitwuzlaTerm
    """
    return _term(bitwuzla_api.mk_true())

def mk_false() -> Term:
    """mk_false()

    Create false value.

    :return: A term representing false.
    :rtype: BitwuzlaTerm
    """
    return _term(bitwuzla_api.mk_false())

def mk_bv_value(sort: Sort, value) -> Term:
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
    base = None
    is_str = isinstance(value, str)
    if is_str and (value.startswith('0x') or value.startswith('#x')):
        base = 16
    elif is_str and (value.startswith('0b') or value.startswith('#b')):
        base = 2
    elif (is_str and value.lstrip('-').isnumeric()) or isinstance(value, int):
        base = 10
        value = str(value)

    if base is None:
        raise ValueError("Cannot convert '{}' to " \
                         "bit-vector value.".format(value))

    return _term(bitwuzla_api.mk_bv_value(sort.c_sort, value.encode(), base))

def mk_bv_ones(sort: Sort) -> Term:
    """mk_bv_ones(sort)

       Create a bit-vector value with ``sort`` where all bits are set to 1.

       :param sort: Bit-vector sort.
       :type sort: BitwuzlaSort

       :return: A term representing the bit-vector value of given sort
                where all bits are set to 1.
       :rtype: BitwuzlaTerm
    """
    return _term(bitwuzla_api.mk_bv_ones(sort.c_sort))

def mk_bv_min_signed(sort: Sort) -> Term:
    """mk_bv_min_signed(sort)

       Create a bit-vector minimum signed value.

       :param sort: Bit-vector sort.
       :type sort: BitwuzlaSort

       :return: A term representing the bit-vector value of given sort
                where the MSB is set to 1 and all remaining bits are set to
                0.
       :rtype: BitwuzlaTerm

    """
    return _term(bitwuzla_api.mk_bv_min_signed(sort.c_sort))

def mk_bv_max_signed(sort: Sort) -> Term:
    """mk_bv_max_signed(sort)

       Create a bit-vector maximum signed value.

       :param sort: Bit-vector sort.
       :type sort: BitwuzlaSort

       :return: A term representing the bit-vector value of given sort
                where the MSB is set to 0 and all remaining bits are set to
                1.
       :rtype: BitwuzlaTerm
    """
    return _term(bitwuzla_api.mk_bv_max_signed(sort.c_sort))

def mk_fp_value(*args) -> Term:
    """mk_fp_value(sign: Term, exponent: Term, significand: Term) -> Term
       mk_fp_value(sort: Sort, rm: Term, real: str) -> Term
       mk_fp_value(sort: Sort, rm: Term, num: str, den: str) -> Term

       Create a floating-point value from its IEEE 754 standard
       representation given as three bit-vector values representing the
       sign bit, the exponent and the significand.

       :param sign: Bit-vector value term representing the sign bit.
       :param exponent: Bit-vector value term representing the exponent.
       :param significand: Bit-vector value term representing the significand.

       Create a floating-point value from its real representation, given as a
       decimal string, with respect to given rounding mode.

       :param sort: Floating-point sort.
       :param rm: Rounding mode term.
       :param real: The decimal string representing a real value

       Create a floating-point value from its rational representation, given as
       a two decimal strings representing the numerator and denominator, with
       respect to given rounding mode.

       :param sort: Floating-point sort.
       :param rm: Rounding mode term.
       :param num: The decimal string representing the numerator.
       :param den: The decimal string representing the denominator.

       :return: A term representing the floating-point value.

       .. seealso::
         :func:`~bitwuzla.Bitwuzla.mk_bv_value` for the supported value
         format for ``sign``, ``exponent``, and ``significand``.
    """
    if isinstance(args[0], Sort):
        _check_arg(args[1], Term)
        _check_arg(args[2], str)
        if len(args) == 4:
            _check_arg(args[3], str)
            return _term(bitwuzla_api.mk_fp_value(
                            _csort(args[0]),
                            _cterm(args[1]),
                            args[2].encode(),
                            args[3].encode()))
        elif len(args) != 3:
            raise ValueError('Invalid number of arguments')
        return _term(bitwuzla_api.mk_fp_value(
                        _csort(args[0]),
                        _cterm(args[1]),
                        <const string&> args[2].encode()))
    elif isinstance(args[0], Term):
        _check_arg(args[1], Term)
        _check_arg(args[2], Term)
        return _term(bitwuzla_api.mk_fp_value(
                        _cterm(args[0]), _cterm(args[1]), _cterm(args[2])))
    else:
        raise ValueError('Invalid arguments')

def mk_fp_pos_zero(sort: Sort) -> Term:
    """Create a floating-point positive zero value (SMT-LIB: `+zero`).

       :param sort: Floating-point sort.
       :return: A term representing the floating-point positive zero value
                of given floating-point sort.
    """
    return _term(bitwuzla_api.mk_fp_pos_zero(_csort(sort)))

def mk_fp_neg_zero(sort: Sort) -> Term:
    """Create a floating-point negative zero value (SMT-LIB: `-zero`).

       :param sort: Floating-point sort.
       :return: A term representing the floating-point negative zero value
                of given floating-point sort.
    """
    return _term(bitwuzla_api.mk_fp_neg_zero(_csort(sort)))

def mk_fp_pos_inf(sort: Sort) -> Term:
    """Create a floating-point positive infinity value (SMT-LIB: `+oo`).

       :param sort: Floating-point sort.
       :return: A term representing the floating-point positive infinity
                value of given floating-point sort.
    """
    return _term(bitwuzla_api.mk_fp_pos_inf(_csort(sort)))

def mk_fp_neg_inf(sort: Sort) -> Term:
    """Create a floating-point negative infinity value (SMT-LIB: `-oo`).

       :param sort: Floating-point sort.
       :return: A term representing the floating-point negative infinity
                value of given floating-point sort.
    """
    return _term(bitwuzla_api.mk_fp_neg_inf(_csort(sort)))

def mk_fp_nan(sort: Sort) -> Term:
    """Create a floating-point NaN value.

       :param sort: Floating-point sort.
       :return: A term representing the floating-point NaN value of given
                floating-point sort.
    """
    return _term(bitwuzla_api.mk_fp_nan(_csort(sort)))

def mk_rm_value(rm: RoundingMode) -> Term:
    """Create a rounding mode value.

       :param rm: Rounding mode.
       :return: A term representing the rounding mode value.
    """
    return _term(bitwuzla_api.mk_rm_value(rm.value))


# --------------------------------------------------------------------------- #
# Term functions
# --------------------------------------------------------------------------- #

def mk_const(sort: Sort, symbol: str = None) -> Term:
    """Create a (first-order) constant of given sort with given symbol.

       :param sort: The sort of the constant.
       :param symbol: The symbol of the constant.
       :return: A term of kind :class:`~bitwuzla.Kind.CONSTANT`,
                representing the constant.
    """
    cdef optional[string] opt = nullopt
    if symbol:
        opt = <string?> symbol.encode()
    return _term(bitwuzla_api.mk_const(_csort(sort), <optional[const string]?> opt))

def mk_const_array(sort: Sort, term: Term) -> Term:
    """Create a one-dimensional constant array of given sort, initialized with
       given value.

       :param sort: The sort of the array.
       :param term: The term to initialize the elements of the array with.
       :return: A term of kind :class:`~bitwuzla.Kind.CONST_ARRAY`,
                representing a constant array of given sort.
    """
    return _term(bitwuzla_api.mk_const_array(_csort(sort), _cterm(term)))

def mk_var(sort: Sort, symbol: str = None) -> Term:
    """Create a (first-order) variable of given sort with given symbol.

       :param sort: The sort of the variable.
       :param symbol: The symbol of the variable.
       :return: A term of kind :class:`~bitwuzla.Kind.VARIABLE`,
                representing the variable.
    """
    cdef optional[string] opt = nullopt
    if symbol:
        opt = <string?> symbol.encode()
    return _term(bitwuzla_api.mk_var(_csort(sort), <optional[const string]?> opt))

def mk_term(kind: Kind, terms: list[Term], indices: list[int] = []) -> Term:
    """Create a term of given kind with the given argument terms.

       :param kind: The operator kind.
       :param terms: The argument terms.
       :param indices: The indices of this term, empty if not indexed.
       :return: A term representing an operation of given kind.
    """
    return _term(bitwuzla_api.mk_term(kind.value, _term_vec(terms), indices))

