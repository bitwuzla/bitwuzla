###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2020 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

"""
The Python API of the SMT solver Bitwuzla.
"""

cimport bitwuzla_api
from libc.stdint cimport uint8_t, int32_t, uint32_t, uint64_t
from libcpp cimport bool as c_bool
from libcpp.optional cimport optional, nullopt, make_optional
from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map
from libcpp.vector cimport vector
from libcpp.memory cimport unique_ptr, shared_ptr
from cpython.ref cimport PyObject
from cython.operator import dereference
import cython

include "enums.pxd"
include "options.pxd"

# -------------------------------------------------------------------------- #

class BitwuzlaException(Exception):
    """Bitwuzla exception class."""
    def __init__(self, msg):
        self.msg = msg

    def __str__(self):
        return self.msg

# --------------------------------------------------------------------------- #
# Utility functions
# --------------------------------------------------------------------------- #

cdef str _to_str(const char *string):
    if string is NULL:
        return None
    cdef bytes py_str = string
    return str(py_str.decode())

cdef Term _term(tm: TermManager, term: bitwuzla_api.Term):
    t = Term()
    t.c_term = term
    t.tm = tm
    return t

cdef bitwuzla_api.Term _cterm(term: Term):
    return term.c_term

cdef list[Term] _terms(tm: TermManager, vector[bitwuzla_api.Term]& c_terms):
    return [_term(tm, t) for t in c_terms]

cdef vector[bitwuzla_api.Term] _term_vec(terms):
    cdef vector[bitwuzla_api.Term] vec
    for t in terms:
        vec.push_back(_cterm(t))
    return vec

cdef Sort _sort(tm: TermManager, sort: bitwuzla_api.Sort):
    s = Sort()
    s.c_sort = sort
    s.tm = tm
    return s

cdef list[Sort] _sorts(tm: TermManager, vector[bitwuzla_api.Sort]& c_sorts):
    return [_sort(tm, s) for s in c_sorts]

cdef bitwuzla_api.Sort _csort(sort: Sort):
    return sort.c_sort

cdef vector[bitwuzla_api.Sort] _sort_vec(list sorts):
    cdef vector[bitwuzla_api.Sort] vec
    for s in sorts:
        vec.push_back(_csort(s))
    return vec

def _check_arg(arg, _type):
    if not isinstance(_type, list):
        _type = [_type]

    if not any([isinstance(arg, _t) for _t in _type]):
        raise ValueError(
                f'Expected type {str(_type)} for argument, but got {type(arg)}')

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
    """A Bitwuzla sort."""
    cdef bitwuzla_api.Sort c_sort
    cdef TermManager tm

    def is_null(self) -> bool:
        """Determine if this sort is a null sort.

           :return: True if this sort is a null sort.
        """
        return self.c_sort.is_null()

    def id(self) -> int:
        """Get the id of this sort.

           :return: The sort id.
        """
        return self.c_sort.id()

    def bv_size(self) -> int:
        """Get the size of a bit-vector sort.

           Requires that given sort is a bit-vector sort.

           :return: The size of the bit-vector sort.
        """
        return self.c_sort.bv_size()

    def fp_exp_size(self) -> int:
        """Get the exponent size of a floating-point sort.

           Requires that given sort is a floating-point sort.

           :return: The exponent size of the floating-point sort.
        """
        return self.c_sort.fp_exp_size()

    def fp_sig_size(self) -> int:
        """ Get the significand size of a floating-point sort.

            Requires that given sort is a floating-point sort.

            :return: The significand size of the floating-point sort.
        """
        return self.c_sort.fp_sig_size()

    def array_index(self) -> Sort:
        """Get the index sort of an array sort.

           Requires that given sort is an array sort.

           :return: The index sort of the array sort.
        """
        return _sort(self.tm, self.c_sort.array_index())

    def array_element(self) -> Sort:
        """Get the element sort of an array sort.

           Requires that given sort is an array sort.

           :return: The element sort of the array sort.
        """
        return _sort(self.tm, self.c_sort.array_element())

    def fun_domain(self) -> list[Sort]:
        """Get the domain sorts of a function sort.

           Requires that given sort is a function sort.

           :return: The domain sorts of the function sort.
        """
        return [_sort(self.tm, s) for s in self.c_sort.fun_domain()]

    def fun_codomain(self) -> Sort:
        """Get the codomain sort of a function sort.

           Requires that given sort is a function sort.

           :return: The codomain sort of the function sort.
        """
        return _sort(self.tm, self.c_sort.fun_codomain())

    def fun_arity(self) -> int:
        """Get the arity of a function sort.

           :return: The number of arguments of the function sort.
        """
        return self.c_sort.fun_arity()

    def uninterpreted_symbol(self) -> str:
        """Get the symbol of an uninterpreted sort.

           :return: The symbol.
        """
        symbol = self.c_sort.uninterpreted_symbol()
        return symbol.value().decode() if symbol.has_value() else None

    def is_array(self) -> bool:
        """Determine if this sort is an array sort.

           :return: True if this sort is an array sort.
        """
        return self.c_sort.is_array()

    def is_bool(self) -> bool:
        """Determine if this sort is a Boolean sort.

           :return: True if this sort is a Boolean sort.
        """
        return self.c_sort.is_bool()

    def is_bv(self) -> bool:
        """Determine if this sort is a bit-vector sort.

           :return: True if `sort` is a bit-vector sort.
        """
        return self.c_sort.is_bv()

    def is_fp(self) -> bool:
        """Determine if this sort is a floating-point sort.

           :return: True if this sort is a floating-point sort.
        """
        return self.c_sort.is_fp()

    def is_fun(self) -> bool:
        """Determine if this sort is a function sort.

           :return: True if this sort is a function sort.
        """
        return self.c_sort.is_fun()

    def is_rm(self) -> bool:
        """Determine if this sort is a Roundingmode sort.

           :return: True if this sort is a Roundingmode sort.
        """
        return self.c_sort.is_rm()

    def is_uninterpreted(self) -> bool:
        """Determine if this sort is an uninterpreted sort.

           :return: True if this sort is an uninterpreted sort.
        """
        return self.c_sort.is_uninterpreted()

    def __str__(self) -> str:
        """Get string representation of this sort.

           :return: String representation of this sort.
        """
        return self.c_sort.str().decode()

    def __eq__(self, Sort other) -> bool:
        """Syntactical equality operator.

           :param a: The first sort.
           :param b: The second sort.
           :return: True if the given sorts are equal.
        """
        return self.c_sort == other.c_sort

    def __hash__(self):
        """Hash function for Sort.

           :param sort: The sort.
           :return: The hash value of the sort.
        """
        return self.id()


# --------------------------------------------------------------------------- #
# Term wrapper
# --------------------------------------------------------------------------- #

cdef class Term:
    """A Bitwuzla term."""
    cdef bitwuzla_api.Term c_term
    cdef TermManager tm

    def is_null(self) -> bool:
        """Determine if this term is a null term.

           :return: True if this term is a null term.
        """
        return self.c_term.is_null()

    def id(self) -> int:
        """Get the id of this term.

           :return: The term id.
        """
        return self.c_term.id()

    def kind(self) -> Kind:
        """Get the kind of this term.

           :return: The kind.
        """
        return Kind(self.c_term.kind())

    def sort(self) -> Sort:
        """Get the sort of this term.

           :return: The sort of the term.
        """
        return _sort(self.tm, self.c_term.sort())

    def num_children(self) -> int:
        """Get the number of child terms of this term.

           :return: The number of children of this term.
        """
        return self.c_term.num_children()

    def children(self) -> list[Term]:
        """Get the child terms of this term.

           :return: The children of this term as a vector of terms.
        """
        return _terms(self.tm, self.c_term.children())

    def __getitem__(self, uint64_t index) -> Term:
        """Get child at position `index`.

           :note: Only valid to call if num_children() > 0.

           :param index: The position of the child.
           :return: The child node at position `index`.
        """
        return _term(self.tm, self.c_term[index])

    def num_indices(self) -> int:
        """Get the number of indices of this term.

           :return: The number of indices of this term.
        """
        return self.c_term.num_indices()

    def indices(self) -> list[int]:
        """Get the indices of an indexed term.

           Requires that given term is an indexed term.

           :return: The indices of this term as a vector of indices.
        """
        return [i for i in self.c_term.indices()]

    def symbol(self) -> str:
        """Get the symbol of this term.

           :return: The symbol of this term. `None` if no symbol is defined.
        """
        opt = self.c_term.symbol()
        if opt.has_value():
            return opt.value().get().decode()
        return None

    def is_const(self) -> bool:
        """Determine if this term is a constant.

           :return: True if this term is a constant.
        """
        return self.c_term.is_const()

    def is_variable(self) -> bool:
        """Determine if this term is a variable.

           :return: True if this term is a variable.
        """
        return self.c_term.is_variable()

    def is_value(self) -> bool:
        """Determine if this term is a value.

           :return: True if this term is a value.
        """
        return self.c_term.is_value()

    def is_true(self) -> bool:
        """Determine if this term is Boolean value true.

           :return: True if this term is Boolean value true.
        """
        return self.c_term.is_true()

    def is_false(self) -> bool:
        """Determine if this term is Boolean value false.

           :return: True if this term is Boolean value false.
        """
        return self.c_term.is_false()

    def is_bv_value_zero(self) -> bool:
        """Determine if this term is a bit-vector value representing zero.

           :return: True if this term is a bit-vector zero value.
        """
        return self.c_term.is_bv_value_zero()

    def is_bv_value_one(self) -> bool:
        """Determine if this term is a bit-vector value representing one.

           :return: True if this term is a bit-vector one value.
        """
        return self.c_term.is_bv_value_one()

    def is_bv_value_ones(self) -> bool:
        """Determine if this term is a bit-vector value with all bits set to one.

           :return: True if this term is a bit-vector value with all bits set to one.
        """
        return self.c_term.is_bv_value_ones()

    def is_bv_value_min_signed(self) -> bool:
        """Determine if this term is a bit-vector minimum signed value.

           :return: True if this term is a bit-vector value with the most
                    significant bit set to 1 and all other bits set to 0.
        """
        return self.c_term.is_bv_value_min_signed()

    def is_bv_value_max_signed(self) -> bool:
        """Determine if this term is a bit-vector maximum signed value.

           :return: True if this term is a bit-vector value with the most
                    significant bit set to 0 and all other bits set to 1.
        """
        return self.c_term.is_bv_value_max_signed()

    def is_fp_value_pos_zero(self) -> bool:
        """Determine if this term is a floating-point positive zero (``+zero``)
           value.

           :return: True if this term is a floating-point ``+zero`` value.
        """
        return self.c_term.is_fp_value_pos_zero()

    def is_fp_value_neg_zero(self) -> bool:
        """Determine if this term is a floating-point value negative zero
           (``-zero``).

           :return: True if this term is a floating-point ``-zero``.
        """
        return self.c_term.is_fp_value_neg_zero()

    def is_fp_value_pos_inf(self) -> bool:
        """Determine if this term is a floating-point positive infinity
           (``+oo``) value.

           :return: True if this term is a floating-point ``+oo`` value.
        """
        return self.c_term.is_fp_value_pos_inf()

    def is_fp_value_neg_inf(self) -> bool:
        """Determine if this term is a floating-point negative infinity
           (``-oo``) value.

           :return: True if this term is a floating-point ``-oo`` value.
        """
        return self.c_term.is_fp_value_neg_inf()

    def is_fp_value_nan(self) -> bool:
        """Determine if this term is a floating-point NaN value.

           :return: True if this term is a floating-point NaN value.
        """
        return self.c_term.is_fp_value_nan()

    def is_rm_value_rna(self) -> bool:
        """Determine if this term is a rounding mode ``RNA`` value.

           :return: True if this term is a roundindg mode ``RNA`` value.
        """
        return self.c_term.is_rm_value_rna()

    def is_rm_value_rne(self) -> bool:
        """Determine if this term is a rounding mode ``RNE`` value.

           :return: True if this term is a rounding mode ``RNE`` value.
        """
        return self.c_term.is_rm_value_rne()

    def is_rm_value_rtn(self) -> bool:
        """Determine if this term is a rounding mode ``RTN`` value.

           :return: True if this term is a rounding mode RTN value.
        """
        return self.c_term.is_rm_value_rtn()

    def is_rm_value_rtp(self) -> bool:
        """Determine if this term is a rounding mode ``RTP`` value.

           :return: True if this term is a rounding mode ``RTP`` value.
        """
        return self.c_term.is_rm_value_rtp()

    def is_rm_value_rtz(self) -> bool:
        """Determine if this term is a rounding mode ``RTZ`` value.

           :return: True if this term is a rounding mode ``RTZ`` value.
        """
        return self.c_term.is_rm_value_rtz()

    def value(self, uint8_t base = 2, fp_as_tuple = True):
        """Get value from value term.

           This function is instantiated for types
           - ``bool`` for Boolean values
           - ``RoundingMode`` for rounding mode values
           - ``string`` for bit-vector and floating-point values

           In case of string representations of values this returns the raw
           value string (as opposed to str(), which returns the SMT-LIB v2
           representation of a term). For example, this function returns
           ``"010"`` for a bit-vector value 2 of size 3, while str() returns
           ``"#b010"``.

           :note: The returned string for floating-point values is always the
                  binary IEEE-754 representation of the value (parameter `base`
                  is ignored). Parameter `base` always configures the numeric
                  base for bit-vector values, and for floating-point values in
                  case of the tuple of strings instantiation. It is always
                  ignored for Boolean and RoundingMode values.

           :param base: The numeric base for bit-vector values; ``2`` for
                         binary, ``10`` for decimal, and ``16`` for hexadecimal.
           :param fp_as_tuple: True if a floating-point value is to be
                                represented as a tuple of raw string
                                representations of the sign, exponent and
                                significand bit-vectors. False to represent as
                                the binary IEEE-754 string representation of a
                                single bit-vector.
        """
        sort = self.sort()
        if sort.is_bool():
            return self.c_term.value[c_bool]()
        if sort.is_rm():
            return RoundingMode(self.c_term.value[bitwuzla_api.RoundingMode]())
        if sort.is_fp() and fp_as_tuple:
            return [s.decode()
                    for s in bitwuzla_api.get_fp_value_ieee(self.c_term, base)]
        return self.c_term.value[string](base).decode()

    def str(self, uint8_t base = 2) -> str:
        """Get the SMT-LIB v2 string representation of this term.

           :param base: The base of the string representation of bit-vector
                         values; ``2`` for binary, ``10`` for decimal, and
                         ``16`` for hexadecimal. Always ignored for Boolean and
                         RoundingMode values.
           :return: A string representation of this term.
        """
        return self.c_term.str(base).decode()

    def __str__(self) -> str:
        """Get the SMT-LIB v2 string representation of this term.

           :note: This uses the default (binary) output number format for
                  bit-vector values.
           :return: A string representation of this term.
        """
        return self.c_term.str(2).decode()

    def __eq__(self, other: Term) -> bool:
        """Syntactical equality operator.

           :param a: The first term.
           :param b: The second term.
           :return: True if the given terms are equal.
        """
        return self.c_term == other.c_term

    def __hash__(self):
        return self.id()


# --------------------------------------------------------------------------- #
# Options wrapper
# --------------------------------------------------------------------------- #

cdef class Options:
    """A Bitwuzla options configuration."""
    cdef bitwuzla_api.Options c_options

    def is_valid(self, name: str):
        """Determine if given string is a valid short or long option name.
           :param name: The name.
           :return: True if given string is a option name.
        """
        return self.c_options.is_valid(<const string&> name.encode())

    def shrt(self, option: Option) -> str:
        """Get the short name of this option.

           :return: The short name of this option.
        """
        return self.c_options.shrt(option.value).decode()

    def lng(self, option: Option) -> str:
        """Get the long name of this option.

           :return: The long name of this option.
        """
        return self.c_options.lng(option.value).decode()

    def description(self, option: Option) -> str:
        """Get the description of this option.

           :return: The description of this option.
        """
        return self.c_options.description(option.value).decode()

    def modes(self, option: Option) -> list[str]:
        """Get the modes of this option.

           :return: The modes of this option.
        """
        return [m.decode() for m in self.c_options.modes(option.value)]

    def set(self, option, value):
        """ Set option.

            :param option: The option or the long or short name of an option.
            :param value:  The option value.
        """
        cdef bitwuzla_api.Option opt
        if isinstance(option, Option):
            opt = option.value
        elif isinstance(option, str):
            opt = self.option(option).value
        else:
            raise ValueError(f'Invalid option {option}.')

        if isinstance(value, str):
            self.c_options.set(opt, <const string&> value.encode())
        elif isinstance(value, bool) or isinstance(value, int):
            self.c_options.set(opt, <uint64_t?> value)
        else:
            raise ValueError(f'Invalid value type for option {option.value}.')

    def set_args(self, *args):
        """ Set option via command-line.

            Supports the following command line option format:

            Short option names: ::

              -short      ... ["-short"]
              -short=val  ... ["-short=val"]
              -short val  ... ["-short", "val"]

            Long option names: ::

              --long      ... ["--long"]
              --long=val  ... ["--long=val"]
              --long val  ... ["--long", "val"]

            :param args: List of command line options.
        """
        cdef vector[string] opts
        for a in args:
            opts.push_back(str(a).encode())
        self.c_options.set(opts)

    def option(self, name: str) -> Option:
        """ Get the option associated to the given short or long option name.

            :return: The option associated to the given short or long option
                     name.
        """
        return Option(self.c_options.option(name.encode()))

    def get(self, option: Option):
        """ Get the current value of the given option.

            :param option: The option.
            :return: The current value of the given option.
        """
        if self.c_options.is_mode(option.value):
            return self.c_options.get_mode(option.value).decode()
        elif self.c_options.is_numeric(option.value):
            return self.c_options.get(option.value)
        elif self.c_options.is_bool(option.value):
            return self.c_options.get(option.value) != 0

    def is_bool(self, option: Option):
        """ Determine if given option is a Boolean option.

            :param option: The option to query.
            :return: True if `option` is a Boolean option.
        """
        return self.c_options.is_bool(option.value)

    def is_numeric(self, option: Option):
        """ Determine if given option is a numeric option.

            :param option: The option to query.
            :return: True if `option` is a numeric option.
        """
        return self.c_options.is_numeric(option.value)


    def is_mode(self, option: Option):
        """ Determine if given option is an option with a mode.

            :param option: The option to query.
            :return: True if `option` is an option with a mode.
        """
        return self.c_options.is_mode(option.value)

# --------------------------------------------------------------------------- #
# OptionInfo wrapper
# --------------------------------------------------------------------------- #

class OptionInfoKind(Enum):
    """The kind of an OptionInfo.

    """
    BOOL = bitwuzla_api.CppOptionInfoKind.BOOL
    NUMERIC = bitwuzla_api.CppOptionInfoKind.NUMERIC
    MODE = bitwuzla_api.CppOptionInfoKind.MODE

cdef class OptionInfo:
    """ The class holding all information about an option.
    """
    cdef unique_ptr[bitwuzla_api.OptionInfo] c_info

    def __init__(self, options: Options, option: Option):
        self.c_info.reset(
                new bitwuzla_api.OptionInfo(options.c_options, option.value))

    def shrt(self):
        """Get the short name of an option.
           :return: The short name, if any, else None.
        """
        return _to_str(self.c_info.get().shrt)

    def lng(self):
        """Get the long name of an option.
           :return: The long name of an option.
        """
        return _to_str(self.c_info.get().lng)

    def kind(self) -> OptionInfoKind:
        """Get the kind of this OptionInfo.
           :return: The kind.
        """
        return OptionInfoKind(self.c_info.get().kind)

    def dflt(self):
        """Get the default value of an option.
           :return: The default value.
        """
        if self.kind() == OptionInfoKind.BOOL:
            return self.c_info.get().value[bitwuzla_api.OptionInfoBool]().dflt
        if self.kind() == OptionInfoKind.MODE:
            return self.c_info.get().value[
                    bitwuzla_api.OptionInfoMode]().dflt.decode()
        return self.c_info.get().value[bitwuzla_api.OptionInfoNumeric]().dflt

    def cur(self):
        """Get the current value of an option.
           :return: The current default value.
        """
        if self.kind() == OptionInfoKind.BOOL:
            return self.c_info.get().value[bitwuzla_api.OptionInfoBool]().cur
        if self.kind() == OptionInfoKind.MODE:
            return self.c_info.get().value[
                    bitwuzla_api.OptionInfoMode]().cur.decode()
        return self.c_info.get().value[bitwuzla_api.OptionInfoNumeric]().cur

    def min(self):
        """Get the minimum value of a numeric option.
           :return: The minimum value.
        """
        if self.kind() == OptionInfoKind.NUMERIC:
            return self.c_info.get().value[bitwuzla_api.OptionInfoNumeric]().min
        return None

    def max(self):
        """Get the maximum value of a numeric option.
           :return: The maximum value.
        """
        if self.kind() == OptionInfoKind.NUMERIC:
            return self.c_info.get().value[bitwuzla_api.OptionInfoNumeric]().max
        return None

    def modes(self):
        """Get the available modes of an option with modes.
           :return: The modes.
        """
        if self.kind() == OptionInfoKind.MODE:
            return [
                    _to_str(m) for m in
                    self.c_info.get().value[bitwuzla_api.OptionInfoMode]().modes
                   ]
        return None

    def description(self):
        """Get the description of an option.
           :return: The description.
        """
        return _to_str(self.c_info.get().description)

# --------------------------------------------------------------------------- #
# TermManager wrapper
# --------------------------------------------------------------------------- #

cdef class TermManager:
    """The term manager is responsible for the creation and management of sorts
       and terms. Sorts and terms are tied to a specific term manager instance
       and can be shared between multiple solver instances that have the same
       term manager.
    """
    cdef shared_ptr[bitwuzla_api.TermManager] c_tm
    cdef bitwuzla_api.TermManager* c_tm_ptr

    def __init__(self):
        self.c_tm.reset(new bitwuzla_api.TermManager())
        self.c_tm_ptr = self.c_tm.get()

    def __eq__(self, other: TermManager):
        return self.c_tm_ptr == other.c_tm_ptr

    # ----------------------------------------------------------------------- #
    # Sort functions
    # ----------------------------------------------------------------------- #

    def mk_bool_sort(self) -> Sort:
        """Create a Boolean sort.

           :return: Sort of type Boolean.
        """
        return _sort(self, self.c_tm_ptr.mk_bool_sort())

    def mk_bv_sort(self, size: uint64_t) -> Sort:
        """Create bit-vector sort of size ``size``.

           :param size: Bit width.
           :return:  Bit-vector sort of size ``size``.
        """
        return _sort(self, self.c_tm_ptr.mk_bv_sort(size))

    def mk_array_sort(self, index: Sort, elem: Sort) -> Sort:
        """Create array sort with given index and element sorts.

           :param index: The sort of the array index.
           :param elem: The sort of the array elements.
           :return:  Array sort.
          """
        return _sort(self, self.c_tm_ptr.mk_array_sort(index.c_sort, elem.c_sort))

    def mk_fun_sort(self, domain: list[Sort], codomain: Sort) -> Sort:
        """Create function sort with given domain and codomain.

           :param domain: A list of all the function arguments' sorts.
           :param codomain: The sort of the function's return value.
           :return:  Function sort, which maps ``domain`` to ``codomain``.
          """
        return _sort(self, self.c_tm_ptr.mk_fun_sort(_sort_vec(domain),
                                               _csort(codomain)))

    def mk_fp_sort(self, exp_size: uint64_t, sig_size: uint64_t) -> Sort:
        """Create a floating-point sort with given exponent size ``exp_size``
           and significand size ``sig_size``.

           :param exp_size: Exponent size.
           :param sig_size: Significand size.
           :return: Floating-point sort.
        """
        return _sort(self, self.c_tm_ptr.mk_fp_sort(exp_size, sig_size))

    def mk_rm_sort(self, ) -> Sort:
        """Create a rounding mode sort.

           :return: Rounding mode sort.
        """
        return _sort(self, self.c_tm_ptr.mk_rm_sort())

    def mk_uninterpreted_sort(self, symbol: str = None) -> Sort:
        """Create an uninterpreted sort.

           :param symbol: The symbol of the sort.
           :return: Uninterpreted Sort.

           .. note::
                Only 0-arity uninterpreted sorts are supported.
        """
        cdef optional[string] opt = nullopt
        if symbol:
            opt = <string?> symbol.encode()
        return _sort(self,
                self.c_tm_ptr.mk_uninterpreted_sort(
                    <optional[const string]?> opt))


    # ----------------------------------------------------------------------- #
    # Value functions
    # ----------------------------------------------------------------------- #

    def mk_true(self, ) -> Term:
        """mk_true()

        Create true value.

        :return: A term representing true.
        :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_true())

    def mk_false(self, ) -> Term:
        """mk_false()

        Create false value.

        :return: A term representing false.
        :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_false())

    def mk_bv_value(self, sort: Sort, value, *args) -> Term:
        """mk_bv_value(sort: Sort, value: int) -> Term
           mk_bv_value(sort: Sort, value: str, base: int) -> Term

           Create bit-vector representing ``value`` of given ``sort``.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort
           :param value: An integer representing the value.
           :type value: int

           Create bit-vector representing ``value`` of given ``sort`` and
           ``base``.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort
           :param value: A string representing the value.
           :type value: str
           :param base: The numerical base of the string representation (``2``
                        for binary, ``10`` for decimal, ``16`` for hexadecimal).
           :type base: int

           :return: A term representing the bit-vector value.
           :rtype: BitwuzlaTerm
        """
        if isinstance(value, str):
            if not args:
                raise ValueError('expected base')
            return _term(self,
                    self.c_tm_ptr.mk_bv_value(
                        sort.c_sort, value.encode(), <uint8_t> int(args[0])))
        if args:
            raise ValueError('unexpected base')
        return _term(self,
                self.c_tm_ptr.mk_bv_value(sort.c_sort,
                                            str(value).encode(),
                                            10))

    def mk_bv_zero(self, sort: Sort) -> Term:
        """mk_bv_zero(sort)

           Create a bit-vector value zero with ``sort``.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value zero of given sort.
           :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_bv_zero(sort.c_sort))

    def mk_bv_one(self, sort: Sort) -> Term:
        """mk_bv_one(sort)

           Create a bit-vector value one with ``sort``.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value one of given sort.
           :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_bv_one(sort.c_sort))

    def mk_bv_ones(self, sort: Sort) -> Term:
        """mk_bv_ones(sort)

           Create a bit-vector value with ``sort`` where all bits are set to 1.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where all bits are set to 1.
           :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_bv_ones(sort.c_sort))

    def mk_bv_min_signed(self, sort: Sort) -> Term:
        """mk_bv_min_signed(sort)

           Create a bit-vector minimum signed value.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where the MSB is set to 1 and all remaining bits are set to
                    0.
           :rtype: BitwuzlaTerm

        """
        return _term(self, self.c_tm_ptr.mk_bv_min_signed(sort.c_sort))

    def mk_bv_max_signed(self, sort: Sort) -> Term:
        """mk_bv_max_signed(sort)

           Create a bit-vector maximum signed value.

           :param sort: Bit-vector sort.
           :type sort: BitwuzlaSort

           :return: A term representing the bit-vector value of given sort
                    where the MSB is set to 0 and all remaining bits are set to
                    1.
           :rtype: BitwuzlaTerm
        """
        return _term(self, self.c_tm_ptr.mk_bv_max_signed(sort.c_sort))

    def mk_fp_value(self, *args) -> Term:
        """mk_fp_value(sign: Term, exponent: Term, significand: Term) -> Term
           mk_fp_value(sort: Sort, rm: Term, real: str) -> Term
           mk_fp_value(sort: Sort, rm: Term, num: str, den: str) -> Term

           Create a floating-point value from its IEEE 754 standard
           representation given as three bit-vector values representing the
           sign bit, the exponent and the significand.

           :param sign: Bit-vector value term representing the sign bit.
           :param exponent: Bit-vector value term representing the exponent.
           :param significand: Bit-vector value term representing the
                               significand.

           Create a floating-point value from its real representation, given as
           a decimal string, with respect to given rounding mode.

           :param sort: Floating-point sort.
           :param rm: Rounding mode term.
           :param real: The decimal string representing a real value

           Create a floating-point value from its rational representation,
           given as a two decimal strings representing the numerator and
           denominator, with respect to given rounding mode.

           :param sort: Floating-point sort.
           :param rm: Rounding mode term.
           :param num: The decimal string representing the numerator.
           :param den: The decimal string representing the denominator.

           :return: A term representing the floating-point value.

           .. seealso::
             :func:`~bitwuzla.TermManager.mk_bv_value` for the supported value
             format for ``sign``, ``exponent``, and ``significand``.
        """
        if isinstance(args[0], Sort):
            _check_arg(args[1], Term)
            if len(args) == 4:
                _check_arg(args[2], [str, int])
                _check_arg(args[3], [str, int])
                return _term(self, self.c_tm_ptr.mk_fp_value(
                                _csort(args[0]),
                                _cterm(args[1]),
                                str(args[2]).encode(),
                                str(args[3]).encode()))
            elif len(args) != 3:
                raise ValueError('Invalid number of arguments')
            _check_arg(args[2], [str, int, float])
            return _term(self, self.c_tm_ptr.mk_fp_value(
                            _csort(args[0]),
                            _cterm(args[1]),
                            <const string&> str(args[2]).encode()))
        elif isinstance(args[0], Term):
            _check_arg(args[1], Term)
            _check_arg(args[2], Term)
            return _term(self, self.c_tm_ptr.mk_fp_value(
                            _cterm(args[0]), _cterm(args[1]), _cterm(args[2])))
        else:
            raise ValueError('Invalid arguments')

    def mk_fp_pos_zero(self, sort: Sort) -> Term:
        """Create a floating-point positive zero value (SMT-LIB: `+zero`).

           :param sort: Floating-point sort.
           :return: A term representing the floating-point positive zero value
                    of given floating-point sort.
        """
        return _term(self, self.c_tm_ptr.mk_fp_pos_zero(_csort(sort)))

    def mk_fp_neg_zero(self, sort: Sort) -> Term:
        """Create a floating-point negative zero value (SMT-LIB: `-zero`).

           :param sort: Floating-point sort.
           :return: A term representing the floating-point negative zero value
                    of given floating-point sort.
        """
        return _term(self, self.c_tm_ptr.mk_fp_neg_zero(_csort(sort)))

    def mk_fp_pos_inf(self, sort: Sort) -> Term:
        """Create a floating-point positive infinity value (SMT-LIB: `+oo`).

           :param sort: Floating-point sort.
           :return: A term representing the floating-point positive infinity
                    value of given floating-point sort.
        """
        return _term(self, self.c_tm_ptr.mk_fp_pos_inf(_csort(sort)))

    def mk_fp_neg_inf(self, sort: Sort) -> Term:
        """Create a floating-point negative infinity value (SMT-LIB: `-oo`).

           :param sort: Floating-point sort.
           :return: A term representing the floating-point negative infinity
                    value of given floating-point sort.
        """
        return _term(self, self.c_tm_ptr.mk_fp_neg_inf(_csort(sort)))

    def mk_fp_nan(self, sort: Sort) -> Term:
        """Create a floating-point NaN value.

           :param sort: Floating-point sort.
           :return: A term representing the floating-point NaN value of given
                    floating-point sort.
        """
        return _term(self, self.c_tm_ptr.mk_fp_nan(_csort(sort)))

    def mk_rm_value(self, rm: RoundingMode) -> Term:
        """Create a rounding mode value.

           :param rm: Rounding mode.
           :return: A term representing the rounding mode value.
        """
        return _term(self, self.c_tm_ptr.mk_rm_value(rm.value))


    # ----------------------------------------------------------------------- #
    # Term functions
    # ----------------------------------------------------------------------- #

    def mk_const(self, sort: Sort, symbol: str = None) -> Term:
        """Create a (first-order) constant of given sort with given symbol.

           :param sort: The sort of the constant.
           :param symbol: The symbol of the constant.
           :return: A term of kind :class:`~bitwuzla.Kind.CONSTANT`,
                    representing the constant.
        """
        cdef optional[string] opt = nullopt
        if symbol:
            opt = <string?> symbol.encode()
        return _term(self, self.c_tm_ptr.mk_const(
                        _csort(sort), <optional[const string]?> opt))

    def mk_const_array(self, sort: Sort, term: Term) -> Term:
        """Create a one-dimensional constant array of given sort, initialized
           with given value.

           :param sort: The sort of the array.
           :param term: The term to initialize the elements of the array with.
           :return: A term of kind :class:`~bitwuzla.Kind.CONST_ARRAY`,
                    representing a constant array of given sort.
        """
        return _term(self,
                     self.c_tm_ptr.mk_const_array(_csort(sort), _cterm(term)))

    def mk_var(self, sort: Sort, symbol: str = None) -> Term:
        """Create a (first-order) variable of given sort with given symbol.

           :param sort: The sort of the variable.
           :param symbol: The symbol of the variable.
           :return: A term of kind :class:`~bitwuzla.Kind.VARIABLE`,
                    representing the variable.
        """
        cdef optional[string] opt = nullopt
        if symbol:
            opt = <string?> symbol.encode()
        return _term(self, self.c_tm_ptr.mk_var(
                        _csort(sort), <optional[const string]?> opt))

    def mk_term(self, kind: Kind,
                terms: list[Term],
                indices: list[int] = []) -> Term:
        """Create a term of given kind with the given argument terms.

           :param kind: The operator kind.
           :param terms: The argument terms.
           :param indices: The indices of this term, empty if not indexed.
           :return: A term representing an operation of given kind.
        """
        return _term(self, self.c_tm_ptr.mk_term(kind.value,
                                             _term_vec(terms),
                                             indices))

    # ----------------------------------------------------------------------- #
    # Term substitution
    # ----------------------------------------------------------------------- #

    def substitute_term(self, term: Term, substs: dict[Term, Term]) -> Term:
        """Substitute a set terms in a given term. The substitutions to perform
           are represented as map from keys to be substituted with their
           corresponding values in the given term.

           :param term: The term in which the terms are to be substituted.
           :param substs: The substitution map.
           :return: The resulting term from this substitution.
        """
        cdef unordered_map[bitwuzla_api.Term, bitwuzla_api.Term] c_substs
        for k,v in substs.items(): c_substs[_cterm(k)] = _cterm(v)
        return _term(self, self.c_tm_ptr.substitute_term(term.c_term, c_substs))

    def substitute_terms(self,
                         terms: list[Term],
                         substs: dict[Term, Term]) -> list[Term]:
        """Substitute a set of terms in a set of given terms. The substitutions
           to perform are represented as map from keys to be substituted with
           their corresponding values in the given terms.

           The terms in `terms` are replaced with the terms resulting from these
           substitutions.

           :param terms: The terms in which the terms are to be substituted.
           :param substs: The substitution map.
        """
        cdef unordered_map[bitwuzla_api.Term, bitwuzla_api.Term] c_substs
        cdef vector[bitwuzla_api.Term] c_terms = _term_vec(terms)
        for k,v in substs.items(): c_substs[_cterm(k)] = _cterm(v)
        self.c_tm_ptr.substitute_terms(c_terms, c_substs)
        return _terms(self, c_terms)


# --------------------------------------------------------------------------- #
# Bitwuzla wrapper
# --------------------------------------------------------------------------- #

cdef class Bitwuzla:
    """A Bitwuzla solver instance."""
    cdef shared_ptr[bitwuzla_api.Bitwuzla] c_bitwuzla
    cdef unique_ptr[bitwuzla_api.PyTerminator] c_terminator
    cdef TermManager tm

    @staticmethod
    @cython.cfunc
    def from_shared_ptr(tm: TermManager(), _sptr: shared_ptr[bitwuzla_api.Bitwuzla]) -> Bitwuzla:
        """Wrap shared_ptr[bitwuzla_api.Bitwuzla] into Bitwuzla instance.
        """
        b: Bitwuzla = Bitwuzla.__new__(Bitwuzla)
        b.c_bitwuzla = _sptr
        b.tm = tm
        return b

    def __init__(self, tm: TermManager, options: Options = Options()):
        """Constructor.

           :param options: The options configuration of the solver instance.
        """
        self.c_bitwuzla.reset(
            new bitwuzla_api.Bitwuzla(dereference(tm.c_tm.get()),
                                                  options.c_options))
        self.tm = tm

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

                def __call__(self):
                    # Terminate after self.time_limit seconds passed
                    return time.time() - self.start_time > self.time_limit

             bitwuzla = Bitwuzla()
             bitwuzla.configure_terminator(lambda: True)            # immediately terminate
             bitwuzla.configure_terminator(TimeLimitTerminator(1))  # terminate after 1s
             bitwuzla.configure_terminator(TimeLimitTerminator(10)) # terminate after 10s

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


    def get_assertions(self) -> list[Term]:
        """Get currently asserted formulas.
           :return: List of current assertions.
        """
        return _terms(self.tm, self.c_bitwuzla.get().get_assertions())

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
        return _terms(self.tm, self.c_bitwuzla.get().get_unsat_assumptions())

    def get_unsat_core(self) -> list[Term]:
        """Return list of unsatisfiable assertions previously added via
           :func:`~bitwuzla.Bitwuzla.assert_formula`.

           Requires that the last :func:`~bitwuzla.Bitwuzla.check_sat` call
           returned :class:`~bitwuzla.Result.UNSAT`.

           :return:  list of unsatisfiable assertions
        """
        return _terms(self.tm, self.c_bitwuzla.get().get_unsat_core())

    def simplify(self):
        """Simplify current set of input assertions.

           .. note::
               Each call to :func:`~bitwuzla.Bitwuzla.check_sat`
               simplifies the input formula as a preprocessing step.
               It is not necessary to call this function explicitly in the
               general case.
        """
        self.c_bitwuzla.get().simplify()

    def get_value(self, term: Term) -> Term:
        """Get model value of term.

           Requires that the last :func:`~bitwuzla.Bitwuzla.check_sat` call
           returned `~bitwuzla.Result.SAT`.

           :return: Term representing the model value of `term`.
        """
        return _term(self.tm, self.c_bitwuzla.get().get_value(_cterm(term)))

    def print_formula(self, fmt: str = 'smt2', uint8_t base = 2) -> str:
        """Get the current input formula as a string.

           :param fmt: The output format for printing the formula. Currently,
                        only `"smt2"` for the SMT-LIB v2 format is supported.
           :param base: The base of the string representation of bit-vector
                        values; ``2`` for binary, ``10`` for decimal, and
                        ``16`` for hexadecimal. Always ignored for Boolean and
                        RoundingMode values.
           :return: The current input formula as a string in the given format.
        """
        cdef bitwuzla_api.stringstream c_ss
        cdef unique_ptr[bitwuzla_api.set_bv_format] c_bv_fmt

        c_bv_fmt.reset(new bitwuzla_api.set_bv_format(base))

        c_ss << dereference(c_bv_fmt.get())
        self.c_bitwuzla.get().print_formula(c_ss, <const string&> fmt.encode())
        return c_ss.to_string().decode()

    def print_unsat_core(self, fmt: str = 'smt2', uint8_t base = 2) -> str:
        """Get the current unsat core as benchmark as a string.

           :param fmt: The output format for printing the formula. Currently,
                        only `"smt2"` for the SMT-LIB v2 format is supported.
           :param base: The base of the string representation of bit-vector
                        values; ``2`` for binary, ``10`` for decimal, and
                        ``16`` for hexadecimal. Always ignored for Boolean and
                        RoundingMode values.
           :return: The current input formula as a string in the given format.
        """
        cdef bitwuzla_api.stringstream c_ss
        cdef unique_ptr[bitwuzla_api.set_bv_format] c_bv_fmt

        c_bv_fmt.reset(new bitwuzla_api.set_bv_format(base))

        c_ss << dereference(c_bv_fmt.get())
        self.c_bitwuzla.get().print_unsat_core(c_ss,
                                               <const string&> fmt.encode())
        return c_ss.to_string().decode()

    def statistics(self) -> dict[str, str]:
        """Get current statistics.

           :return: A map of strings of statistics entries, maps statistic name
                    to value.
        """
        return {_to_str(k): _to_str(v)
                for [k, v] in self.c_bitwuzla.get().statistics()}

    def term_mgr(self) -> TermManager:
        tm = TermManager()
        tm.c_tm_ptr = &self.c_bitwuzla.get().term_mgr()
        return tm

# --------------------------------------------------------------------------- #
# Parser
# --------------------------------------------------------------------------- #

cdef class Parser:
    """The Bitwuzla parser."""
    cdef unique_ptr[bitwuzla_api.Parser] c_parser
    cdef Options options
    cdef TermManager tm

    def __init__(self,
                 tm: TermManager,
                 options: Options,
                 language = "smt2",
                 uint8_t base = 2):
        """Constructor.

           :note: The parser creates and owns the associated Bitwuzla instance.
           :param options:  The configuration options for the Bitwuzla instance
                            (created by the parser).
           :param language: The format of the input.
           :param base:     The base of the string representation of bit-vector
                            values; ``2`` for binary, ``10`` for decimal, and
                            ``16`` for hexadecimal. Always ignored for Boolean
                            and RoundingMode values.
        """
        cdef unique_ptr[bitwuzla_api.set_bv_format] c_bv_fmt
        self.options = options
        self.tm = tm
        c_bv_fmt.reset(new bitwuzla_api.set_bv_format(base))
        bitwuzla_api.cout << dereference(c_bv_fmt.get())
        self.c_parser.reset(
                new bitwuzla_api.Parser(
                    dereference(tm.c_tm.get()),
                    options.c_options,
                    <const string&> str(language).encode(),
                    &bitwuzla_api.cout))

    def configure_auto_print_model(self, value: bool):
        """Enable or disable the automatic printing of the model after each
           satisfiable query.

           Enable to automatically print the model after every sat query.
           Must be enabled to automatically print models for BTOR2 input (does
           not provide a command to print the model like `(get-model)` in
           SMT-LIB2). False (default) configures the standard behavior for
           SMT-LIB2 input (print model only after a `(get-model)` command).

           :note: By default, auto printing of the model is disabled.
           :param value: True to enable auto printing of the model.
        """
        self.c_parser.get().configure_auto_print_model(value)

    def parse(self,
              iinput,
              parse_only: bool = False,
              parse_file: bool = True) -> bool:
        """Parse input, either from a file or from a string.

           :param input:      The name of the input file if ``parse_file`` is
                              ``True``, else a string with the input.
           :param parse_only: ``True`` to only parse without issuing calls to
                              check_sat.
           :param parse_file: ``True`` to parse an input file with the given
                              name ``iinput``, ``False`` to parse from
                              ``iinput`` as a string input.
           :raise BitwuzlaException: On parse error.
           :note: Parameter `parse_only` is redundant for BTOR2 input, its the
                  only available mode for BTOR2 (due to the language not
                  supporting "commands" as in SMT2).
        """
        self.c_parser.get().parse(
                <const string&> str(iinput).encode(), parse_only, parse_file)

    def parse_term(self, iinput) -> Term:
        """Parse term from string.

           :param input: The input string.
           :return:      The parsed term.
           :raise BitwuzlaException: On parse error.
        """
        return _term(self.tm, self.c_parser.get().parse_term(
                <const string&> str(iinput).encode()))

    def parse_sort(self, iinput) -> Sort:
        """Parse sort from string.

           :param input: The input string.
           :return:      The parsed sort.
           :raise BitwuzlaException: On parse error.
        """
        return _sort(self.tm, self.c_parser.get().parse_sort(
                <const string&> str(iinput).encode()))

    def get_declared_sorts(self) -> list[Sort]:
        """Get the current set of (user-)declared sort symbols.

           :note: Corresponds to the sorts declared via SMT-LIB command
                  ``declare-sort``. Will always return an empty list for BTOR2
                  input.
           :return: The declared sorts.
        """
        return _sorts(self.tm, self.c_parser.get().get_declared_sorts())

    def get_declared_funs(self) -> list[Term]:
        """Get the current set of (user-)declared function symbols.

           :note: Corresponds to the function symbols declared via SMT-LIB
                  commands ``declare-const`` and ``declare-fun``.
           :return: The declared function symbols.
        """
        return _terms(self.tm, self.c_parser.get().get_declared_funs())

    def bitwuzla(self) -> Bitwuzla:
        """Get the associated Bitwuzla instance.

           :return: The Bitwuzla instance.
        """
        return Bitwuzla.from_shared_ptr(self.tm, self.c_parser.get().bitwuzla())
