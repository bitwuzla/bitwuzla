###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

from bitwuzla import BitwuzlaException
from cpython.ref cimport PyObject
from libc.stdint cimport uint8_t, uint32_t, uint64_t, int64_t
from libcpp cimport bool
from libcpp.optional cimport optional
from libcpp.string cimport string
from libcpp.vector cimport vector

cdef extern from "<functional>" namespace "std" nogil:
    cdef cppclass reference_wrapper[T]:
        pass

cdef extern from "terminator.h":
    cdef cppclass PyTerminator:
        PyTerminator(PyObject* terminator)
        bool terminate()

cdef extern from "bitwuzla/cpp/bitwuzla.h" namespace "bitwuzla":

    string copyright() except +
    string version() except +
    string git_id() except +

    cdef enum class Kind:
        pass

    cdef enum class Result:
        pass

    cdef enum class RoundingMode:
        pass

    cdef enum class Option:
        pass

    cdef cppclass Options:
        Options() except +
        bool is_bool(Option option) except +
        bool is_numeric(Option option) except +
        bool is_mode(Option option) except +
        const char *shrt(Option option) except +
        const char *lng(Option option) except +
        const char *description(Option option) except +
        vector[string] modes(Option option) except +
        Option option(const char *name) except +
        void set(Option option, uint64_t value) except +
        void set(Option option, const string &mode) except +
        #void set(const string &lng, const string &value) except +
        void set(const vector[string] &args) except +
        uint64_t get(Option option) except +
        const string &get_mode(Option option) except +

    cdef cppclass Sort:
        Sort() except +
        bool is_null() except +
        uint64_t id() except +
        uint64_t bv_size() except +
        uint64_t fp_exp_size() except +
        uint64_t fp_sig_size() except +
        Sort array_index() except +
        Sort array_element() except +
        vector[Sort] fun_domain() except +
        Sort fun_codomain() except +
        size_t fun_arity() except +
        optional[string] uninterpreted_symbol() except +
        bool is_array() except +
        bool is_bool() except +
        bool is_bv() except +
        bool is_fp() except +
        bool is_fun() except +
        bool is_rm() except +
        bool is_uninterpreted() except +
        string str() except +
        bool operator==(const Sort&) except +

    cdef cppclass Term:
        Term() except +
        bool is_null() except +
        uint64_t id() except +
        Kind kind() except +
        Sort sort() except +
        size_t num_children() except +
        vector[Term] children() except +
        Term operator[](size_t index) except +
        size_t num_indices() except +
        vector[uint64_t] indices() except +
        optional[reference_wrapper[const string]] symbol() except +
        bool is_const() except +
        bool is_variable() except +
        bool is_value() except +
        bool is_bv_value_zero() except +
        bool is_bv_value_one() except +
        bool is_bv_value_ones() except +
        bool is_bv_value_min_signed() except +
        bool is_bv_value_max_signed() except +
        bool is_fp_value_pos_zero() except +
        bool is_fp_value_neg_zero() except +
        bool is_fp_value_pos_inf() except +
        bool is_fp_value_neg_inf() except +
        bool is_fp_value_nan() except +
        bool is_rm_value_rna() except +
        bool is_rm_value_rne() except +
        bool is_rm_value_rtn() except +
        bool is_rm_value_rtp() except +
        bool is_rm_value_rtz() except +
        string str() except +
        bool value[bool](uint8_t base) except +
        RoundingMode value[RoundingMode](uint8_t base) except +
        string value[string](uint8_t base) except +

    cdef cppclass Terminator:
        pass

    cdef cppclass Bitwuzla:
        Bitwuzla(const Options &options);
        void configure_terminator(Terminator *terminator) except +
        void push(uint32_t nlevels) except +
        void pop(uint32_t nlevels) except +
        void assert_formula(const Term &term) except +
        bool is_unsat_assumption(const Term &term) except +
        vector[Term] get_unsat_assumptions() except +
        vector[Term] get_unsat_core() except +
        Result simplify() except +
        Result check_sat(const vector[Term] &assumptions) except +
        Term get_value(const Term &term) except +
        #void print_formula(ostream &out, const string &format) except +


    Sort mk_array_sort(const Sort &index, const Sort &element) except +
    Sort mk_bool_sort() except +
    Sort mk_bv_sort(uint64_t size) except +
    Sort mk_fp_sort(uint64_t exp_size, uint64_t sig_size) except +
    Sort mk_fun_sort(const vector[Sort] &domain, const Sort &codomain) except +
    Sort mk_rm_sort() except +
    Sort mk_uninterpreted_sort(optional[const string] symbol) except +


    Term mk_true() except +
    Term mk_false() except +
    Term mk_bv_zero(const Sort &sort) except +
    Term mk_bv_one(const Sort &sort) except +
    Term mk_bv_ones(const Sort &sort) except +
    Term mk_bv_min_signed(const Sort &sort) except +
    Term mk_bv_max_signed(const Sort &sort) except +
    Term mk_bv_value(const Sort &sort, const string &value, uint8_t base) except +
    Term mk_bv_value_uint64(const Sort &sort, uint64_t value) except +
    Term mk_bv_value_int64(const Sort &sort, int64_t value) except +
    Term mk_fp_pos_zero(const Sort &sort) except +
    Term mk_fp_neg_zero(const Sort &sort) except +
    Term mk_fp_pos_inf(const Sort &sort) except +
    Term mk_fp_neg_inf(const Sort &sort) except +
    Term mk_fp_nan(const Sort &sort) except +
    Term mk_fp_value(const Term &bv_sign,
                     const Term &bv_exponent,
                     const Term &bv_significand) except +

    Term mk_fp_value(const Sort &sort, const Term &rm, const string &real) except +
    Term mk_fp_value(const Sort &sort,
                     const Term &rm,
                     const string &num,
                     const string &den) except +
    Term mk_const_array(const Sort &sort, const Term &term) except +
    Term mk_rm_value(RoundingMode rm) except +
    Term mk_term(Kind kind,
                 const vector[Term] &args,
                 const vector[uint64_t] &indices) except +
    Term mk_const(const Sort &sort,
                  optional[const string] symbol) except +
    Term mk_var(const Sort &sort,
                optional[const string] symbol) except +

# -------------------------------------------------------------------------- #
