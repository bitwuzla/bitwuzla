###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

from libc.stdio cimport FILE
from libcpp cimport bool
from cpython.ref cimport PyObject
from libc.stdint cimport int32_t, uint32_t, uint64_t
from pybitwuzla import BitwuzlaException

cdef inline int raise_py_error() except *:
    raise BitwuzlaException(
            pybitwuzla_get_err_msg().decode('utf-8').split(':', 1)[1].strip())

cdef extern from "pybitwuzla_abort.h":
    void pybitwuzla_abort_fun(const char* msg)
    const char * pybitwuzla_get_err_msg()

cdef extern from "pybitwuzla_utils.h":
    void pybitwuzla_delete(Bitwuzla *bitwuzla)
    void pybitwuzla_set_term(
            Bitwuzla *bitwuzla, PyObject *fun, PyObject *state)

cdef extern from "bitwuzla.h":
    ctypedef struct BitwuzlaTerm:
        pass
    ctypedef struct Bitwuzla:
        pass
    ctypedef struct BitwuzlaSort:
        pass
    ctypedef enum BitwuzlaOption:
        pass
    cdef struct BitwuzlaOptionInfo_union_numeric:
        uint32_t cur_val
    cdef struct BitwuzlaOptionInfo_union_string:
        const char *cur_val;
    cdef union BitwuzlaOptionInfo_union:
        BitwuzlaOptionInfo_union_numeric numeric
        BitwuzlaOptionInfo_union_string string
    ctypedef struct BitwuzlaOptionInfo:
        bool is_numeric
        BitwuzlaOptionInfo_union_numeric numeric
        BitwuzlaOptionInfo_union_string string
    ctypedef enum BitwuzlaKind:
        pass
    ctypedef enum BitwuzlaBVBase:
        pass
    ctypedef enum BitwuzlaResult:
        pass
    ctypedef enum BitwuzlaRoundingMode:
        pass

# -------------------------------------------------------------------------- #
# Bitwuzla                                                                   #
# -------------------------------------------------------------------------- #

    Bitwuzla *bitwuzla_new() \
        except +raise_py_error
    void bitwuzla_delete(Bitwuzla *bitwuzla) \
        except +raise_py_error

    const char *bitwuzla_copyright(Bitwuzla *bitwuzla) \
        except +raise_py_error
    const char *bitwuzla_version(Bitwuzla *bitwuzla) \
        except +raise_py_error
    const char *bitwuzla_git_id(Bitwuzla *bitwuzla) \
        except +raise_py_error

    bool bitwuzla_terminate(Bitwuzla *bitwuzla) \
        except +raise_py_error
    void bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                           int32_t (*fun)(void *),
                                           void *state) \
        except +raise_py_error
    void *bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla) \
        except +raise_py_error

    void bitwuzla_set_abort_callback(void (*fun)(const char *msg)) \
        except +raise_py_error

    void bitwuzla_set_option(Bitwuzla *bitwuzla,
                             BitwuzlaOption option,
                             uint32_t val) \
        except +raise_py_error
    void bitwuzla_set_option_str(Bitwuzla *bitwuzla,
                                 BitwuzlaOption option,
                                 const char *val) \
        except +raise_py_error
    uint32_t bitwuzla_get_option(Bitwuzla *bitwuzla, BitwuzlaOption option) \
        except +raise_py_error

    void bitwuzla_get_option_info(Bitwuzla *bitwuzla,
                                  BitwuzlaOption option,
                                  BitwuzlaOptionInfo *info) \
        except +raise_py_error

    const BitwuzlaSort *bitwuzla_mk_array_sort(Bitwuzla *bitwuzla,
                                               const BitwuzlaSort *index,
                                               const BitwuzlaSort *element) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_mk_bool_sort(Bitwuzla *bitwuzla) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_mk_bv_sort(Bitwuzla *bitwuzla, uint32_t size) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_mk_fp_sort(Bitwuzla *bitwuzla,
                                            uint32_t exp_size,
                                            uint32_t sig_size) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_mk_fun_sort(Bitwuzla *bitwuzla,
                                             uint32_t arity,
                                             const BitwuzlaSort *domain[],
                                             const BitwuzlaSort *codomain) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_mk_rm_sort(Bitwuzla *bitwuzla) \
        except +raise_py_error

#    const BitwuzlaTerm *bitwuzla_mk_true(Bitwuzla *bitwuzla) \
#        except +raise_py_error
#    const BitwuzlaTerm *bitwuzla_mk_false(Bitwuzla *bitwuzla) \
#        except +raise_py_error

#    const BitwuzlaTerm *bitwuzla_mk_bv_zero(Bitwuzla *bitwuzla,
#                                      const BitwuzlaSort *sort) \
#        except +raise_py_error
#    const BitwuzlaTerm *bitwuzla_mk_bv_one(Bitwuzla *bitwuzla,
#                                     const BitwuzlaSort *sort) \
#        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_bv_ones(Bitwuzla *bitwuzla,
                                            const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_bv_min_signed(Bitwuzla *bitwuzla,
                                                  const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_bv_max_signed(Bitwuzla *bitwuzla,
                                                  const BitwuzlaSort *sort) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_fp_pos_zero(Bitwuzla *bitwuzla,
                                                const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_fp_neg_zero(Bitwuzla *bitwuzla,
                                                const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_fp_pos_inf(Bitwuzla *bitwuzla,
                                               const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_fp_neg_inf(Bitwuzla *bitwuzla,
                                               const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaTerm *bitwuzla_mk_fp_nan(Bitwuzla *bitwuzla,
                                           const BitwuzlaSort *sort) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_bv_value(Bitwuzla *bitwuzla,
                                             const BitwuzlaSort *sort,
                                             const char *value,
                                             BitwuzlaBVBase base) \
        except +raise_py_error

#    const BitwuzlaTerm *bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
#                                              const BitwuzlaSort *sort,
#                                              uint64_t value) \
#        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_fp_value(
            Bitwuzla *bitwuzla,
            const BitwuzlaTerm *bv_sign,
            const BitwuzlaTerm *bv_exponent,
            const BitwuzlaTerm *bv_significand) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_fp_value_from_real(
            Bitwuzla *bitwuzla,
            const BitwuzlaSort *sort,
            const BitwuzlaTerm *rm,
            const char *real) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_fp_value_from_rational(
            Bitwuzla *bitwuzla,
            const BitwuzlaSort *sort,
            const BitwuzlaTerm *rm,
            const char *num,
            const char *den) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_rm_value(Bitwuzla *bitwuzla,
                                             BitwuzlaRoundingMode rm) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_term1(Bitwuzla *bitwuzla,
                                          BitwuzlaKind kind,
                                          const BitwuzlaTerm *arg) \
        except +raise_py_error

#    const BitwuzlaTerm *bitwuzla_mk_term2(Bitwuzla *bitwuzla,
#                                          BitwuzlaKind kind,
#                                          const BitwuzlaTerm *arg0,
#                                          const BitwuzlaTerm *arg1) \
#        except +raise_py_error
#
#    const BitwuzlaTerm *bitwuzla_mk_term3(Bitwuzla *bitwuzla,
#                                          BitwuzlaKind kind,
#                                          const BitwuzlaTerm *arg0,
#                                          const BitwuzlaTerm *arg1,
#                                          const BitwuzlaTerm *arg2) \
#        except +raise_py_error
#
    const BitwuzlaTerm *bitwuzla_mk_term(Bitwuzla *bitwuzla,
                                   BitwuzlaKind kind,
                                   uint32_t argc,
                                   const BitwuzlaTerm *args[]) \
        except +raise_py_error

#    const BitwuzlaTerm *bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   const BitwuzlaTerm *arg,
#                                                   uint32_t idx) \
#        except +raise_py_error
#
#    const BitwuzlaTerm *bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   const BitwuzlaTerm *arg,
#                                                   uint32_t idx0,
#                                                   uint32_t idx1) \
#        except +raise_py_error
#
#    const BitwuzlaTerm *bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   const BitwuzlaTerm *arg0,
#                                                   const BitwuzlaTerm *arg1,
#                                                   uint32_t idx) \
#        except +raise_py_error
#
#    const BitwuzlaTerm *bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   const BitwuzlaTerm *arg0,
#                                                   const BitwuzlaTerm *arg1,
#                                                   uint32_t idx0,
#                                                   uint32_t idx1) \
#        except       +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_term_indexed(Bitwuzla *bitwuzla,
                                                 BitwuzlaKind kind,
                                                 uint32_t argc,
                                                 const BitwuzlaTerm *args[],
                                                 uint32_t idxc,
                                                 uint32_t idxs[]) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_const(Bitwuzla *bitwuzla,
                                         const BitwuzlaSort *sort,
                                         const char *symbol) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_const_array(Bitwuzla *bitwuzla,
                                                const BitwuzlaSort *sort,
                                                const BitwuzlaTerm *value) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_mk_var(Bitwuzla *bitwuzla,
                                        const BitwuzlaSort *sort,
                                        const char *symbol) \
        except +raise_py_error

    void bitwuzla_push(Bitwuzla *bitwuzla, uint32_t nlevels) \
        except +raise_py_error
    void bitwuzla_pop(Bitwuzla *bitwuzla, uint32_t nlevels) \
        except +raise_py_error

    void bitwuzla_assert(Bitwuzla *bitwuzla, const BitwuzlaTerm *term) \
        except +raise_py_error
    void bitwuzla_assume(Bitwuzla *bitwuzla, const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla,
                                      const BitwuzlaTerm *term) \
        except +raise_py_error

    const BitwuzlaTerm **bitwuzla_get_unsat_assumptions(
            Bitwuzla *bitwuzla, size_t *size) \
        except +raise_py_error
    const BitwuzlaTerm **bitwuzla_get_unsat_core(
            Bitwuzla *bitwuzla, size_t *size) \
        except +raise_py_error

    void bitwuzla_fixate_assumptions(Bitwuzla *bitwuzla) \
        except +raise_py_error
    void bitwuzla_reset_assumptions(Bitwuzla *bitwuzla) \
        except +raise_py_error

    BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla) \
        except +raise_py_error

    BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla) \
        except +raise_py_error

    const BitwuzlaTerm *bitwuzla_get_value(Bitwuzla *bitwuzla,
                                           const BitwuzlaTerm *term) \
        except +raise_py_error

    const char *bitwuzla_get_bv_value(Bitwuzla *bitwuzla,
                                      const BitwuzlaTerm *term) \
        except +raise_py_error

    void bitwuzla_get_fp_value(Bitwuzla *bitwuzla,
                               const BitwuzlaTerm *term,
                               const char **sign,
                               const char **exponent,
                               const char **significand) \
        except +raise_py_error

    const char *bitwuzla_get_rm_value(Bitwuzla *bitwuzla,
                                      const BitwuzlaTerm *term) \
        except +raise_py_error

    void bitwuzla_get_array_value(Bitwuzla *bitwuzla,
                                  const BitwuzlaTerm *term,
                                  const BitwuzlaTerm ***indices,
                                  const BitwuzlaTerm ***values,
                                  size_t *size,
                                  const BitwuzlaTerm **default_value) \
        except +raise_py_error

    void bitwuzla_get_fun_value(Bitwuzla *bitwuzla,
                                const BitwuzlaTerm *term,
                                const BitwuzlaTerm ****args,
                                size_t *arity,
                                const BitwuzlaTerm ***values,
                                size_t *size) \
        except +raise_py_error


    void bitwuzla_print_model(Bitwuzla *bitwuzla,
                              const char *format, FILE *file) \
        except +raise_py_error

    void bitwuzla_dump_formula(Bitwuzla *bitwuzla,
                               const char *format, FILE *file) \
        except +raise_py_error

#    BitwuzlaResult bitwuzla_parse(Bitwuzla *bitwuzla,
#                                  FILE *infile,
#                                  const char *infile_name,
#                                  FILE *outfile,
#                                  char **error_msg,
#                                  int32_t *parsed_status,
#                                  bool *parsed_smt2) \
#        except +raise_py_error
#
#    BitwuzlaResult bitwuzla_parse_format(Bitwuzla *bitwuzla,
#                                         const char *format,
#                                         FILE *infile,
#                                         const char *infile_name,
#                                         FILE *outfile,
#                                         char **error_msg,
#                                         int32_t *parsed_status) \
#        except +raise_py_error

    void bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
                                   size_t terms_size,
                                   const BitwuzlaTerm *terms[],
                                   size_t map_size,
                                   const BitwuzlaTerm *map_keys[],
                                   const BitwuzlaTerm *map_values[]) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
# BitwuzlaSort                                                               #
# -------------------------------------------------------------------------- #

    size_t bitwuzla_sort_hash(const BitwuzlaSort *sort) \
        except +raise_py_error

    uint32_t bitwuzla_sort_bv_get_size(const BitwuzlaSort *sort) \
        except +raise_py_error
    uint32_t bitwuzla_sort_fp_get_exp_size(const BitwuzlaSort *sort) \
        except +raise_py_error
    uint32_t bitwuzla_sort_fp_get_sig_size(const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_sort_array_get_index(
            const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_sort_array_get_element(
            const BitwuzlaSort *sort) \
        except +raise_py_error
    const BitwuzlaSort **bitwuzla_sort_fun_get_domain_sorts(
        const BitwuzlaSort *sort,
        size_t *size) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_sort_fun_get_codomain(
            const BitwuzlaSort *sort) \
        except +raise_py_error
    uint32_t bitwuzla_sort_fun_get_arity(const BitwuzlaSort *sort) \
        except +raise_py_error

    bool bitwuzla_sort_is_equal(const BitwuzlaSort *sort0,
                                const BitwuzlaSort *sort1) \
        except +raise_py_error
    bool bitwuzla_sort_is_array(const BitwuzlaSort *sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_bv(const BitwuzlaSort *sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_fp(const BitwuzlaSort *sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_fun(const BitwuzlaSort *sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_rm(const BitwuzlaSort *sort) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
# BitwuzlaTerm                                                               #
# -------------------------------------------------------------------------- #

    size_t bitwuzla_term_hash(const BitwuzlaTerm *term) \
        except +raise_py_error

    BitwuzlaKind bitwuzla_term_get_kind(const BitwuzlaTerm *term) \
        except +raise_py_error

    const BitwuzlaTerm **bitwuzla_term_get_children(const BitwuzlaTerm *term,
                                                    size_t *size) \
        except +raise_py_error

    uint32_t *bitwuzla_term_get_indices(const BitwuzlaTerm *term,
                                              size_t *size) \
        except +raise_py_error

    bool bitwuzla_term_is_indexed(const BitwuzlaTerm *term) \
        except +raise_py_error

#    Bitwuzla *bitwuzla_term_get_bitwuzla(const BitwuzlaTerm *term) \
#        except +raise_py_error
    const BitwuzlaSort *bitwuzla_term_get_sort(const BitwuzlaTerm *term) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_term_array_get_index_sort(
            const BitwuzlaTerm *term) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_term_array_get_element_sort(
            const BitwuzlaTerm *term) \
        except +raise_py_error
    const BitwuzlaSort **bitwuzla_term_fun_get_domain_sorts(
        const BitwuzlaTerm *term,
        size_t *size) \
        except +raise_py_error
    const BitwuzlaSort *bitwuzla_term_fun_get_codomain_sort(
            const BitwuzlaTerm *term) \
        except +raise_py_error

    uint32_t bitwuzla_term_bv_get_size(const BitwuzlaTerm *term) \
        except +raise_py_error
    uint32_t bitwuzla_term_fp_get_exp_size(const BitwuzlaTerm *term) \
        except +raise_py_error
    uint32_t bitwuzla_term_fp_get_sig_size(const BitwuzlaTerm *term) \
        except +raise_py_error
    uint32_t bitwuzla_term_fun_get_arity(const BitwuzlaTerm *term) \
        except +raise_py_error

    const char *bitwuzla_term_get_symbol(const BitwuzlaTerm *term) \
        except +raise_py_error
    void bitwuzla_term_set_symbol(
            const BitwuzlaTerm *term, const char *symbol) \
        except +raise_py_error

#    bool bitwuzla_term_is_equal_sort(const BitwuzlaTerm *term0,
#                                     const BitwuzlaTerm *term1) \
#        except +raise_py_error

    bool bitwuzla_term_is_array(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_const(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fun(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_var(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_bound_var(const BitwuzlaTerm *term) \
        except +raise_py_error

    bool bitwuzla_term_is_bv_value(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value(const BitwuzlaTerm *term) \
        except +raise_py_error

    bool bitwuzla_term_is_bv(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm(const BitwuzlaTerm *term) \
        except +raise_py_error

    bool bitwuzla_term_is_bv_value_zero(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_one(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_ones(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_min_signed(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_max_signed(const BitwuzlaTerm *term) \
        except +raise_py_error

    bool bitwuzla_term_is_fp_value_pos_zero(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_neg_zero(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_pos_inf(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_neg_inf(const BitwuzlaTerm *term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_nan(const BitwuzlaTerm *term) \
        except +raise_py_error

    bool bitwuzla_term_is_const_array(const BitwuzlaTerm *term) \
        except +raise_py_error

    void bitwuzla_term_dump(const BitwuzlaTerm *term,
                            const char *format,
                            FILE *file) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
