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
from libc.stdint cimport uint8_t, int32_t, uint32_t, uint64_t
from bitwuzla import BitwuzlaException

cdef inline int raise_py_error() except *:
    raise BitwuzlaException(
            py_bitwuzla_get_err_msg().decode('utf-8').split(':', 1)[1].strip())

cdef extern from "abort.h":
    void py_bitwuzla_abort_fun(const char* msg)
    const char * py_bitwuzla_get_err_msg()

cdef extern from "utils.h":
    void py_bitwuzla_delete(Bitwuzla *bitwuzla)
    void py_bitwuzla_set_term(
            Bitwuzla *bitwuzla, PyObject *fun, PyObject *state)

cdef extern from "bitwuzla/c/bitwuzla.h":
    ctypedef struct BitwuzlaTerm:
        pass
    ctypedef struct Bitwuzla:
        pass
    ctypedef struct BitwuzlaSort:
        pass
    ctypedef struct BitwuzlaOptions:
        pass
    cdef struct BitwuzlaOptionInfo_union_numeric:
        uint64_t cur
        uint64_t dflt
        uint64_t min
        uint64_t max
    cdef struct BitwuzlaOptionInfo_union_mode:
        const char *cur
        const char *dflt
        size_t num_modes
        char **modes
    cdef union BitwuzlaOptionInfo_union:
        BitwuzlaOptionInfo_union_numeric numeric
        BitwuzlaOptionInfo_union_mode mode
    ctypedef struct BitwuzlaOptionInfo:
        BitwuzlaOption opt
        const char *shrt
        const char *lng
        const char *desc
        bool is_numeric
        BitwuzlaOptionInfo_union_numeric numeric
        BitwuzlaOptionInfo_union_mode mode
    ctypedef enum BitwuzlaOption:
        pass
    ctypedef enum BitwuzlaKind:
        pass
    ctypedef enum BitwuzlaBVBase:
        pass
    ctypedef enum BitwuzlaResult:
        pass
    ctypedef enum BitwuzlaRoundingMode:
        pass

# -------------------------------------------------------------------------- #
# *_to_string                                                                #
# -------------------------------------------------------------------------- #

    const char *bitwuzla_result_to_string(BitwuzlaResult result) \
        except +raise_py_error
    const char *bitwuzla_rm_to_string(BitwuzlaRoundingMode rm) \
        except +raise_py_error
    const char *bitwuzla_kind_to_string(BitwuzlaKind kind) \
        except +raise_py_error
    const char *bitwuzla_term_to_string(BitwuzlaTerm term) \
        except +raise_py_error
    const char *bitwuzla_sort_to_string(BitwuzlaSort sort) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
# BitwuzlaOptions                                                            #
# -------------------------------------------------------------------------- #

    BitwuzlaOptions *bitwuzla_options_new() except +raise_py_error
    void bitwuzla_options_delete(BitwuzlaOptions *options) \
        except +raise_py_error
    bool bitwuzla_option_is_numeric(BitwuzlaOptions *options, \
                                    BitwuzlaOption option) \
        except +raise_py_error

    bool bitwuzla_option_is_mode(BitwuzlaOptions *options,
                                 BitwuzlaOption option) \
        except +raise_py_error

    void bitwuzla_set_option(BitwuzlaOptions *options,
                             BitwuzlaOption option,
                             uint32_t val) \
        except +raise_py_error

    void bitwuzla_set_option_mode(BitwuzlaOptions *options,
                                 BitwuzlaOption option,
                                 const char *val) \
        except +raise_py_error
    uint32_t bitwuzla_get_option(BitwuzlaOptions *options, BitwuzlaOption option) \
        except +raise_py_error

    void bitwuzla_get_option_info(BitwuzlaOptions *options,
                                  BitwuzlaOption option,
                                  BitwuzlaOptionInfo *info) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
# Library info                                                               #
# -------------------------------------------------------------------------- #

    const char *bitwuzla_copyright() except +raise_py_error
    const char *bitwuzla_version() except +raise_py_error
    const char *bitwuzla_git_id() except +raise_py_error

# -------------------------------------------------------------------------- #
# Bitwuzla                                                                   #
# -------------------------------------------------------------------------- #

    Bitwuzla *bitwuzla_new(const BitwuzlaOptions *options) \
        except +raise_py_error
    void bitwuzla_delete(Bitwuzla *bitwuzla) \
        except +raise_py_error
    void bitwuzla_reset(Bitwuzla *bitwuzla) \
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

    BitwuzlaSort bitwuzla_mk_array_sort(BitwuzlaSort index,
                                        BitwuzlaSort element) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_mk_bool_sort() \
        except +raise_py_error
    BitwuzlaSort bitwuzla_mk_bv_sort(uint64_t size) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_mk_fp_sort(uint64_t exp_size,
                                     uint64_t sig_size) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_mk_fun_sort(uint64_t arity,
                                      BitwuzlaSort domain[],
                                      BitwuzlaSort codomain) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_mk_rm_sort() \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_true() \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_false() \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_bv_zero(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_bv_one(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_bv_ones(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_bv_min_signed(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_bv_max_signed(BitwuzlaSort sort) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_fp_pos_zero(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_fp_neg_zero(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_fp_pos_inf(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_fp_neg_inf(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaTerm bitwuzla_mk_fp_nan(BitwuzlaSort sort) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_bv_value(BitwuzlaSort sort,
                                      const char *value,
                                      uint8_t base) \
        except +raise_py_error

#    BitwuzlaTerm bitwuzla_mk_bv_value_uint64(Bitwuzla *bitwuzla,
#                                              BitwuzlaSort sort,
#                                              uint64_t value) \
#        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_fp_value(
            BitwuzlaTerm bv_sign,
            BitwuzlaTerm bv_exponent,
            BitwuzlaTerm bv_significand) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_fp_from_real(
            BitwuzlaSort sort,
            BitwuzlaTerm rm,
            const char *real) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_fp_from_rational(
            BitwuzlaSort sort,
            BitwuzlaTerm rm,
            const char *num,
            const char *den) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_rm_value(BitwuzlaRoundingMode rm) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_term1(BitwuzlaKind kind,
                                   BitwuzlaTerm arg) \
        except +raise_py_error

#    BitwuzlaTerm bitwuzla_mk_term2(Bitwuzla *bitwuzla,
#                                          BitwuzlaKind kind,
#                                          BitwuzlaTerm arg0,
#                                          BitwuzlaTerm arg1) \
#        except +raise_py_error
#
#    BitwuzlaTerm bitwuzla_mk_term3(Bitwuzla *bitwuzla,
#                                          BitwuzlaKind kind,
#                                          BitwuzlaTerm arg0,
#                                          BitwuzlaTerm arg1,
#                                          BitwuzlaTerm arg2) \
#        except +raise_py_error
#
    BitwuzlaTerm bitwuzla_mk_term(BitwuzlaKind kind,
                                  uint32_t argc,
                                  BitwuzlaTerm args[]) \
        except +raise_py_error

#    BitwuzlaTerm bitwuzla_mk_term1_indexed1(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   BitwuzlaTerm arg,
#                                                   uint32_t idx) \
#        except +raise_py_error
#
#    BitwuzlaTerm bitwuzla_mk_term1_indexed2(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   BitwuzlaTerm arg,
#                                                   uint32_t idx0,
#                                                   uint32_t idx1) \
#        except +raise_py_error
#
#    BitwuzlaTerm bitwuzla_mk_term2_indexed1(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   BitwuzlaTerm arg0,
#                                                   BitwuzlaTerm arg1,
#                                                   uint32_t idx) \
#        except +raise_py_error
#
#    BitwuzlaTerm bitwuzla_mk_term2_indexed2(Bitwuzla *bitwuzla,
#                                                   BitwuzlaKind kind,
#                                                   BitwuzlaTerm arg0,
#                                                   BitwuzlaTerm arg1,
#                                                   uint32_t idx0,
#                                                   uint32_t idx1) \
#        except       +raise_py_error

    BitwuzlaTerm bitwuzla_mk_term_indexed(BitwuzlaKind kind,
                                          uint32_t argc,
                                          BitwuzlaTerm args[],
                                          uint32_t idxc,
                                          uint64_t idxs[]) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_const(BitwuzlaSort sort,
                                   const char *symbol) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_const_array(BitwuzlaSort sort,
                                         BitwuzlaTerm value) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_mk_var(BitwuzlaSort sort,
                                 const char *symbol) \
        except +raise_py_error

    void bitwuzla_push(Bitwuzla *bitwuzla, uint64_t nlevels) \
        except +raise_py_error
    void bitwuzla_pop(Bitwuzla *bitwuzla, uint64_t nlevels) \
        except +raise_py_error

    void bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla,
                                      BitwuzlaTerm term) \
        except +raise_py_error

    BitwuzlaTerm *bitwuzla_get_unsat_assumptions(
            Bitwuzla *bitwuzla, size_t *size) \
        except +raise_py_error
    BitwuzlaTerm *bitwuzla_get_unsat_core(
            Bitwuzla *bitwuzla, size_t *size) \
        except +raise_py_error

    BitwuzlaResult bitwuzla_simplify(Bitwuzla *bitwuzla) \
        except +raise_py_error

    BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla) \
        except +raise_py_error

    BitwuzlaResult bitwuzla_check_sat_assuming(Bitwuzla *bitwuzla,
                                               uint32_t argc,
                                               BitwuzlaTerm args[]) \
        except +raise_py_error

    BitwuzlaTerm bitwuzla_get_value(Bitwuzla *bitwuzla,
                                           BitwuzlaTerm term) \
        except +raise_py_error

    const char *bitwuzla_get_bv_value(Bitwuzla *bitwuzla,
                                      BitwuzlaTerm term,
                                      uint8_t base) \
        except +raise_py_error

    void bitwuzla_get_fp_value(Bitwuzla *bitwuzla,
                               BitwuzlaTerm term,
                               const char **sign,
                               const char **exponent,
                               const char **significand,
                               uint8_t base) \
        except +raise_py_error

    BitwuzlaRoundingMode bitwuzla_get_rm_value(Bitwuzla *bitwuzla,
                                      BitwuzlaTerm term) \
        except +raise_py_error

#    void bitwuzla_get_array_value(Bitwuzla *bitwuzla,
#                                  BitwuzlaTerm term,
#                                  BitwuzlaTerm **indices,
#                                  BitwuzlaTerm **values,
#                                  size_t *size,
#                                  BitwuzlaTerm *default_value) \
#        except +raise_py_error
#
#    void bitwuzla_get_fun_value(Bitwuzla *bitwuzla,
#                                BitwuzlaTerm term,
#                                BitwuzlaTerm ***args,
#                                size_t *arity,
#                                BitwuzlaTerm **values,
#                                size_t *size) \
#        except +raise_py_error


#    void bitwuzla_print_model(Bitwuzla *bitwuzla,
#                              const char *format, FILE *file) \
#        except +raise_py_error

#    void bitwuzla_dump_formula(Bitwuzla *bitwuzla,
#                               const char *format, FILE *file) \
#        except +raise_py_error

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

#    void bitwuzla_substitute_terms(Bitwuzla *bitwuzla,
#                                   size_t terms_size,
#                                   BitwuzlaTerm terms[],
#                                   size_t map_size,
#                                   BitwuzlaTerm map_keys[],
#                                   BitwuzlaTerm map_values[]) \
#        except +raise_py_error

# -------------------------------------------------------------------------- #
# BitwuzlaSort                                                               #
# -------------------------------------------------------------------------- #

    size_t bitwuzla_sort_hash(BitwuzlaSort sort) \
        except +raise_py_error

    uint64_t bitwuzla_sort_bv_get_size(BitwuzlaSort sort) \
        except +raise_py_error
    uint64_t bitwuzla_sort_fp_get_exp_size(BitwuzlaSort sort) \
        except +raise_py_error
    uint64_t bitwuzla_sort_fp_get_sig_size(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_sort_array_get_index(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_sort_array_get_element(BitwuzlaSort sort) \
        except +raise_py_error
    BitwuzlaSort *bitwuzla_sort_fun_get_domain_sorts(
        BitwuzlaSort sort,
        size_t *size) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_sort_fun_get_codomain(
            BitwuzlaSort sort) \
        except +raise_py_error
    uint64_t bitwuzla_sort_fun_get_arity(BitwuzlaSort sort) \
        except +raise_py_error
    const char *bitwuzla_sort_get_uninterpreted_symbol(BitwuzlaSort sort) \
        except +raise_py_error

    bool bitwuzla_sort_is_equal(BitwuzlaSort sort0, BitwuzlaSort sort1) \
        except +raise_py_error
    bool bitwuzla_sort_is_array(BitwuzlaSort sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_bv(BitwuzlaSort sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_fp(BitwuzlaSort sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_fun(BitwuzlaSort sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_rm(BitwuzlaSort sort) \
        except +raise_py_error
    bool bitwuzla_sort_is_uninterpreted(BitwuzlaSort sort) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
# BitwuzlaTerm#
# -------------------------------------------------------------------------- #

    size_t bitwuzla_term_hash(BitwuzlaTerm term) \
        except +raise_py_error

    BitwuzlaKind bitwuzla_term_get_kind(BitwuzlaTerm term) \
        except +raise_py_error

    BitwuzlaTerm *bitwuzla_term_get_children(BitwuzlaTerm term,
                                                    size_t *size) \
        except +raise_py_error

    uint64_t *bitwuzla_term_get_indices(BitwuzlaTerm term,
                                              size_t *size) \
        except +raise_py_error

    bool bitwuzla_term_is_indexed(BitwuzlaTerm term) \
        except +raise_py_error

#    Bitwuzla *bitwuzla_term_get_bitwuzla(BitwuzlaTerm term) \
#        except +raise_py_error
    BitwuzlaSort bitwuzla_term_get_sort(BitwuzlaTerm term) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_term_array_get_index_sort(
            BitwuzlaTerm term) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_term_array_get_element_sort(
            BitwuzlaTerm term) \
        except +raise_py_error
    BitwuzlaSort *bitwuzla_term_fun_get_domain_sorts(
        BitwuzlaTerm term,
        size_t *size) \
        except +raise_py_error
    BitwuzlaSort bitwuzla_term_fun_get_codomain_sort(
            BitwuzlaTerm term) \
        except +raise_py_error

    uint64_t bitwuzla_term_bv_get_size(BitwuzlaTerm term) \
        except +raise_py_error
    uint64_t bitwuzla_term_fp_get_exp_size(BitwuzlaTerm term) \
        except +raise_py_error
    uint64_t bitwuzla_term_fp_get_sig_size(BitwuzlaTerm term) \
        except +raise_py_error
    uint64_t bitwuzla_term_fun_get_arity(BitwuzlaTerm term) \
        except +raise_py_error

    const char *bitwuzla_term_get_symbol(BitwuzlaTerm term) \
        except +raise_py_error
    #void bitwuzla_term_set_symbol(
    #        BitwuzlaTerm term, const char *symbol) \
    #    except +raise_py_error

#    bool bitwuzla_term_is_equal_sort(BitwuzlaTerm term0,
#                                     BitwuzlaTerm term1) \
#        except +raise_py_error

    bool bitwuzla_term_is_array(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_const(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fun(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_var(BitwuzlaTerm term) \
        except +raise_py_error
    #bool bitwuzla_term_is_bound_var(BitwuzlaTerm term) \
    #    except +raise_py_error

    bool bitwuzla_term_is_value(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value(BitwuzlaTerm term) \
        except +raise_py_error

    bool bitwuzla_term_is_bool(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_uninterpreted(BitwuzlaTerm term) \
        except +raise_py_error

    bool bitwuzla_term_is_bv_value_zero(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_one(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_ones(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm term) \
        except +raise_py_error

    bool bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_fp_value_nan(BitwuzlaTerm term) \
        except +raise_py_error

    bool bitwuzla_term_is_rm_value_rna(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value_rne(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value_rtn(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value_rtp(BitwuzlaTerm term) \
        except +raise_py_error
    bool bitwuzla_term_is_rm_value_rtz(BitwuzlaTerm term) \
        except +raise_py_error

    bool bitwuzla_term_is_const_array(BitwuzlaTerm term) \
        except +raise_py_error

    void bitwuzla_term_dump(BitwuzlaTerm term,
                            const char *format,
                            FILE *file) \
        except +raise_py_error

# -------------------------------------------------------------------------- #
