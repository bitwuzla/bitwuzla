/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_C_H_INCLUDED
#define BITWUZLA_API_C_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

/* -------------------------------------------------------------------------- */

#if __cplusplus
extern "C" {
#endif

#define BITWUZLA_API_USE_C_ENUMS
#include <bitwuzla/enums.h>
#include <bitwuzla/option.h>
#undef BITWUZLA_API_USE_C_ENUMS

/* -------------------------------------------------------------------------- */
/* Library info                                                               */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_libinfo
 *  @{
 */

/**
 * Get copyright information.
 */
const char *bitwuzla_copyright();

/**
 * Get version information.
 */
const char *bitwuzla_version();

/**
 * Get git information.
 */
const char *bitwuzla_git_id();

/** @} */

/* -------------------------------------------------------------------------- */
/* BitwuzlaOptionInfo                                                         */
/* -------------------------------------------------------------------------- */

/**
 * The option info struct holds all information about an option, which can
 * be queried via `bitwuzla_get_option_info`.
 *
 * @see
 *   * `bitwuzla_get_option_info`
 */
struct BitwuzlaOptionInfo
{
  /** The Bitwuzla option. */
  BitwuzlaOption opt;
  /** Short option name. */
  const char *shrt;
  /** Long option name. */
  const char *lng;
  /** Option description. */
  const char *description;
  /** Indicates whether values are numeric or strings. */
  bool is_numeric;

  struct NumericValue
  {
    /** Current numeric option value. */
    uint64_t cur;
    /** Default numeric option value. */
    uint64_t dflt;
    /** Minimum numeric option value. */
    uint64_t min;
    /** Maximum numeric option value. */
    uint64_t max;
  };

  struct ModeValue
  {
    /** Current mode option value. */
    const char *cur;
    /** Default mode option value. */
    const char *dflt;
    /** Number of available modes. */
    size_t num_modes;
    /** List of available modes. */
    const char **modes;
  };

  union
  {
    struct NumericValue numeric;
    struct ModeValue mode;
  };
};

#ifndef DOXYGEN_SKIP
typedef struct BitwuzlaOptionInfo BitwuzlaOptionInfo;
#endif

/* -------------------------------------------------------------------------- */
/* BitwuzlaOptions                                                            */
/* -------------------------------------------------------------------------- */

/** The Bitwuzla configuration options. */
typedef struct BitwuzlaOptions BitwuzlaOptions;

/** \addtogroup c_bitwuzlaoptions
 *  @{
 */

/**
 * Create a new BitwuzlaOptions instance.
 *
 * The returned instance must be deleted via `bitwuzla_options_delete()`.
 *
 * @return A pointer to the created BitwuzlaOptions instance.
 *
 * @see
 *   * `bitwuzla_options_delete`
 */
BitwuzlaOptions *bitwuzla_options_new();

/**
 * Delete a BitwuzlaOptions instance.
 *
 * The given instance must have been created via `bitwuzla_options_new()`.
 *
 * @param options The BitwuzlaOptions instance to delete.
 *
 * @see
 *   * `bitwuzla_options_new`
 */
void bitwuzla_options_delete(BitwuzlaOptions *options);

/**
 * Determine if given string is a valid short or long option name.
 * @param name The name.
 * @return True if given string is a option name.
 */
bool bitwuzla_option_is_valid(BitwuzlaOptions *options, const char *name);

/**
 * Determine if a given option is a numeric (or Boolean) option.
 * @return True if the given option is a numeric or Boolean option.
 */
bool bitwuzla_option_is_numeric(BitwuzlaOptions *options,
                                BitwuzlaOption option);
/**
 * Determine if a given option is an option with a mode
 * @return True if the given option is an option with a mode.
 */
bool bitwuzla_option_is_mode(BitwuzlaOptions *options, BitwuzlaOption option);

/**
 * Set option.
 *
 * @param options The Bitwuzla options instance.
 * @param option The option.
 * @param val The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 *   * `bitwuzla_get_option`
 */
void bitwuzla_set_option(BitwuzlaOptions *options,
                         BitwuzlaOption option,
                         uint64_t val);

/**
 * Set option mode for options with modes.
 *
 * @param options The Bitwuzla options instance.
 * @param option The option.
 * @param val The option string value.
 *
 * @see
 *   * `BitwuzlaOption`
 *   * `bitwuzla_get_option_mode`
 */
void bitwuzla_set_option_mode(BitwuzlaOptions *options,
                              BitwuzlaOption option,
                              const char *val);

/**
 * Get the current value of an option.
 *
 * @param options The Bitwuzla options instance.
 * @param option The option.
 *
 * @return The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 */
uint64_t bitwuzla_get_option(BitwuzlaOptions *options, BitwuzlaOption option);

/**
 * Get the current mode of an option as a string if option has modes.
 *
 * @param options The Bitwuzla options instance.
 * @param option The option.
 *
 * @return The option value.
 *
 * @see
 *   * `BitwuzlaOption`
 *   * `bitwuzla_set_option_mode`
 */
const char *bitwuzla_get_option_mode(BitwuzlaOptions *options,
                                     BitwuzlaOption option);

/**
 * Get the details of an option.
 *
 * @param options The Bitwuzla options instance.
 * @param option The option.
 * @param info The option info to populate, will be valid until the next
 *             `bitwuzla_get_option_info` call.
 *
 * @see
 *   * `BitwuzlaOptionInfo`
 */
void bitwuzla_get_option_info(BitwuzlaOptions *options,
                              BitwuzlaOption option,
                              BitwuzlaOptionInfo *info);

/** @} */

/* -------------------------------------------------------------------------- */
/* BitwuzlaResult (Satisfiability Result)                                     */
/* -------------------------------------------------------------------------- */

// Note: The BitwuzlaResult enum is defined in api/enums.h.

/**
 * Get the string representation of a result.
 * @return A string representation of the given result.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_result_to_string` call.
 */
const char *bitwuzla_result_to_string(BitwuzlaResult result);

/* -------------------------------------------------------------------------- */
/* BitwuzlaRoundingMode                                                       */
/* -------------------------------------------------------------------------- */

// Note: The BitwuzlaRoundingMode enum is defined in api/enums.h.

/**
 * Get the string representation of a rounding mode.
 * @return A string representation of the rounding mode.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_rm_to_string` call.
 */
const char *bitwuzla_rm_to_string(BitwuzlaRoundingMode rm);

/* -------------------------------------------------------------------------- */
/* BitwuzlaKind (Term Kind)                                                   */
/* -------------------------------------------------------------------------- */

// Note: The BitwuzlaKind enum is defined in api/enums.h.

/**
 * Get the string representation of a term kind.
 * @return A string representation of the given term kind.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_kind_to_string` call.
 */
const char *bitwuzla_kind_to_string(BitwuzlaKind kind);

/* -------------------------------------------------------------------------- */
/* BitwuzlaSort                                                               */
/* -------------------------------------------------------------------------- */

/** A Bitwuzla sort. */
typedef uint64_t BitwuzlaSort;

/** \addtogroup c_bitwuzlasort
 *  @{
 */

/**
 * Compute the hash value for a sort.
 *
 * @param sort The sort.
 *
 * @return The hash value of the sort.
 */
size_t bitwuzla_sort_hash(BitwuzlaSort sort);

/**
 * Get the size of a bit-vector sort.
 *
 * Requires that given sort is a bit-vector sort.
 *
 * @param sort The sort.
 *
 * @return The size of the bit-vector sort.
 */
uint64_t bitwuzla_sort_bv_get_size(BitwuzlaSort sort);

/**
 * Get the exponent size of a floating-point sort.
 *
 * Requires that given sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return The exponent size of the floating-point sort.
 */
uint64_t bitwuzla_sort_fp_get_exp_size(BitwuzlaSort sort);

/**
 * Get the significand size of a floating-point sort.
 *
 * Requires that given sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return The significand size of the floating-point sort.
 */
uint64_t bitwuzla_sort_fp_get_sig_size(BitwuzlaSort sort);

/**
 * Get the index sort of an array sort.
 *
 * Requires that given sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return The index sort of the array sort.
 */
BitwuzlaSort bitwuzla_sort_array_get_index(BitwuzlaSort sort);

/**
 * Get the element sort of an array sort.
 *
 * Requires that given sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return The element sort of the array sort.
 */
BitwuzlaSort bitwuzla_sort_array_get_element(BitwuzlaSort sort);

/**
 * Get the domain sorts of a function sort.
 *
 * The domain sorts are returned as an array of sorts of size `size`.
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 * @param size The size of the returned array.
 *
 * @return The domain sorts of the function sort.
 */
BitwuzlaSort *bitwuzla_sort_fun_get_domain_sorts(BitwuzlaSort sort,
                                                 size_t *size);

/**
 * Get the codomain sort of a function sort.
 *
 * Requires that given sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return The codomain sort of the function sort.
 */
BitwuzlaSort bitwuzla_sort_fun_get_codomain(BitwuzlaSort sort);

/**
 * Get the arity of a function sort.
 *
 * @param sort The sort.
 *
 * @return The number of arguments of the function sort.
 */
uint64_t bitwuzla_sort_fun_get_arity(BitwuzlaSort sort);

/**
 * Get the symbol of an uninterpreted sort.
 * @param sort The sort.
 * @return The symbol; NULL if no symbol is defined.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_sort_uninterpreted_get_symbol` call.
 */
const char *bitwuzla_sort_get_uninterpreted_symbol(BitwuzlaSort sort);

/**
 * Determine if two sorts are equal.
 *
 * @param sort0 The first sort.
 * @param sort1 The second sort.
 *
 * @return True if the given sorts are equal.
 */
bool bitwuzla_sort_is_equal(BitwuzlaSort sort0, BitwuzlaSort sort1);

/**
 * Determine if a sort is an array sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is an array sort.
 */
bool bitwuzla_sort_is_array(BitwuzlaSort sort);

/**
 * Determine if a sort is a Boolean sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a Boolean sort.
 */
bool bitwuzla_sort_is_bool(BitwuzlaSort sort);

/**
 * Determine if a sort is a bit-vector sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a bit-vector sort.
 */
bool bitwuzla_sort_is_bv(BitwuzlaSort sort);

/**
 * Determine if a sort is a floating-point sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a floating-point sort.
 */
bool bitwuzla_sort_is_fp(BitwuzlaSort sort);

/**
 * Determine if a sort is a function sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a function sort.
 */
bool bitwuzla_sort_is_fun(BitwuzlaSort sort);

/**
 * Determine if a sort is a Roundingmode sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a Roundingmode sort.
 */
bool bitwuzla_sort_is_rm(BitwuzlaSort sort);

/**
 * Determine if a sort is an uninterpreted sort.
 *
 * @param sort The sort.
 *
 * @return True if `sort` is a uninterpreted sort.
 */
bool bitwuzla_sort_is_uninterpreted(BitwuzlaSort sort);

/**
 * Get the SMT-LIBV v2 string representation of a sort.
 * @return A string representation of the given sort.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_sort_to_string` call.
 */
const char *bitwuzla_sort_to_string(BitwuzlaSort sort);

/**
 * Print sort to given file in SMT-LIB v2 format.
 *
 * @param sort The sort.
 * @param file The file to print the sort to.
 */
void bitwuzla_sort_print(BitwuzlaSort sort, FILE *file);

/** @} */

/* -------------------------------------------------------------------------- */
/* BitwuzlaTerm                                                               */
/* -------------------------------------------------------------------------- */

/** A Bitwuzla term. */
typedef uint64_t BitwuzlaTerm;

/** \addtogroup c_bitwuzlaterm
 *  @{
 */

/**
 * Compute the hash value for a term.
 *
 * @param term The term.
 *
 * @return The hash value of the term.
 */
size_t bitwuzla_term_hash(BitwuzlaTerm term);

/**
 * Get the kind of a term.
 *
 * @param term The term.
 *
 * @return The kind of the given term.
 *
 * @see BitwuzlaKind
 */
BitwuzlaKind bitwuzla_term_get_kind(BitwuzlaTerm term);

/**
 * Get the child terms of a term.
 *
 * Returns \c NULL if given term does not have children.
 *
 * @param term The term.
 * @param size Output parameter, stores the number of children of `term`.
 *
 * @return The children of `term` as an array of terms.
 */
BitwuzlaTerm *bitwuzla_term_get_children(BitwuzlaTerm term, size_t *size);

/**
 * Get the indices of an indexed term.
 *
 * Requires that given term is an indexed term.
 *
 * @param term The term.
 * @param size Output parameter, stores the number of indices of `term`.
 *
 * @return The indices of `term` as an array of indices.
 */
uint64_t *bitwuzla_term_get_indices(BitwuzlaTerm term, size_t *size);

/**
 * Determine if a term is an indexed term.
 *
 * @param term The term.
 *
 * @return True if `term` is an indexed term.
 */
bool bitwuzla_term_is_indexed(BitwuzlaTerm term);

/**
 * Get the sort of a term.
 *
 * @param term The term.
 *
 * @return The sort of the term.
 */
BitwuzlaSort bitwuzla_term_get_sort(BitwuzlaTerm term);

/**
 * Get the index sort of an array term.
 *
 * Requires that given term is an array or an array store term.
 *
 * @param term The term.
 *
 * @return The index sort of the array term.
 */
BitwuzlaSort bitwuzla_term_array_get_index_sort(BitwuzlaTerm term);

/**
 * Get the element sort of an array term.
 *
 * Requires that given term is an array or an array store term.
 *
 * @param term The term.
 *
 * @return The element sort of the array term.
 */
BitwuzlaSort bitwuzla_term_array_get_element_sort(BitwuzlaTerm term);

/**
 * Get the domain sorts of a function term.
 *
 * The domain sorts are returned as an array of sorts of size `size.
 * Requires that given term is an uninterpreted function, a lambda term, an
 * array store term, or an ite term over function terms.
 *
 * @param term The term.
 * @param size The size of the returned array. Optional, NULL is allowed.
 *
 * @return The domain sorts of the function term.
 */
BitwuzlaSort *bitwuzla_term_fun_get_domain_sorts(BitwuzlaTerm term,
                                                 size_t *size);

/**
 * Get the codomain sort of a function term.
 *
 * Requires that given term is an uninterpreted function, a lambda term, an
 * array store term, or an ite term over function terms.
 *
 * @param term The term.
 *
 * @return The codomain sort of the function term.
 */
BitwuzlaSort bitwuzla_term_fun_get_codomain_sort(BitwuzlaTerm term);

/**
 * Get the bit-width of a bit-vector term.
 *
 * Requires that given term is a bit-vector term.
 *
 * @param term The term.
 *
 * @return The bit-width of the bit-vector term.
 */
uint64_t bitwuzla_term_bv_get_size(BitwuzlaTerm term);

/**
 * Get the bit-width of the exponent of a floating-point term.
 *
 * Requires that given term is a floating-point term.
 *
 * @param term The term.
 *
 * @return The bit-width of the exponent of the floating-point term.
 */
uint64_t bitwuzla_term_fp_get_exp_size(BitwuzlaTerm term);

/**
 * Get the bit-width of the significand of a floating-point term.
 *
 * Requires that given term is a floating-point term.
 *
 * @param term The term.
 *
 * @return The bit-width of the significand of the floating-point term.
 */
uint64_t bitwuzla_term_fp_get_sig_size(BitwuzlaTerm term);

/**
 * Get the arity of a function term.
 *
 * Requires that given term is a function term.
 *
 * @param term The term.
 *
 * @return The arity of the function term.
 */
uint64_t bitwuzla_term_fun_get_arity(BitwuzlaTerm term);

/**
 * Get the symbol of a term.
 *
 * @param term The term.
 *
 * @return The symbol of `term`. \c NULL if no symbol is defined.
 */
const char *bitwuzla_term_get_symbol(BitwuzlaTerm term);

/**
 * Determine if the sorts of two terms are equal.
 *
 * @param term0 The first term.
 * @param term1 The second term.
 *
 * @return True if the sorts of `term0` and `term1` are equal.
 */
bool bitwuzla_term_is_equal_sort(BitwuzlaTerm term0, BitwuzlaTerm term1);

/**
 * Determine if a term is an array term.
 *
 * @param term The term.
 *
 * @return True if `term` is an array term.
 */
bool bitwuzla_term_is_array(BitwuzlaTerm term);

/**
 * Determine if a term is a constant.
 *
 * @param term The term.
 *
 * @return True if `term` is a constant.
 */
bool bitwuzla_term_is_const(BitwuzlaTerm term);

/**
 * Determine if a term is a function.
 *
 * @param term The term.
 *
 * @return True if `term` is a function.
 */
bool bitwuzla_term_is_fun(BitwuzlaTerm term);

/**
 * Determine if a term is a variable.
 *
 * @param term The term.
 *
 * @return True if `term` is a variable.
 */
bool bitwuzla_term_is_var(BitwuzlaTerm term);

/**
 * Determine if a term is a value.
 *
 * @param term The term.
 *
 * @return True if `term` is a value.
 */
bool bitwuzla_term_is_value(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value.
 */
bool bitwuzla_term_is_bv_value(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point value.
 */
bool bitwuzla_term_is_fp_value(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode value.
 */
bool bitwuzla_term_is_rm_value(BitwuzlaTerm term);

/**
 * Determine if a term is a Boolean term.
 *
 * @param term The term.
 *
 * @return True if `term` is a Boolean term.
 */
bool bitwuzla_term_is_bool(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector term.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector term.
 */
bool bitwuzla_term_is_bv(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point term.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point term.
 */
bool bitwuzla_term_is_fp(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode term.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode term.
 */
bool bitwuzla_term_is_rm(BitwuzlaTerm term);

/**
 * Determine if a term is a term of uninterpreted sort.
 *
 * @param term The term.
 *
 * @return True if `term` is a term of uninterpreted sort.
 */
bool bitwuzla_term_is_uninterpreted(BitwuzlaTerm term);

/**
 * Determine if a term is Boolean value true.
 *
 * @param term The term.
 *
 * @return True if `term` is a Boolean value true.
 */
bool bitwuzla_term_is_true(BitwuzlaTerm term);

/**
 * Determine if a term is Boolean value false.
 *
 * @param term The term.
 *
 * @return false if `term` is a Boolean value false.
 */
bool bitwuzla_term_is_false(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector value representing zero.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector zero value.
 */
bool bitwuzla_term_is_bv_value_zero(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector value representing one.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector one value.
 */
bool bitwuzla_term_is_bv_value_one(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector value with all bits set to one.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with all bits set to one.
 */
bool bitwuzla_term_is_bv_value_ones(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector minimum signed value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with the most significant bit
 *         set to 1 and all other bits set to 0.
 */
bool bitwuzla_term_is_bv_value_min_signed(BitwuzlaTerm term);

/**
 * Determine if a term is a bit-vector maximum signed value.
 *
 * @param term The term.
 *
 * @return True if `term` is a bit-vector value with the most significant bit
 *         set to 0 and all other bits set to 1.
 */
bool bitwuzla_term_is_bv_value_max_signed(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point positive zero (+zero) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point +zero value.
 */
bool bitwuzla_term_is_fp_value_pos_zero(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point value negative zero (-zero).
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point value negative zero.
 */
bool bitwuzla_term_is_fp_value_neg_zero(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point positive infinity (+oo) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point +oo value.
 */
bool bitwuzla_term_is_fp_value_pos_inf(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point negative infinity (-oo) value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point -oo value.
 */
bool bitwuzla_term_is_fp_value_neg_inf(BitwuzlaTerm term);

/**
 * Determine if a term is a floating-point NaN value.
 *
 * @param term The term.
 *
 * @return True if `term` is a floating-point NaN value.
 */
bool bitwuzla_term_is_fp_value_nan(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode RNA value.
 *
 * @param term The term.
 *
 * @return True if `term` is a roundindg mode RNA value.
 */
bool bitwuzla_term_is_rm_value_rna(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode RNE value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RNE value.
 */
bool bitwuzla_term_is_rm_value_rne(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode RTN value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTN value.
 */
bool bitwuzla_term_is_rm_value_rtn(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode RTP value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTP value.
 */
bool bitwuzla_term_is_rm_value_rtp(BitwuzlaTerm term);

/**
 * Determine if a term is a rounding mode RTZ value.
 *
 * @param term The term.
 *
 * @return True if `term` is a rounding mode RTZ value.
 */
bool bitwuzla_term_is_rm_value_rtz(BitwuzlaTerm term);

/**
 * Get Boolean representation of given Boolean value term.
 *
 * @param term The Boolean value term.
 * @return Boolean representation of value term.
 */
bool bitwuzla_term_value_get_bool(BitwuzlaTerm term);

/**
 * Get string representation of Boolean, bit-vector, floating-point, or
 * rounding mode value term.
 *
 * This returns the raw value string (as opposed to bitwuzla_term_to_string(),
 * which returns the SMT-LIB v2 representation of a term).
 * For example, this function returns "010" for a bit-vector value 2 of size
 * 3, while bitwuzla_term_to_string() returns "#b010".
 *
 * @note This uses default binary format for bit-vector value strings.
 *
 * @param term The value term.
 * @return The string representation of the value term.
 *
 * @note Return value is valid until next `bitwuzla_term_value_get_str` call.
 */
const char *bitwuzla_term_value_get_str(BitwuzlaTerm term);

/**
 * Get string representation of Boolean, bit-vector, floating-point, or
 * rounding mode value term. String representations of bit-vector values are
 * printed in the given base.
 *
 * This returns the raw value string (as opposed to bitwuzla_term_to_string(),
 * which returns the SMT-LIB v2 representation of a term).
 * For example, this function returns "010" for a bit-vector value 2 of size
 * 3, while bitwuzla_term_to_string() returns "#b010".
 *
 * @param term The value term.
 * @param base The base of the string representation of bit-vector values; `2`
 *             for binary, `10` for decimal, and `16` for hexadecimal. Always
 *             ignored for Boolean and RoundingMode values.
 * @return String representation of the value term.
 *
 * @note The returned string for floating-point values is always the binary
 *       IEEE-754 representation of the value (parameter `base` is ignored).
 *       Parameter `base` always configures the numeric base for bit-vector
 *       values, and for floating-point values in case of the tuple of strings
 *       instantiation. It is always ignored for Boolean and RoundingMode
 *       values.
 *
 * @note Return value is valid until next `bitwuzla_term_value_get_str_fmt`
 *       call.
 */
const char *bitwuzla_term_value_get_str_fmt(BitwuzlaTerm term, uint8_t base);

/**
 * Get (the raw) string representation of a given floating-point value
 * term in IEEE 754 standard representation.
 *
 * @param term        The floating-point value term.
 * @param sign        Output parameter. String representation of the
 *                    sign bit.
 * @param exponent    Output parameter. String representation of the exponent
 *                    bit-vector value.
 * @param significand Output parameter. String representation of the
 *                    significand bit-vector value.
 * @param base        The base in which the component bit-vector strings are
 *                    given; `2` for binary, `10` for decimal, and `16` for
 *                    hexadecimal.
 *
 * @note Return values sign, exponent and significand are valid until next
 *       `bitwuzla_term_value_get_fp_ieee` call.
 */
void bitwuzla_term_value_get_fp_ieee(BitwuzlaTerm term,
                                     const char **sign,
                                     const char **exponent,
                                     const char **significand,
                                     uint8_t base);

/**
 * Get representation of given rounding mode value term.
 * @param term The rounding mode value term.
 * @return The BitwuzlaRoundingMode representation of the given rounding mode
 *         value.
 */
BitwuzlaRoundingMode bitwuzla_term_value_get_rm(BitwuzlaTerm term);

/**
 * Get the SMT-LIB v2 string representation of a term.
 * @note This uses default binary format for bit-vector value strings.
 * @return A string representation of the given term.
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_term_to_string` call.
 */
const char *bitwuzla_term_to_string(BitwuzlaTerm term);

/**
 * Get the SMT-LIB v2 string representation of a term. String representations
 * of bit-vector values are printed in the given base.
 * @param base The base of the string representation of bit-vector values; `2`
 *             for binary, `10` for decimal, and `16` for hexadecimal. Always
 *             ignored for Boolean and RoundingMode values.
 * @return     A string representation of the given term.
 *
 * @note The returned char* pointer is only valid until the next
 *       `bitwuzla_term_to_string` call.
 */
const char *bitwuzla_term_to_string_fmt(BitwuzlaTerm term, uint8_t base);

/**
 * Print term in SMT-LIB v2 format.
 * @note This uses default binary format for bit-vector value strings.
 * @param term  The term.
 * @param file  The file to print the term to.
 */
void bitwuzla_term_print(BitwuzlaTerm term, FILE *file);

/**
 * Print term in SMT-LIB v2 format.
 * @param term  The term.
 * @param file  The file to print the term to.
 * @param base The base of the string representation of bit-vector values; `2`
 *             for binary, `10` for decimal, and `16` for hexadecimal.
 *
 * @note Floating-point values are printed in terms of operator `fp`. Their
 *       component bit-vector values can only be printed in binary or decimal
 *       format. If base `16` is configured, the format for floating-point
 *       component bit-vector values defaults to binary format.
 */
void bitwuzla_term_print_fmt(BitwuzlaTerm term, FILE *file, uint8_t base);

/** @} */

/* -------------------------------------------------------------------------- */
/* Bitwuzla                                                                   */
/* -------------------------------------------------------------------------- */

/** The Bitwuzla solver. */
typedef struct Bitwuzla Bitwuzla;

/** \addtogroup c_bitwuzla
 *  @{
 */

/**
 * Create a new Bitwuzla instance.
 *
 * The returned instance must be deleted via `bitwuzla_delete()`.
 *
 * @param options The associated options (optional).
 * @return A pointer to the created Bitwuzla instance.
 *
 * @see
 *   * `bitwuzla_delete`
 */
Bitwuzla *bitwuzla_new(const BitwuzlaOptions *options);

/**
 * Delete a Bitwuzla instance.
 *
 * The given instance must have been created via `bitwuzla_new()`.
 *
 * @param bitwuzla The Bitwuzla instance to delete.
 *
 * @see
 *   * `bitwuzla_new`
 */
void bitwuzla_delete(Bitwuzla *bitwuzla);

/**
 * Configure a termination callback function.
 *
 * The `state` of the callback can be retrieved via
 * `bitwuzla_get_termination_callback_state()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param fun The callback function, returns a value != 0 if `bitwuzla` should
 *            be terminated.
 * @param state The argument to the callback function.
 *
 * @see
 *   * `bitwuzla_terminate`
 *   * `bitwuzla_get_termination_callback_state`
 */
void bitwuzla_set_termination_callback(Bitwuzla *bitwuzla,
                                       int32_t (*fun)(void *),
                                       void *state);

/**
 * Get the state of the termination callback function.
 *
 * The returned object representing the state of the callback corresponds to
 * the `state` configured as argument to the callback function via
 * `bitwuzla_set_termination_callback()`.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return The object passed as argument `state` to the callback function.
 *
 * @see
 *   * `bitwuzla_terminate`
 *   * `bitwuzla_set_termination_callback`
 */
void *bitwuzla_get_termination_callback_state(Bitwuzla *bitwuzla);

/**
 * Configure an abort callback function, which is called instead of exit
 * on abort conditions.
 *
 * @note If the abort callback function throws a C++ exception, this must be
 *       thrown via std::rethrow_if_nested.
 *
 * @param fun The callback function. Argument `msg` explains the reason for the
 *            abort.
 */
void bitwuzla_set_abort_callback(void (*fun)(const char *msg));

/**
 * Push context levels.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to push.
 *
 * @see
 *   * `bitwuzla_set_option`
 */
void bitwuzla_push(Bitwuzla *bitwuzla, uint64_t nlevels);

/**
 * Pop context levels.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param nlevels The number of context levels to pop.
 *
 * @see
 *   * `bitwuzla_set_option`
 */
void bitwuzla_pop(Bitwuzla *bitwuzla, uint64_t nlevels);

/**
 * Assert formula.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The formula to assert.
 */
void bitwuzla_assert(Bitwuzla *bitwuzla, BitwuzlaTerm term);

/**
 * Get the set of currently asserted formulas.
 * @return The asserted formulas.
 * @return An array with the set of asserted formulas of size `size`. Only
 *         valid until the next `bitwuzla_get_assertions` call.
 */
BitwuzlaTerm *bitwuzla_get_assertions(Bitwuzla *bitwuzla, size_t *size);

/**
 * Determine if an assumption is an unsat assumption.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The assumption to check for.
 *
 * @return True if given assumption is an unsat assumption.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `bitwuzla_check_sat`
 */
bool bitwuzla_is_unsat_assumption(Bitwuzla *bitwuzla, BitwuzlaTerm term);

/**
 * Get the set of unsat assumptions.
 *
 * Unsat assumptions are assumptions that force an input formula to become
 * unsatisfiable. Unsat assumptions handling in Bitwuzla is analogous to
 * failed assumptions in MiniSAT.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assumptions of size `size`. Only valid until
 *         the next `bitwuzla_get_unsat_assumptions` call.
 *
 * @see
 *   * `bitwuzla_set_option`
 *   * `bitwuzla_check_sat`
 */
BitwuzlaTerm *bitwuzla_get_unsat_assumptions(Bitwuzla *bitwuzla, size_t *size);

/**
 * Get the unsat core (unsat assertions).
 *
 * The unsat core consists of the set of assertions that force an input formula
 * to become unsatisfiable.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_UNSAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param size Output parameter, stores the size of the returned array.
 *
 * @return An array with unsat assertions of size `size`. Only valid until
 *         the next `bitwuzla_get_unsat_core` call.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `bitwuzla_check_sat`
 */
BitwuzlaTerm *bitwuzla_get_unsat_core(Bitwuzla *bitwuzla, size_t *size);

/**
 * Simplify the current input formula.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @note Each call to `bitwuzla_check_sat()` and `bitwuzla_check_sat_assuming()`
 *       simplifies the input formula as a preprocessing step. It is not
 *       necessary to call this function explicitly in the general case.
 *
 * @see
 *   * `bitwuzla_assert`
 */
void bitwuzla_simplify(Bitwuzla *bitwuzla);

/**
 * Check satisfiability of current input formula.
 *
 * An input formula consists of assertions added via `bitwuzla_assert()`.
 * The search for a solution can by guided by additionally making assumptions
 * (see `bitwuzla_check_sat_assuming`).
 *
 * @note Assertions and assumptions are combined via Boolean and.
 *
 * @param bitwuzla The Bitwuzla instance.
 *
 * @return `::BITWUZLA_SAT` if the input formula is satisfiable and
 *         `::BITWUZLA_UNSAT` if it is unsatisfiable, and `::BITWUZLA_UNKNOWN`
 *         when neither satisfiability nor unsatisfiability was determined.
 *         This can happen when `bitwuzla` was terminated via a termination
 *         callback.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `bitwuzla_set_option`
 *   * `BitwuzlaResult`
 */
BitwuzlaResult bitwuzla_check_sat(Bitwuzla *bitwuzla);

/**
 * Check satisfiability of current input formula wrt to the given set of
 * assumptions.
 *
 * An input formula consists of assertions added via `bitwuzla_assert()`.
 * The search for a solution can by guided by additionally making assumptions
 * (the given set of assumptions `args`).
 *
 * @note Assertions and assumptions are combined via Boolean and.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param argc     The number of assumptions in `args`.
 * @param args     The assumptions.
 *
 * @return `::BITWUZLA_SAT` if the input formula is satisfiable and
 *         `::BITWUZLA_UNSAT` if it is unsatisfiable, and `::BITWUZLA_UNKNOWN`
 *         when neither satisfiability nor unsatisfiability was determined.
 *         This can happen when `bitwuzla` was terminated via a termination
 *         callback.
 *
 * @see
 *   * `bitwuzla_assert`
 *   * `bitwuzla_set_option`
 *   * `BitwuzlaResult`
 */
BitwuzlaResult bitwuzla_check_sat_assuming(Bitwuzla *bitwuzla,
                                           uint32_t argc,
                                           BitwuzlaTerm args[]);

/**
 * Get a term representing the model value of a given term.
 *
 * Requires that the last `bitwuzla_check_sat()` query returned
 * `::BITWUZLA_SAT`.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param term The term to query a model value for.
 *
 * @return A term representing the model value of term `term`.
 *
 * @see `bitwuzla_check_sat`
 */
BitwuzlaTerm bitwuzla_get_value(Bitwuzla *bitwuzla, BitwuzlaTerm term);

/**
 * Print the current input formula.
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param format The output format for printing the formula. Currently, only
 *               `"smt2"` for the SMT-LIB v2 format is supported.
 * @param file   The file to print the formula to.
 * @param base   The base of the string representation of bit-vector values;
 *               `2` for binary, `10` for decimal, and `16` for hexadecimal.
 *
 * @note Floating-point values are printed in terms of operator `fp`. Their
 *       component bit-vector values can only be printed in binary or decimal
 *       format. If base `16` is configured, the format for floating-point
 *       component bit-vector values defaults to binary format.
 */
void bitwuzla_print_formula(Bitwuzla *bitwuzla,
                            const char *format,
                            FILE *file,
                            uint8_t base);

/**
 * Get current statistics.
 *
 * The statistics are retrieved as a mapping from statistic name (`keys`)
 * to statistic value (`values`).
 *
 * @param bitwuzla The Bitwuzla instance.
 * @param keys     The resulting set of statistic names.
 * @param values   The resulting set of statistic values.
 * @param size     The resulting size of `keys` and `values`.
 *
 * @note Output parameters `keys` and `values` are only valid until the
 *       next call to `bitwuzla_get_statistics()`.
 */
void bitwuzla_get_statistics(Bitwuzla *bitwuzla,
                             const char ***keys,
                             const char ***values,
                             size_t *size);

/** @} */

/* -------------------------------------------------------------------------- */
/* Sort creation                                                              */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_sort_creation
 *  @{
 */

/**
 * Create an array sort.
 *
 * @param index The index sort of the array sort.
 * @param element The element sort of the array sort.
 * @return An array sort which maps sort `index` to sort `element`.
 *
 * @see
 *   * `bitwuzla_sort_is_array`
 *   * `bitwuzla_sort_array_get_index`
 *   * `bitwuzla_sort_array_get_element`
 *   * `bitwuzla_term_is_array`
 *   * `bitwuzla_term_array_get_index_sort`
 *   * `bitwuzla_term_array_get_element_sort`
 */
BitwuzlaSort bitwuzla_mk_array_sort(BitwuzlaSort index, BitwuzlaSort element);

/**
 * Create a Boolean sort.
 * @return A Boolean sort.
 */
BitwuzlaSort bitwuzla_mk_bool_sort();

/**
 * Create a bit-vector sort of given size.
 *
 * @param size The size of the bit-vector sort.
 * @return A bit-vector sort of given size.
 *
 * @see
 *   * `bitwuzla_sort_is_bv`
 *   * `bitwuzla_sort_bv_get_size`
 *   * `bitwuzla_term_is_bv`
 *   * `bitwuzla_term_bv_get_size`
 */
BitwuzlaSort bitwuzla_mk_bv_sort(uint64_t size);

/**
 * Create a floating-point sort of given exponent and significand size.
 *
 * @param exp_size The size of the exponent.
 * @param sig_size The size of the significand (including sign bit).
 * @return A floating-point sort of given format.
 *
 * @see
 *   * `bitwuzla_sort_is_fp`
 *   * `bitwuzla_sort_fp_get_exp_size`
 *   * `bitwuzla_sort_fp_get_sig_size`
 *   * `bitwuzla_term_is_fp`
 *   * `bitwuzla_term_fp_get_exp_size`
 *   * `bitwuzla_term_fp_get_sig_size`
 */
BitwuzlaSort bitwuzla_mk_fp_sort(uint64_t exp_size, uint64_t sig_size);

/**
 * Create a function sort.
 *
 * @param arity The number of arguments to the function.
 * @param domain The domain sorts (the sorts of the arguments). The number of
 *               sorts in this vector must match `arity`.
 * @param codomain The codomain sort (the sort of the return value).
 * @return A function sort of given domain and codomain sorts.
 *
 * @see
 *   * `bitwuzla_sort_is_fun`
 *   * `bitwuzla_sort_fun_get_arity`
 *   * `bitwuzla_sort_fun_get_domain_sorts`
 *   * `bitwuzla_sort_fun_get_codomain`
 *   * `bitwuzla_term_is_fun`
 *   * `bitwuzla_term_fun_get_arity`
 *   * `bitwuzla_term_fun_get_domain_sorts`
 *   * `bitwuzla_term_fun_get_codomain_sort`
 */
BitwuzlaSort bitwuzla_mk_fun_sort(uint64_t arity,
                                  BitwuzlaSort domain[],
                                  BitwuzlaSort codomain);

/**
 * Create a Roundingmode sort.
 * @return A Roundingmode sort.
 * @see
 *   * `bitwuzla_sort_is_rm`
 *   * `bitwuzla_term_is_rm`
 */
BitwuzlaSort bitwuzla_mk_rm_sort();

/**
 * Create an uninterpreted sort.
 * @param symbol The symbol of the sort. May be NULL.
 * @return A uninterpreted sort.
 * @see
 *   * `bitwuzla_sort_is_uninterpreted`
 *   * `bitwuzla_term_is_uninterpreted`
 */
BitwuzlaSort bitwuzla_mk_uninterpreted_sort(const char *symbol);

/** @} */

/* -------------------------------------------------------------------------- */
/* Term creation                                                              */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_term_creation
 *  @{
 */

/**
 * Create a true value.
 * @return A term representing true.
 */
BitwuzlaTerm bitwuzla_mk_true();

/**
 * Create a false value.
 * @return A term representing false.
 */
BitwuzlaTerm bitwuzla_mk_false();

/**
 * Create a bit-vector value zero.
 *
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value 0 of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_zero(BitwuzlaSort sort);

/**
 * Create a bit-vector value one.
 *
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value 1 of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_one(BitwuzlaSort sort);

/**
 * Create a bit-vector value where all bits are set to 1.
 *
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort
 *         where all bits are set to 1.
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_ones(BitwuzlaSort sort);

/**
 * Create a bit-vector minimum signed value.
 *
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 1 and all remaining bits are set to 0.
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_min_signed(BitwuzlaSort sort);
/**
 * Create a bit-vector maximum signed value.
 *
 * @param sort The sort of the value.
 * @return A term representing the bit-vector value of given sort where the MSB
 *         is set to 0 and all remaining bits are set to 1.
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_max_signed(BitwuzlaSort sort);

/**
 * Create a floating-point positive zero value (SMT-LIB: `+zero`).
 *
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive zero value of given
 *         floating-point sort.
 * @see
 *  * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_pos_zero(BitwuzlaSort sort);

/**
 * Create a floating-point negative zero value (SMT-LIB: `-zero`).
 *
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative zero value of given
 *         floating-point sort.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_neg_zero(BitwuzlaSort sort);

/**
 * Create a floating-point positive infinity value (SMT-LIB: `+oo`).
 *
 * @param sort The sort of the value.
 * @return A term representing the floating-point positive infinity value of
 *         given floating-point sort.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_pos_inf(BitwuzlaSort sort);

/**
 * Create a floating-point negative infinity value (SMT-LIB: `-oo`).
 *
 * @param sort The sort of the value.
 * @return A term representing the floating-point negative infinity value of
 *         given floating-point sort.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_neg_inf(BitwuzlaSort sort);

/**
 * Create a floating-point NaN value.
 *
 * @param sort The sort of the value.
 * @return A term representing the floating-point NaN value of given
 *         floating-point sort.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_nan(BitwuzlaSort sort);

/**
 * Create a bit-vector value from its string representation.
 *
 * Parameter `base` determines the base of the string representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value A string representing the value.
 * @param base The base in which the string is given; `2` for binary, `10` for
 *             decimal, and `16` for hexadecimal.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_value(BitwuzlaSort sort,
                                  const char *value,
                                  uint8_t base);

/**
 * Create a bit-vector value from its unsigned integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_value_uint64(BitwuzlaSort sort, uint64_t value);

/**
 * Create a bit-vector value from its signed integer representation.
 *
 * @note Given value must fit into a bit-vector of given size (sort).
 *
 * @param sort The sort of the value.
 * @param value The unsigned integer representation of the bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the bit-vector value
 *         of given sort.
 *
 * @see
 *   * `bitwuzla_mk_bv_sort`
 */
BitwuzlaTerm bitwuzla_mk_bv_value_int64(BitwuzlaSort sort, int64_t value);

/**
 * Create a floating-point value from its IEEE 754 standard representation
 * given as three bit-vector values representing the sign bit, the exponent and
 * the significand.
 *
 * @param bv_sign The sign bit.
 * @param bv_exponent The exponent bit-vector value.
 * @param bv_significand The significand bit-vector value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the floating-point
 *         value.
 */
BitwuzlaTerm bitwuzla_mk_fp_value(BitwuzlaTerm bv_sign,
                                  BitwuzlaTerm bv_exponent,
                                  BitwuzlaTerm bv_significand);

/**
 * Create a floating-point value from its real representation, given as a
 * decimal string, with respect to given rounding mode.
 *
 * @note Given rounding mode may be an arbitrary, non-value rounding mode term.
 *       If it is a value, the returned term will be a floating-point value,
 *       else a non-value floating-point term.
 *
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param real The decimal string representing a real value.
 *
 * @return A floating-point representation of the given real string. If `rm`
 *         is of kind BITWUZLA_KIND_VALUE the floating-point will be of kind
 *         BITWUZLA_KIND_VALUE, else it will be a non-value term.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_from_real(BitwuzlaSort sort,
                                      BitwuzlaTerm rm,
                                      const char *real);

/**
 * Create a floating-point value from its rational representation, given as a
 * two decimal strings representing the numerator and denominator, with respect
 * to given rounding mode.
 *
 * @note Given rounding mode may be an arbitrary, non-value rounding mode term.
 *       If it is a value, the returned term will be a floating-point value,
 *       else a non-value floating-point term.
 *
 * @param sort The sort of the value.
 * @param rm The rounding mode.
 * @param num The decimal string representing the numerator.
 * @param den The decimal string representing the denominator.
 *
 * @return A floating-point representation of the given rational string. If
 *         `rm` is of kind BITWUZLA_KIND_VALUE the floating-point will be of
 *         kind BITWUZLA_KIND_VALUE, else it will be a non-value term.
 * @see
 *   * `bitwuzla_mk_fp_sort`
 */
BitwuzlaTerm bitwuzla_mk_fp_from_rational(BitwuzlaSort sort,
                                          BitwuzlaTerm rm,
                                          const char *num,
                                          const char *den);

/**
 * Create a rounding mode value.
 *
 * @param rm The rounding mode value.
 *
 * @return A term of kind BITWUZLA_KIND_VAL, representing the rounding mode
 *         value.
 *
 * @see
 *   * `BitwuzlaRoundingMode`
 */
BitwuzlaTerm bitwuzla_mk_rm_value(BitwuzlaRoundingMode rm);

/**
 * Create a term of given kind with one argument term.
 *
 * @param kind The operator kind.
 * @param arg The argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term1(BitwuzlaKind kind, BitwuzlaTerm arg);

/**
 * Create a term of given kind with two argument terms.
 *
 * @param kind The operator kind.
 * @param arg0 The first argument to the operator.
 * @param arg1 The second argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term2(BitwuzlaKind kind,
                               BitwuzlaTerm arg0,
                               BitwuzlaTerm arg1);

/**
 * Create a term of given kind with three argument terms.
 *
 * @param kind The operator kind.
 * @param arg0 The first argument to the operator.
 * @param arg1 The second argument to the operator.
 * @param arg2 The third argument to the operator.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term3(BitwuzlaKind kind,
                               BitwuzlaTerm arg0,
                               BitwuzlaTerm arg1,
                               BitwuzlaTerm arg2);

/**
 * Create a term of given kind with the given argument terms.
 *
 * @param kind The operator kind.
 * @param argc The number of argument terms.
 * @param args The argument terms.
 *
 * @return A term representing an operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term(BitwuzlaKind kind,
                              uint32_t argc,
                              BitwuzlaTerm args[]);

/**
 * Create an indexed term of given kind with one argument term and one index.
 *
 * @param kind The operator kind.
 * @param arg The argument term.
 * @param idx The index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term1_indexed1(BitwuzlaKind kind,
                                        BitwuzlaTerm arg,
                                        uint64_t idx);

/**
 * Create an indexed term of given kind with one argument term and two indices.
 *
 * @param kind The operator kind.
 * @param arg The argument term.
 * @param idx0 The first index.
 * @param idx1 The second index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term1_indexed2(BitwuzlaKind kind,
                                        BitwuzlaTerm arg,
                                        uint64_t idx0,
                                        uint64_t idx1);

/**
 * Create an indexed term of given kind with two argument terms and one index.
 *
 * @param kind The operator kind.
 * @param arg0 The first argument term.
 * @param arg1 The second argument term.
 * @param idx The index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term2_indexed1(BitwuzlaKind kind,
                                        BitwuzlaTerm arg0,
                                        BitwuzlaTerm arg1,
                                        uint64_t idx);

/**
 * Create an indexed term of given kind with two argument terms and two indices.
 *
 * @param kind The operator kind.
 * @param arg0 The first argument term.
 * @param arg1 The second argument term.
 * @param idx0 The first index.
 * @param idx1 The second index.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term2_indexed2(BitwuzlaKind kind,
                                        BitwuzlaTerm arg0,
                                        BitwuzlaTerm arg1,
                                        uint64_t idx0,
                                        uint64_t idx1);

/**
 * Create an indexed term of given kind with the given argument terms and
 * indices.
 *
 * @param kind The operator kind.
 * @param argc The number of argument terms.
 * @param args The argument terms.
 * @param idxc The number of indices.
 * @param idxs The indices.
 *
 * @return A term representing an indexed operation of given kind.
 *
 * @see
 *   * `BitwuzlaKind`
 */
BitwuzlaTerm bitwuzla_mk_term_indexed(BitwuzlaKind kind,
                                      uint32_t argc,
                                      BitwuzlaTerm args[],
                                      uint32_t idxc,
                                      const uint64_t idxs[]);

/**
 * Create a (first-order) constant of given sort with given symbol.
 *
 * @param sort The sort of the constant.
 * @param symbol The symbol of the constant.
 *
 * @return A term of kind BITWUZLA_KIND_CONST, representing the constant.
 *
 * @see
 *   * `bitwuzla_mk_array_sort`
 *   * `bitwuzla_mk_bool_sort`
 *   * `bitwuzla_mk_bv_sort`
 *   * `bitwuzla_mk_fp_sort`
 *   * `bitwuzla_mk_fun_sort`
 *   * `bitwuzla_mk_rm_sort`
 */
BitwuzlaTerm bitwuzla_mk_const(BitwuzlaSort sort, const char *symbol);

/**
 * Create a one-dimensional constant array of given sort, initialized with
 * given value.
 *
 * @param sort The sort of the array.
 * @param value The term to initialize the elements of the array with.
 *
 * @return A term of kind BITWUZLA_KIND_CONST_ARRAY, representing a constant
 *         array of given sort.
 *
 * @see
 *   * `bitwuzla_mk_array_sort`
 */
BitwuzlaTerm bitwuzla_mk_const_array(BitwuzlaSort sort, BitwuzlaTerm value);

/**
 * Create a variable of given sort with given symbol.
 *
 * @note This creates a variable to be bound by quantifiers or lambdas.
 *
 * @param sort The sort of the variable.
 * @param symbol The symbol of the variable.
 *
 * @return A term of kind BITWUZLA_KIND_VAR, representing the variable.
 *
 * @see
 *   * `bitwuzla_mk_bool_sort`
 *   * `bitwuzla_mk_bv_sort`
 *   * `bitwuzla_mk_fp_sort`
 *   * `bitwuzla_mk_fun_sort`
 *   * `bitwuzla_mk_rm_sort`
 */
BitwuzlaTerm bitwuzla_mk_var(BitwuzlaSort sort, const char *symbol);

/** @} */

/* -------------------------------------------------------------------------- */
/* Term substitution                                                          */
/* -------------------------------------------------------------------------- */

/** \addtogroup c_term_substitution
 *  @{
 */

/**
 * Substitute a set of keys with their corresponding values in the given term.
 *
 * @param term The term in which the keys are to be substituted.
 * @param map_size The size of the substitution map.
 * @param map_keys The keys.
 * @param map_values The mapped values.
 *
 * @return The resulting term from this substitution.
 */
BitwuzlaTerm bitwuzla_substitute_term(BitwuzlaTerm term,
                                      size_t map_size,
                                      BitwuzlaTerm map_keys[],
                                      BitwuzlaTerm map_values[]);

/**
 * Substitute a set of keys with their corresponding values in the set of given
 * terms.
 *
 * The terms in `terms` are replaced with the terms resulting from these
 * substitutions.
 *
 * @param terms_size The size of the set of terms.
 * @param terms The terms in which the keys are to be substituted.
 * @param map_size The size of the substitution map.
 * @param map_keys The keys.
 * @param map_values The mapped values.
 */
void bitwuzla_substitute_terms(size_t terms_size,
                               BitwuzlaTerm terms[],
                               size_t map_size,
                               BitwuzlaTerm map_keys[],
                               BitwuzlaTerm map_values[]);

/** @} */

#if __cplusplus
}
#endif

/* -------------------------------------------------------------------------- */
#endif
