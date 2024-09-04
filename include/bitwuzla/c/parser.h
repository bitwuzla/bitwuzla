/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_C_PARSER_H_INCLUDED
#define BITWUZLA_API_C_PARSER_H_INCLUDED

#include <bitwuzla/c/bitwuzla.h>

/** A Bitwuzla parser. */
typedef struct BitwuzlaParser BitwuzlaParser;

/** \addtogroup c_bitwuzlaparser
 *  @{
 */

/**
 * Create a new Bitwuzla parser instance.
 *
 * The returned instance must be deleted via `bitwuzla_parser_delete()`.
 *
 * @note The parser creates and owns the associated Bitwuzla instance.
 * @param tm The associated term manager instance.
 * @param options The associated options.
 * @param language     The format of the input.
 * @param base         The base of the string representation of bit-vector
 *                     values; `2` for binary, `10` for decimal, and `16` for
 *                     hexadecimal. Always ignored for Boolean and RoundingMode
 *                     values.
 * @param outfile_name The output file name. If name is '\<stdout\>', the parser
 *                     writes to stdout.
 * @return A pointer to the created Bitwuzla parser instance.
 *
 * @see
 *   * `bitwuzla_parser_delete`
 */
BitwuzlaParser* bitwuzla_parser_new(BitwuzlaTermManager* tm,
                                    BitwuzlaOptions* options,
                                    const char* language,
                                    uint8_t base,
                                    const char* outfile_name);

/**
 * Delete a Bitwuzla parser instance.
 *
 * The given instance must have been created via `bitwuzla_parser_new()`.
 *
 * @param parser The Bitwuzla parser instance to delete.
 *
 * @see
 *   * `bitwuzla_parser_new`
 */
void bitwuzla_parser_delete(BitwuzlaParser* parser);

/**
 * Enable or disable the automatic printing of the model after each
 * satisfiable query.
 *
 * Enable to automatically print the model after every sat query. Must be
 * enabled to automatically print models for BTOR2 input (does not provide a
 * command to print the model like `(get-model)` in SMT-LIB2). False (default)
 * configures the standard behavior for SMT-LIB2 input (print model only after
 * a `(get-model)` command).
 *
 * @note By default, auto printing of the model is disabled.
 *
 * @param parser     The Bitwuzla parser instance.
 * @param value True to enable auto printing of the model.
 */
void bitwuzla_parser_configure_auto_print_model(BitwuzlaParser* parser,
                                                bool value);

/**
 * Parse input, either from a file or from a string.
 *
 * @param parser     The Bitwuzla parser instance.
 * @param input      The name of the input file if `parse_file` is true,
 *                   else a string with the input.
 * @param parse_only True to only parse without executing check-sat calls.
 * @param parse_file True to parse an input file with the given name `input`,
 *                   false to parse from `input` as a string input.
 * @param error_msg  Output parameter for the error message in case of a
 *                   parse error, NULL if no error occurred.
 * @note Parameter `parse_only` is redundant for BTOR2 input, its the only
 *       available mode for BTOR2 (due to the language not supporting
 *       "commands" as in SMT2).
 */
void bitwuzla_parser_parse(BitwuzlaParser* parser,
                           const char* input,
                           bool parse_only,
                           bool parse_file,
                           const char** error_msg);

/**
 * Parse term from string.
 * @param parser     The Bitwuzla parser instance.
 * @param input      The input string.
 * @param error_msg  Output parameter for the error message in case of a
 *                   parse error, NULL if no error occurred.
 * @return The resulting term.
 */
BitwuzlaTerm bitwuzla_parser_parse_term(BitwuzlaParser* parser,
                                        const char* input,
                                        const char** error_msg);
/**
 * Parse sort from string.
 * @param parser     The Bitwuzla parser instance.
 * @param input The input string.
 * @return The resulting sort.
 * @param error_msg  Output parameter for the error message in case of a
 *                   parse error, NULL if no error occurred.
 */
BitwuzlaSort bitwuzla_parser_parse_sort(BitwuzlaParser* parser,
                                        const char* input,
                                        const char** error_msg);

/**
 * Get the current set of (user-)declared sort symbols.
 * @note Corresponds to the sorts declared via SMT-LIB command `declare-sort`.
 *       Will always return an empty set for BTOR2 input.
 * @param size The size of the returned sort array.
 * @return The declared sorts, NULL if empty.
 */
BitwuzlaSort* bitwuzla_parser_get_declared_sorts(BitwuzlaParser* parser,
                                                 size_t* size);
/**
 * Get the current set of (user-)declared function symbols.
 * @note Corresponds to the function symbols declared via SMT-LIB commands
 *       `declare-const` and `declare-fun`.
 * @param size The size of the returned sort array.
 * @return The declared function symbols, NULL if empty.
 */
BitwuzlaTerm* bitwuzla_parser_get_declared_funs(BitwuzlaParser* parser,
                                                size_t* size);

/**
 * Get the current error message.
 * @param parser The Bitwuzla parser instance.
 * @return The error message.
 */
const char* bitwuzla_parser_get_error_msg(BitwuzlaParser* parser);

/**
 * Get the associated Bitwuzla instance.
 * @return The Bitwuzla instance.
 */
Bitwuzla* bitwuzla_parser_get_bitwuzla(BitwuzlaParser* parser);

/** @} */

#endif
