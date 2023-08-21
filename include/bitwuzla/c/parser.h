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
 * @param options The associated options.
 * @param infile_name  The name of the input file.
 * @param infile       The input file.
 * @param language     The format of the input file.
 * @param base         The base of the string representation of bit-vector
 *                     values; `2` for binary, `10` for decimal, and `16` for
 *                     hexadecimal. Always ignored for Boolean and RoundingMode
 *                     values.
 * @param outfile_name The output file name. If name is '<stdout>', the parser
 *                     writes to stdout.
 * @return A pointer to the created Bitwuzla parser instance.
 *
 * @see
 *   * `bitwuzla_parser_delete`
 */
BitwuzlaParser* bitwuzla_parser_new(BitwuzlaOptions* options,
                                    const char* infile_name,
                                    FILE* infile,
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
 * Parser input file.
 *
 * @param parser The Bitwuzla parser instance to delete.
 * @param parse_only True to only parse without executing check-sat calls.
 * @return The error message in case of an error, else NULL.
 */
const char* bitwuzla_parser_parse(BitwuzlaParser* parser, bool parse_only);

/**
 * Get the associated Bitwuzla instance.
 * @return The Bitwuzla instance.
 */
Bitwuzla* bitwuzla_parser_get_bitwuzla(BitwuzlaParser* parser);

/** @} */

#endif
