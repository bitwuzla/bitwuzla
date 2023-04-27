#ifndef BITWUZLA_API_C_PARSER_H_INCLUDED
#define BITWUZLA_API_C_PARSER_H_INCLUDED

#include <bitwuzla/c/bitwuzla.h>

/** A Bitwuzla parser. */
typedef struct BitwuzlaParser BitwuzlaParser;

/**
 * Create a new Bitwuzla parser instance.
 *
 * The returned instance must be deleted via `bitwuzla_parser_delete()`.
 *
 * @note The parser creates and owns the associated Bitwuzla instance.
 * @param options The associated options.
 * @param infile_name The name of the input file.
 * @param infile      The input file.
 * @param format      The format of the input file.
 * @return A pointer to the created Bitwuzla parser instance.
 *
 * @see
 *   * `bitwuzla_parser_delete`
 */
BitwuzlaParser* bitwuzla_parser_new(BitwuzlaOptions* options,
                                    const char* infile_name,
                                    FILE* infile,
                                    const char* language);

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

#endif
