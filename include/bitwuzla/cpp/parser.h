/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BITWUZLA_API_CPP_PARSER_H_INCLUDED
#define BITWUZLA_API_CPP_PARSER_H_INCLUDED

#include <bitwuzla/cpp/bitwuzla.h>

#include <memory>

namespace bzla::parser {
class Parser;
}

namespace bitwuzla::parser {

/* -------------------------------------------------------------------------- */

/** The Bitwuzla parser. */
class Parser
{
 public:
  /**
   * Constructor.
   * @note The parser creates and owns the associated Bitwuzla instance.
   * @param options     The configuration options for the Bitwuzla instance
   *                    (created by the parser).
   * @param language    The format of the input file.
   * @param out         The output stream.
   */
  Parser(Options &options,
         const std::string &language = "smt2",
         std::ostream *out           = &std::cout);
  /** Destructor. */
  ~Parser();
  /**
   * Parse input, either from a file or from a string.
   * @param input      The name of the input file if `parse_file` is true,
   *                   else a string with the input.
   * @param parse_only True to only parse without issuing calls to check_sat.
   * @param parse_file True to parse an input file with the given name `input`,
   *                   false to parse from `input` as a string input.
   * @return The error message in case of an error, empty if no error.
   * @note Parameter `parse_only` is redundant for BTOR2 input, its the only
   *       available mode for BTOR2 (due to the language not supporting
   *       "commands" as in SMT2).
   */
  std::string parse(const std::string &input,
                    bool parse_only = false,
                    bool parse_file = true);
  /**
   * Parse input from an input stream.
   * @param infile_name The name of the input file. This is required for error
   *                    message printing only. Use '<stdin>' if the input
   *                    stream is std::cin, and '<string>' if the input stream
   *                    was created from a string.
   * @param input       The input stream.
   * @param parse_only  True to only parse without issuing calls to check_sat.
   * @return The error message in case of an error, empty if no error.
   * @note Parameter `parse_only` is redundant for BTOR2 input, its the only
   *       available mode for BTOR2 (due to the language not supporting
   *       "commands" as in SMT2).
   */
  std::string parse(const std::string &infile_name,
                    std::istream &input,
                    bool parse_only = false);

  /**
   * Get the associated Bitwuzla instance.
   * @return The Bitwuzla instance.
   */
  std::shared_ptr<bitwuzla::Bitwuzla> bitwuzla();

 private:
  std::unique_ptr<bzla::parser::Parser> d_parser;
};

/* -------------------------------------------------------------------------- */

}  // namespace bitwuzla::parser

#endif
