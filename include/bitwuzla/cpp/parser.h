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
   * Parse input file.
   * @param infile_name The name of the input file.
   * @param parse_only  True to only parse without issuing calls to check_sat.
   * @return The error message in case of an error, empty if no error.
   */
  std::string parse(const std::string &infile_name, bool parse_only = false);
  /**
   * Parse input file.
   * @param infile_name The name of the input file.
   * @param input       The input stream.
   * @param parse_only  True to only parse without issuing calls to check_sat.
   * @return The error message in case of an error, empty if no error.
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
