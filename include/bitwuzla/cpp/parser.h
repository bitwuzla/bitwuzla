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
   * @param infile_name The name of the input file.
   * @param language    The format of the input file.
   */
  Parser(Options &options,
         const std::string &infile_name,
         const std::string &language = "smt2");
  /**
   * Constructor.
   * @note The parser creates and owns the associated Bitwuzla instance.
   * @param options     The configuration options for the Bitwuzla instance
   *                    (created by the parser).
   * @param infile_name The name of the input file.
   * @param infile      The input file.
   * @param language    The format of the input file.
   */
  Parser(Options &options,
         const std::string &infile_name,
         FILE *infile,
         const std::string &language = "smt2");
  /** Destructor. */
  ~Parser();
  /**
   * Parse input file.
   * @param parse_only  True to only parse without issuing calls to check_sat.
   * @return The error message in case of an error, empty if no error.
   */
  std::string parse(bool parse_only = false);

  /**
   * Get the associated Bitwuzla instance.
   * @return The Bitwuzla instance.
   */
  bitwuzla::Bitwuzla *bitwuzla();

 private:
  std::unique_ptr<bzla::parser::Parser> d_parser;
};

/* -------------------------------------------------------------------------- */

}  // namespace bitwuzla::parser

#endif
